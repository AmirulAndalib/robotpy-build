from keyword import iskeyword
import re
import sphinxify
import typing

from .config.autowrap_yml import (
    AutowrapConfigYaml,
    BufferData,
    BufferType,
    ClassData,
    EnumData,
    EnumValue,
    FunctionData,
    PropData,
    PropAccess,
    ReturnValuePolicy,
)
from .generator_data import GeneratorData, MissingReporter
from .mangle import trampoline_signature

from .j2_context import (
    BaseClassData,
    ClassContext,
    Documentation,
    EnumContext,
    EnumeratorContext,
    FunctionContext,
    HeaderContext,
    ParamContext,
    PropContext,
    ReturnParamContext,
    TemplateInstanceContext,
    TrampolineData,
)


# TODO: this isn't the best solution
def _gen_int_types():
    for i in ("int", "uint"):
        for j in ("", "_fast", "_least"):
            for k in ("8", "16", "32", "64"):
                yield f"{i}{j}{k}_t"
    yield "intmax_t"
    yield "uintmax_t"


_int32_types = frozenset(_gen_int_types())


_rvp_map = {
    ReturnValuePolicy.TAKE_OWNERSHIP: ", py::return_value_policy::take_ownership",
    ReturnValuePolicy.COPY: ", py::return_value_policy::copy",
    ReturnValuePolicy.MOVE: ", py::return_value_policy::move",
    ReturnValuePolicy.REFERENCE: ", py::return_value_policy::reference",
    ReturnValuePolicy.REFERENCE_INTERNAL: ", py::return_value_policy::reference_internal",
    ReturnValuePolicy.AUTOMATIC: "",
    ReturnValuePolicy.AUTOMATIC_REFERENCE: ", py::return_value_policy::automatic_reference",
}

# fmt: off
_operators = {
    # binary
    "-", "+", "*", "/", "%", "&", "^", "==", "!=", "|", ">", ">=", "<", "<=",
    # inplace
    "+=", "-=", "*=", "/=", "%=", "&=", "^=", "|=",
}
# fmt: on

_type_caster_seps = re.compile(r"[<>\(\)]")


class HookError(Exception):
    pass


def _using_signature(cls: ClassContext, fn: FunctionContext) -> str:
    return f"{cls.full_cpp_name_identifier}_{fn.cpp_type}"


class Hooks:
    """
    Header2Whatever hooks used for generating C++ wrappers
    """

    _qualname_bad = ":<>="
    _qualname_trans = str.maketrans(_qualname_bad, "_" * len(_qualname_bad))

    def __init__(
        self,
        data: AutowrapConfigYaml,
        casters: typing.Dict[str, typing.Dict[str, typing.Any]],
        report_only: bool,
    ):
        self.gendata = GeneratorData(data)
        self.rawdata = data
        self.casters = casters
        self.report_only = report_only

        self.types: typing.Set[str] = set()

        self.hctx = HeaderContext(
            extra_includes=data.extra_includes,
            extra_includes_first=data.extra_includes_first,
            inline_code=data.inline_code,
            trampoline_signature=trampoline_signature,
            using_signature=_using_signature,
        )

    def report_missing(self, name: str, reporter: MissingReporter):
        self.gendata.report_missing(name, reporter)

    def _add_type_caster(self, typename: str):
        # defer until the end since there's lots of duplication
        self.types.add(typename)

    def _get_module_var(self, v, data) -> str:
        if data.subpackage:
            var = f"pkg_{data.subpackage.replace('.', '_')}"
            self.hctx.subpackages[data.subpackage] = var
            return var

        return "m"

    def _get_type_caster_cfgs(self, typename: str):
        tmpl_idx = typename.find("<")
        if tmpl_idx == -1:
            typenames = [typename]
        else:
            typenames = [typename[:tmpl_idx]] + _type_caster_seps.split(
                typename[tmpl_idx:].replace(" ", "")
            )
        for typename in typenames:
            if typename:
                ccfg = self.casters.get(typename)
                if ccfg:
                    yield ccfg

    def _get_type_caster_includes(self):
        includes = set()
        for typename in self.types:
            for ccfg in self._get_type_caster_cfgs(typename):
                includes.add(ccfg["hdr"])
        return sorted(includes)

    def _make_py_name(self, name, data, strip_prefixes=None, is_operator=False):
        if data.rename:
            return data.rename

        if strip_prefixes is None:
            strip_prefixes = self.rawdata.strip_prefixes

        if strip_prefixes:
            for pfx in strip_prefixes:
                if name.startswith(pfx):
                    n = name[len(pfx) :]
                    if n.isidentifier():
                        name = n
                        break

        if iskeyword(name):
            return f"{name}_"
        if not name.isidentifier() and not is_operator:
            if not self.report_only:
                raise ValueError(f"name {name!r} is not a valid identifier")

        return name

    def _process_doc(
        self, thing, data, append_prefix="", param_remap: typing.Dict[str, str] = {}
    ) -> Documentation:
        doc = ""

        if data.doc is not None:
            doc = data.doc
        elif "doxygen" in thing:
            doc = thing["doxygen"]
            if param_remap:
                d = sphinxify.Doc.from_comment(doc)
                for param in d.params:
                    new_name = param_remap.get(param.name)
                    if new_name:
                        param.name = new_name
                doc = str(d)
            else:
                doc = sphinxify.process_raw(doc)

        if data.doc_append is not None:
            doc += f"\n{append_prefix}" + data.doc_append.replace(
                "\n", f"\n{append_prefix}"
            )

        return self._quote_doc(doc)

    def _quote_doc(self, doc: typing.Optional[str]) -> Documentation:
        doc_quoted: Documentation = None
        if doc:
            # TODO
            doc = doc.replace("\\", "\\\\").replace('"', '\\"')
            doc_quoted = doc.splitlines(keepends=True)
            doc_quoted = ['"%s"' % (dq.replace("\n", "\\n"),) for dq in doc_quoted]

        return doc_quoted

    def _resolve_default(self, fn, p, name, cpp_type) -> str:
        if isinstance(name, (int, float)):
            return str(name)
        if name in ("NULL", "nullptr"):
            return name

        if name and name[0] == "{" and name[-1] == "}":
            if p["array"]:
                return name
            return f"{cpp_type}{name}"

        # if there's a parent, look there
        parent = fn["parent"]
        if parent:
            for prop in parent["properties"]["public"]:
                if prop["name"] == name:
                    name = f"{parent['namespace']}::{parent['name']}::{name}"
        return name

    def _maybe_add_default_arg_cast(self, p, name, cpp_type):
        if not p.get("disable_type_caster_default_cast", False):
            found_typename = None
            for ccfg in self._get_type_caster_cfgs(cpp_type):
                if ccfg.get("darg"):
                    if found_typename and found_typename != ccfg["typename"]:
                        raise HookError(
                            f"multiple type casters found for {p['name']} ({cpp_type}), use disable_type_caster_default_cast"
                        )
                    found_typename = ccfg["typename"]
                    name = f"({found_typename}){name}"

        return name

    def _get_function_signature(self, fn):
        param_sig = ", ".join(
            p.get("enum", p["raw_type"]) + "&" * p["reference"] + "*" * p["pointer"]
            for p in fn["parameters"]
        )
        param_sig = param_sig.replace(" >", ">")
        if fn["const"]:
            if param_sig:
                param_sig += " [const]"
            else:
                param_sig = "[const]"

        return param_sig

    def _process_base_param(self, decl_param):
        params = decl_param.get("params")
        if params:
            # recurse
            params = [self._process_base_param(param) for param in params]
            return f"{decl_param['param']}<{', '.join(params)}>"
        else:
            return decl_param["param"]

    def _make_base_params(
        self, base_decl_params, pybase_params: typing.Set[str]
    ) -> str:
        base_params = [
            self._process_base_param(decl_param) for decl_param in base_decl_params
        ]

        for decl_param in base_params:
            pybase_params.add(decl_param)

        return ", ".join(base_params)

    def _extract_typealias(
        self,
        in_ta: typing.List[str],
        out_ta: typing.List[str],
        ta_names: typing.Set[str],
    ):
        for typealias in in_ta:
            if typealias.startswith("template"):
                out_ta.append(typealias)
            else:
                teq = typealias.find("=")
                if teq != -1:
                    ta_name = typealias[:teq].strip()
                    out_ta.append(f"using {typealias}")
                else:
                    ta_name = typealias.split("::")[-1]
                    out_ta.append(f"using {ta_name} = {typealias}")
                ta_names.add(ta_name)

    def _enum_hook(
        self, cpp_scope: str, scope_var: str, var_name: str, en, enum_data: EnumData
    ) -> EnumContext:
        ename = en.get("name")
        value_prefix = None
        strip_prefixes = []
        values: typing.List[EnumeratorContext] = []

        py_name = ""
        full_cpp_name = ""

        ename = en.get("name", "")

        if ename:
            full_cpp_name = f"{cpp_scope}{ename}"
            py_name = self._make_py_name(ename, enum_data)

            value_prefix = enum_data.value_prefix
            if not value_prefix:
                value_prefix = ename

            strip_prefixes = [f"{value_prefix}_", value_prefix]

        for v in en["values"]:
            name = v["name"]
            v_data = enum_data.values.get(name)
            if v_data is None:
                v_data = EnumValue()

            values.append(
                EnumeratorContext(
                    cpp_name=f"{full_cpp_name}::{name}",
                    py_name=self._make_py_name(name, v_data, strip_prefixes),
                    doc=self._process_doc(v, v_data, append_prefix="  "),
                )
            )

        return EnumContext(
            scope_var=scope_var,
            var_name=var_name,
            full_cpp_name=full_cpp_name,
            py_name=py_name,
            values=values,
            doc=self._process_doc(en, enum_data),
        )

    def header_hook(self, header, data):
        """Called for each header"""

        self.hctx.rel_fname = header["rel_fname"]

        for i, en in enumerate(header.enums):
            enum_data = self.gendata.get_enum_data(en.get("name"))

            if not enum_data.ignore:
                scope_var = self._get_module_var(en, enum_data)
                var_name = f"enum{i}"
                self.hctx.enums.append(
                    self._enum_hook(en["namespace"], scope_var, var_name, en, enum_data)
                )

        for v in header.variables:
            # TODO: in theory this is used to wrap global variables, but it's
            # currently totally ignored
            self.gendata.get_prop_data(v["name"])
            self._add_type_caster(v["raw_type"])

        for _, u in header.using.items():
            self._add_type_caster(u["raw_type"])

        for i, (k, tmpl_data) in enumerate(data["data"].templates.items()):
            qualname = tmpl_data.qualname
            if "::" not in qualname:
                qualname = f"::{qualname}"
            qualname = qualname.translate(self._qualname_trans)

            doc_add = tmpl_data.doc_append
            if doc_add:
                doc_add = f"\n{doc_add}"

            self.hctx.template_instances.append(
                TemplateInstanceContext(
                    scope_var=self._get_module_var(tmpl_data.dict(), tmpl_data),
                    var_name=f"tmplCls{i}",
                    py_name=k,
                    binding_object=f"rpygen::bind_{qualname}",
                    type_params=tmpl_data.params,
                    header_name=f"{qualname}.hpp",
                    doc_set=self._quote_doc(tmpl_data.doc),
                    doc_add=self._quote_doc(doc_add),
                )
            )

            for param in tmpl_data.params:
                self._add_type_caster(param)

        self.hctx.type_caster_includes = self._get_type_caster_includes()

        user_typealias = []
        self._extract_typealias(self.rawdata.typealias, user_typealias, set())
        self.hctx.user_typealias = user_typealias

    def _function_hook(
        self, fn, data: FunctionData, scope_var: str, internal: bool = False
    ) -> FunctionContext:
        """shared with methods/functions"""

        # if cpp_code is specified, don't release the gil unless the user
        # specifically asks for it
        if data.no_release_gil is None:
            if data.cpp_code:
                data.no_release_gil = True

        x_all_params: typing.List[ParamContext] = []
        x_in_params: typing.List[ParamContext] = []
        x_out_params: typing.List[ParamContext] = []
        x_filtered_params: typing.List[ParamContext] = []
        x_rets: typing.List[ReturnParamContext] = []
        x_temps: typing.List[ParamContext] = []
        x_keepalives = []

        param_remap = {}

        x_genlambda = False
        x_lambda_pre: typing.List[str] = []
        x_lambda_post: typing.List[str] = []

        # Use this if one of the parameter types don't quite match
        param_override = data.param_override

        # buffers: accepts a python object that supports the buffer protocol
        #          as input. If the buffer is an 'out' buffer, then it
        #          will request a writeable buffer. Data is written by the
        #          wrapped function to that buffer directly, and the length
        #          written (if the length is a pointer) will be returned
        buffer_params: typing.Dict[str, BufferData] = {}
        buflen_params: typing.Dict[str, BufferData] = {}
        if data.buffers:
            for bufinfo in data.buffers:
                if bufinfo.src == bufinfo.len:
                    raise ValueError(
                        f"buffer src({bufinfo.src}) and len({bufinfo.len}) cannot be the same"
                    )
                buffer_params[bufinfo.src] = bufinfo
                buflen_params[bufinfo.len] = bufinfo

        self._add_type_caster(fn["returns"])

        is_constructor = fn.get("constructor")

        for i, p in enumerate(fn["parameters"]):

            p_const = p_const
            p_reference = p["reference"]
            p_pointer = p["pointer"]

            if is_constructor and p_reference == 1:
                x_keepalives.append((1, i + 2))

            if p["raw_type"] in _int32_types:
                fundamental = True
            else:
                fundamental = p["fundamental"]

            cpp_type_no_const = p.get("enum", p["raw_type"])
            cpp_type = cpp_type_no_const

            p_name = p["name"]
            orig_pname = p_name
            if p_name == "":
                p_name = f"param{i}"

            if p_pointer:
                call_name = p_name
            elif p_reference:
                call_name = f"std::forward<decltype({p['name']})>({p['name']})"
            else:
                call_name = f"std::move({p['name']})"

            virtual_call_name = p_name
            cpp_retname = orig_pname

            # TODO: this is precarious
            # - needs to override some things
            force_out = False
            po = param_override.get(p_name)
            if po:
                force_out = po.force_out
                if po.name:
                    p_name = po.name
                if po.x_type:
                    cpp_type = po.x_type
                if po.default:
                    default = po.default

            py_pname = p_name
            if iskeyword(py_pname):
                py_pname = f"{py_pname}_"

            if orig_pname != py_pname:
                param_remap[orig_pname] = py_pname

            py_arg = f'py::arg("{py_pname}")'

            default = p.get("default", None)
            if default:
                default = self._resolve_default(fn, p, default)
                default = self._maybe_add_default_arg_cast(p, default, cpp_type)
                if default:
                    py_arg = f"{py_arg} = {default}"

            ptype = "in"

            buflen = buflen_params.pop(p_name, None)

            if p_name in buffer_params:
                bufinfo = buffer_params.pop(p_name)
                x_genlambda = True
                bname = f"__{bufinfo.src}"
                p_const = 1
                p_reference = 1
                p_pointer = 0

                call_name = f"({cpp_type}*){bname}.ptr"
                cpp_type = "py::buffer"

                # this doesn't seem to be true for bytearrays, which is silly
                # x_lambda_pre.append(
                #     f'if (PyBuffer_IsContiguous((Py_buffer*){p_name}.ptr(), \'C\') == 0) throw py::value_error("{p_name}: buffer must be contiguous")'
                # )

                # TODO: check for dimensions, strides, other dangerous things

                # bufinfo was validated and converted before it got here
                if bufinfo.type is BufferType.IN:
                    ptype = "in"
                    x_lambda_pre += [f"auto {bname} = {p_name}.request(false)"]
                else:
                    ptype = "in"
                    x_lambda_pre += [f"auto {bname} = {p_name}.request(true)"]

                x_lambda_pre += [f"{bufinfo.len} = {bname}.size * {bname}.itemsize"]

                if bufinfo.minsz:
                    x_lambda_pre.append(
                        f'if ({bufinfo.len} < {bufinfo.minsz}) throw py::value_error("{p_name}: minimum buffer size is {bufinfo.minsz}")'
                    )

            elif buflen:
                if p_pointer:
                    call_name = f"&{buflen.len}"
                    ptype = "out"
                else:
                    # if it's not a pointer, then the called function
                    # can't communicate through it, so ignore the parameter
                    call_name = buflen.len
                    x_temps.append(p)
                    ptype = "ignored"

            elif force_out or (
                (p_pointer or p_reference == 1) and not p_const and fundamental
            ):
                if p_pointer:
                    call_name = f"&{call_name}"
                else:
                    call_name = p_name

                ptype = "out"
            elif p["array"]:
                asz = p.get("array_size", 0)
                if asz:
                    cpp_type = f"std::array<{cpp_type}, {asz}>"
                    call_name = f"{call_name}.data()"
                    if not default:
                        default = "{}"
                else:
                    # it's a vector
                    pass
                ptype = "out"

            self._add_type_caster(cpp_type)

            if p_const:
                cpp_type = f"const {cpp_type}"

            x_type_full = cpp_type
            x_type_full += "&" * p_reference
            x_type_full += "*" * p_pointer

            x_decl = f"{x_type_full} {p_name}"

            pctx = ParamContext(
                full_cpp_type=x_type_full,
                cpp_type=cpp_type,
                cpp_type_no_const=cpp_type_no_const,
                default=default,
                decl=x_decl,
                py_name=p_name,
                py_arg=py_arg,
                call_name=call_name,
                virtual_call_name=virtual_call_name,
                cpp_retname=cpp_retname,
                const=p_const,
                volatile=p["volatile"],
                array=p.get("array"),
                refs=p_reference,
                pointers=p_pointer,
            )

            x_all_params.append(pctx)
            if not p.get("ignore"):
                x_filtered_params.append(pctx)
                if ptype == "out":
                    x_out_params.append(pctx)
                    x_temps.append(pctx)
                elif ptype == "in":
                    x_in_params.append(pctx)

        if buffer_params:
            raise ValueError(
                "incorrect buffer param names '%s'"
                % ("', '".join(buffer_params.keys()))
            )

        x_callstart = ""
        x_callend = ""
        x_wrap_return = ""
        x_return_value_policy = _rvp_map[data.return_value_policy]

        if x_out_params:
            x_genlambda = True

            # Return all out parameters
            x_rets.extend(x_out_params)

        if fn["rtnType"] != "void":
            x_callstart = "auto __ret ="
            x_rets.insert(
                0, ReturnParamContext(cpp_retname="__ret", cpp_type=fn["rtnType"])
            )
            # dict(x_retname="__ret", x_type=fn["rtnType"])

        if len(x_rets) == 1 and x_rets[0].cpp_type != "void":
            x_wrap_return = f"return {x_rets[0].cpp_retname};"
        elif len(x_rets) > 1:
            x_wrap_return = "return std::make_tuple(%s);" % ",".join(
                [p.cpp_retname for p in x_rets]
            )

        # Temporary values to store out parameters in
        if x_temps:
            for out in reversed(x_temps):
                odef = out.default
                if not odef:
                    x_lambda_pre.insert(0, f"{out.cpp_type} {out.cpp_name}")
                elif odef.startswith("{"):
                    x_lambda_pre.insert(0, f"{out.cpp_type} {out.cpp_name}{odef}")
                else:
                    x_lambda_pre.insert(0, f"{out.cpp_type} {out.cpp_name} = {odef}")

        # Set up the function's name
        if data.rename:
            # user preference wins, of course
            py_name = data.rename
        elif fn["constructor"]:
            py_name = "__init__"
        else:
            # Python exposed function name converted to camelcase
            py_name = self._make_py_name(
                fn["name"], data, is_operator=fn.get("operator", False)
            )
            if not py_name[:2].isupper():
                py_name = f"{py_name[0].lower()}{py_name[1:]}"

            elif data.internal or internal:
                py_name = f"_{py_name}"

        doc_quoted = self._process_doc(fn, data, param_remap=param_remap)

        if data.keepalive is not None:
            x_keepalives = data.keepalive

        if not self.report_only:
            if fn["template"]:
                if data.template_impls is None and not data.cpp_code:
                    raise ValueError(
                        f"{fn['name']}: must specify template impls for function template"
                    )
            else:
                if data.template_impls is not None:
                    raise ValueError(
                        f"{fn['name']}: cannot specify template_impls for non-template functions"
                    )

            if data.ignore_pure and not fn["pure_virtual"]:
                raise ValueError(
                    f"{fn['name']}: cannot specify ignore_pure for function that isn't pure"
                )

            if data.trampoline_cpp_code and (not fn["override"] and not fn["virtual"]):
                raise ValueError(
                    f"{fn['name']}: cannot specify trampoline_cpp_code for a non-virtual method"
                )

            if data.virtual_xform and (not fn["override"] and not fn["virtual"]):
                raise ValueError(
                    f"{fn['name']}: cannot specify virtual_xform for a non-virtual method"
                )

            if fn.get("ref_qualifiers", "") == "&&":
                # pybind11 doesn't support this, user must fix it
                if not data.ignore_py and not data.cpp_code:
                    raise ValueError(
                        f"{fn['name']}: has && ref-qualifier which cannot be directly bound by pybind11, must specify cpp_code or ignore_py"
                    )

        return FunctionContext(
            cpp_name=fn["name"],
            doc=doc_quoted,
            # transforms
            py_name=py_name,
            all_params=x_all_params,
            filtered_params=x_filtered_params,
            in_params=x_in_params,
            out_params=x_out_params,
            x_rets=x_rets,
            keepalives=x_keepalives,
            return_value_policy=x_return_value_policy,
            # lambda generation
            x_genlambda=x_genlambda,
            x_callstart=x_callstart,
            x_lambda_pre=x_lambda_pre,
            x_lambda_post=x_lambda_post,
            x_callend=x_callend,
            x_wrap_return=x_wrap_return,
            # info
            const=fn["const"],
            vararg=fn["vararg"],
            # user settings
            ignore_pure=data.ignore_pure,
            cpp_code=data.cpp_code,
            ifdef=data.ifdef,
            ifndef=data.ifndef,
            release_gil=not data.no_release_gil,
            template_impls=data.template_impls,
            virtual_xform=data.virtual_xform,
        )

    def function_hook(self, fn, h2w_data):
        # Operators aren't rendered
        if fn.get("operator"):
            return

        signature = self._get_function_signature(fn)
        data = self.gendata.get_function_data(fn, signature)
        if data.ignore:
            return

        scope_var = self._get_module_var(fn, data)
        fctx = self._function_hook(fn, data, scope_var)
        self.hctx.functions.append(fctx)

    def class_hook(self, cls, h2w_data):

        # ignore private classes
        if cls["parent"] is not None and cls["access_in_parent"] == "private":
            return

        cls_name = cls["name"]
        cls_key = cls_name
        c = cls
        while c["parent"]:
            c = c["parent"]
            cls_key = c["name"] + "::" + cls_key

        class_data = self.gendata.get_class_data(cls_key)

        if class_data.ignore:
            return

        for _, u in cls["using"].items():
            self._add_type_caster(u["raw_type"])

        for typename in class_data.force_type_casters:
            self._add_type_caster(typename)

        scope_var = self._get_module_var(cls, class_data)
        var_name = f"cls_{cls_name}"

        enums: typing.List[EnumContext] = []

        # fix enum paths
        for i, e in enumerate(cls["enums"]["public"]):
            enum_data = self.gendata.get_cls_enum_data(
                e.get("name"), cls_key, class_data
            )
            if not enum_data.ignore:
                scope = f"{e['namespace']}::{cls_name}::"
                enum_var_name = f"{var_name}_enum{i}"
                ectx = self._enum_hook(scope, var_name, enum_var_name, e, enum_data)
                enums.append(ectx)

        # update inheritance

        pybase_params = set()
        bases: typing.List[BaseClassData] = []
        ignored_bases = {ib: True for ib in class_data.ignored_bases}

        for base in cls["inherits"]:
            if ignored_bases.pop(base["class"], None) or base["access"] == "private":
                continue

            bqual = class_data.base_qualnames.get(base["decl_name"])
            if bqual:
                full_cpp_name_w_templates = bqual
                # TODO: sometimes need to add this to pybase_params, but
                # that would require parsing this more. Seems sufficiently
                # obscure, going to omit it for now.
                tp = bqual.find("<")
                if tp == -1:
                    base_full_cpp_name = bqual
                    template_params = ""
                else:
                    base_full_cpp_name = bqual[:tp]
                    template_params = bqual[tp + 1 : -1]
            else:
                if "::" not in base["decl_name"]:
                    base_full_cpp_name = f'{cls["namespace"]}::{base["decl_name"]}'
                else:
                    base_full_cpp_name = base["decl_name"]

                base_decl_params = base.get("decl_params")
                if base_decl_params:
                    template_params = self._make_base_params(
                        base_decl_params, pybase_params
                    )
                    full_cpp_name_w_templates = (
                        f"{base_full_cpp_name}<{base['x_params']}>"
                    )
                else:
                    template_params = ""
                    full_cpp_name_w_templates = base_full_cpp_name

            base_identifier = base_full_cpp_name.translate(self._qualname_trans)

            bases.append(
                BaseClassData(
                    full_cpp_name=base_full_cpp_name,
                    full_cpp_name_w_templates=full_cpp_name_w_templates,
                    full_cpp_name_identifier=base_identifier,
                    template_params=template_params,
                )
            )

        if not self.report_only and ignored_bases:
            bases = ", ".join(base["class"] for base in cls["inherits"])
            invalid_bases = ", ".join(ignored_bases.keys())
            raise ValueError(
                f"{cls_name}: ignored_bases contains non-existant bases "
                + f"{invalid_bases}; valid bases are {bases}"
            )

        # No template stuff
        simple_cls_qualname = f'{cls["namespace"]}::{cls_name}'

        # Template stuff
        parent_ctx: typing.Optional[ClassContext] = None
        if cls["parent"]:
            parent_ctx = cls["parent"]["class_ctx"]
            cls_qualname = f"{parent_ctx.full_cpp_name}::{cls_name}"
        else:
            cls_qualname = simple_cls_qualname

        cls_cpp_identifier = cls_qualname.translate(self._qualname_trans)
        self.hctx.class_hierarchy[simple_cls_qualname] = [
            base.full_cpp_name for base in bases
        ] + class_data.force_depends

        # <N, .. >
        template_argument_list = ""
        # <typename N, .. >
        template_parameter_list = ""

        if class_data.template_params:
            if class_data.subpackage:
                raise ValueError(
                    f"{cls_name}: classes with subpackages must define subpackage on template instantiation"
                )

            template_args = []
            template_params = []

            base_template_args = []
            base_template_params = []

            for param in class_data.template_params:
                if " " in param:
                    arg = param.split(" ", 1)[1]
                else:
                    arg = param
                    param = f"typename {param}"

                template_args.append(arg)
                template_params.append(param)

                if arg in pybase_params:
                    base_template_args.append(arg)
                    base_template_params.append(param)

            template_argument_list = ", ".join(template_args)
            template_parameter_list = ", ".join(template_params)

            cls_qualname = f"{cls_qualname}<{template_argument_list}>"
        else:
            base_template_params = None
            base_template_args = None

        if base_template_params:
            pybase_args = ", ".join(base_template_args)
            pybase_params = ", ".join(base_template_params)
        else:
            pybase_args = ""
            pybase_params = ""

        if not self.report_only:
            if "template" in cls:
                if template_parameter_list == "":
                    raise ValueError(
                        f"{cls_name}: must specify template_params for templated class, or ignore it"
                    )
            else:
                if template_parameter_list != "":
                    raise ValueError(
                        f"{cls_name}: cannot specify template_params for non-template class"
                    )

        has_constructor = False
        is_polymorphic = class_data.is_polymorphic
        vcheck_fns: typing.List[FunctionContext] = []

        # bad assumption? yep
        if cls["inherits"]:
            is_polymorphic = True

        public_methods: typing.List[FunctionContext] = []
        protected_methods: typing.List[FunctionContext] = []
        private_methods: typing.List[FunctionContext] = []

        for access, methods in (
            ("public", public_methods),
            ("protected", protected_methods),
            ("private", private_methods),
        ):

            for fn in cls["methods"][access]:
                if fn["constructor"]:
                    has_constructor = True
                if fn["override"] or fn["virtual"]:
                    is_polymorphic = True

                operator = fn.get("operator")

                # Ignore some operators, move constructors, copy constructors
                if (
                    (operator and operator not in _operators)
                    or fn.get("destructor")
                    or (
                        fn.get("constructor")
                        and fn["parameters"]
                        and fn["parameters"][0]["class"] is cls
                    )
                    or fn["deleted"]
                ):
                    continue

                is_private = access == "private"
                is_virtual = fn["override"] or fn["virtual"]

                # this has to be done even on private functions, because
                # we do overload detection here
                signature = self._get_function_signature(fn)
                method_data = self.gendata.get_function_data(
                    fn, signature, cls_key, class_data, is_private
                )

                # Have to process private virtual functions too
                if not is_private or is_virtual:
                    if method_data.ignore:
                        # TODO: can't do this, need final private
                        continue

                    if operator:
                        self.hctx.need_operators_h = True
                        if method_data.no_release_gil is None:
                            method_data.no_release_gil = True

                    internal = access != "public"

                    try:
                        fctx = self._function_hook(
                            fn, method_data, var_name, internal=internal
                        )
                    except Exception as e:
                        raise HookError(f"{cls_key}::{fn['name']}") from e
                    else:
                        methods.append(fctx)

                    # If the method has cpp_code defined, it must either match the function
                    # signature of the method, or virtual_xform must be defined with an
                    # appropriate conversion. If neither of these are true, it will lead
                    # to difficult to diagnose errors at runtime. We add a static assert
                    # to try and catch these errors at compile time
                    need_vcheck = (
                        (fn["override"] or fn["virtual"])
                        and method_data.cpp_code
                        and not method_data.virtual_xform
                        and not method_data.trampoline_cpp_code
                        and not cls["final"]
                        and not class_data.force_no_trampoline
                    )
                    if need_vcheck:
                        vcheck_fns.append(fctx)
                        self.hctx.has_vcheck = True

        has_trampoline = (
            is_polymorphic and not cls["final"] and not class_data.force_no_trampoline
        )

        public_properties: typing.List[PropContext] = []
        protected_properties: typing.List[PropContext] = []

        for access, props in (
            ("public", public_properties),
            ("protected", protected_properties),
        ):
            # cannot bind protected properties without a trampoline, so
            # don't bother processing them if there isn't one
            if access == "protected" and not has_trampoline:
                continue

            # class attributes
            for v in cls["properties"][access]:

                prop_name = v["name"]
                propdata = self.gendata.get_cls_prop_data(
                    prop_name, cls_key, class_data
                )
                self._add_type_caster(v["raw_type"])
                if propdata.rename:
                    prop_name = propdata.rename
                else:
                    prop_name = v["name"] if access == "public" else "_" + v["name"]

                if propdata.access == PropAccess.AUTOMATIC:
                    # const variables can't be written
                    if v["constant"] or v["constexpr"]:
                        prop_readonly = True
                    # We assume that a struct intentionally has readwrite data
                    # attributes regardless of type
                    elif cls["declaration_method"] != "class":
                        prop_readonly = False
                    else:
                        # Properties that aren't fundamental or a reference are readonly unless
                        # overridden by the hook configuration
                        prop_readonly = not v["fundamental"] and not v["reference"]
                elif propdata.access == PropAccess.READONLY:
                    prop_readonly = True
                else:
                    prop_readonly = False

                doc = self._process_doc(v, propdata)

                props.append(
                    PropContext(
                        py_name=prop_name,
                        cpp_name=v["name"],
                        cpp_type=v["type"],
                        readonly=prop_readonly,
                        doc=doc,
                        array_size=v.get("array_size", None),
                        array=v["array"],
                        reference=v["reference"],
                        static=v["static"],
                    )
                )

        tctx: typing.Optional[TrampolineData] = None

        if has_trampoline:
            tmpl = ""
            if template_argument_list:
                tmpl = f", {template_argument_list}"

            trampoline_cfg = f"rpygen::PyTrampolineCfg_{cls_cpp_identifier}<{template_argument_list}>"
            tname = f"rpygen::PyTrampoline_{cls_cpp_identifier}<typename {cls_qualname}{tmpl}, typename {trampoline_cfg}>"
            tvar = f"{cls_name}_Trampoline"
            tctx = TrampolineData(
                name=tname,
                var=tvar,
                inline_code=class_data.trampoline_inline_code,
            )

        elif class_data.trampoline_inline_code is not None:
            raise HookError(
                f"{cls_key} has trampoline_inline_code specified, but there is no trampoline!"
            )

        # do logic for extracting user defined typealiases here
        # - these are at class scope, so they can include template
        typealias_names = set()
        user_typealias = []
        self._extract_typealias(class_data.typealias, user_typealias, typealias_names)

        # autodetect embedded using directives, but don't override anything
        # the user specifies
        # - these are in block scope, so they cannot include templates
        auto_typealias = []
        for name, using in cls["using"].items():
            if (
                using["access"] == "public"
                and name not in typealias_names
                and not using["template"]
                and using["using_type"] == "typealias"
            ):
                auto_typealias.append(
                    f"using {name} [[maybe_unused]] = typename {cls['x_qualname']}::{name}"
                )

        doc = self._process_doc(cls, class_data)
        py_name = self._make_py_name(cls_name, class_data)

        cctx = ClassContext(
            parent=parent_ctx,
            full_cpp_name=cls_qualname,
            full_cpp_name_identifier=cls_cpp_identifier,
            py_name=py_name,
            scope_var=scope_var,
            var_name=var_name,
            has_constructor=has_constructor,
            nodelete=class_data.nodelete,
            final=cls["final"],
            doc=doc,
            bases=bases,
            trampoline=tctx,
            public_properties=public_properties,
            protected_properties=protected_properties,
            enums=enums,
            pybase_args=pybase_args,
            pybase_params=pybase_params,
            template_parameter_list=template_parameter_list,
            template_inline_code=class_data.template_inline_code,
            user_typealias=user_typealias,
            auto_typealias=user_typealias,
            constants=class_data.constants,
            inline_code=class_data.inline_code or "",
            vcheck_fns=vcheck_fns,
        )

        # store this to facilitate finding data in parent
        cls["class_ctx"] = cctx
        self.hctx.classes.append(cctx)
