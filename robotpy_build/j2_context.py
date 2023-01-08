#
# These dataclasses hold data to be rendered by the *.j2 files in templates
#
# To simplify the templates, where possible we try to do logic in the code
# that produces this data instead of in the templates.
#
# We also prefer to copy over data from the autowrap YAML file instead of using
# those data structures directly. While there's some slight overhead added,
# this should help to keep the logic outside of the templates.
#

from dataclasses import dataclass, field
from robotpy_build.config.autowrap_yml import ReturnValuePolicy
import typing

Documentation = typing.Optional[typing.List[str]]


@dataclass
class EnumeratorContext:

    #: Name in C++
    cpp_name: str

    #: Name in python
    py_name: str

    #: Documentation
    doc: Documentation


@dataclass
class EnumContext:

    #: Name of parent variable in initializer
    scope_var: str

    #: Name of variable in initializer
    var_name: str

    #: C++ name, including namespace/classname
    full_cpp_name: str

    #: Python name
    py_name: str

    #: Enum values
    values: typing.List[EnumeratorContext]

    #: Documentation
    doc: Documentation


@dataclass
class ReturnParamContext:

    #: was x_type
    cpp_type: str

    #: If this is an out parameter, the name of the parameter
    cpp_retname: str


@dataclass
class ParamContext(ReturnParamContext):

    # was: x_type_full
    full_cpp_type: str

    # In mangle: param.get("enum", param["raw_type"])
    # in params:
    #  p["x_type"] = p.get("enum", p["raw_type"])
    #  .. but then this is changed later
    #  .. changed type, or adds a const

    #: original type without const, used in mangle
    cpp_type_no_const: str

    default: typing.Optional[str]

    # type + name
    decl: str

    #: Parameter name in python
    py_name: str

    #: py::arg() for pybind11
    py_arg: str

    #: Name to pass to function when calling the original
    call_name: str

    #: Name to pass to function when generating a virtual function
    virtual_call_name: str

    #: type marked as const
    const: bool = False

    #: type marked as volatile
    volatile: bool = False

    array: typing.Optional[int] = None

    # Number of &
    refs: int = 0

    # Number of *
    pointers: int = 0


@dataclass
class FunctionContext:

    #: C++ name of function
    cpp_name: str

    #: Name in python
    py_name: str

    #: parent variable to attach to
    scope_var: str

    #: Documentation
    doc: Documentation

    #: every parameter
    all_params: typing.List[ParamContext]
    #: every parameter except ignored
    filtered_params: typing.List[ParamContext]
    #: input parameters
    in_params: typing.List[ParamContext]
    #: output parameters
    out_params: typing.List[ParamContext]

    #: Marked const
    const: bool

    #: Has vararg parameters
    vararg: bool

    #
    # Mixed
    #

    has_buffers: bool

    keepalives: typing.List[typing.Tuple[int, int]]

    return_value_policy: ReturnValuePolicy

    #
    # User settings from autowrap_yml.FunctionData
    #

    #: If True, don't wrap this, but provide a pure virtual implementation
    ignore_pure: bool

    #: Use this code instead of the generated code
    cpp_code: typing.Optional[str]

    #: Generate this in an `#ifdef`
    ifdef: typing.Optional[str]
    #: Generate this in an `#ifndef`
    ifndef: typing.Optional[str]

    release_gil: bool

    # List of template instantiations
    template_impls: typing.Optional[typing.List[typing.List[str]]]

    virtual_xform: typing.Optional[str]

    # Only compute the trampoline signature once, used as cache by
    # trampoline_signature function
    _trampoline_signature: typing.Optional[str] = None


@dataclass
class PropContext:

    py_name: str
    cpp_name: str
    cpp_type: str  # only used in array
    readonly: bool
    doc: Documentation

    array_size: typing.Optional[int]
    array: bool  # cannot sensibly autowrap an array of incomplete size
    reference: bool
    static: bool


@dataclass
class BaseClassData:
    #: C++ name, including namespace/classname
    full_cpp_name: str  # was x_qualname

    full_cpp_name_w_templates: str  # was x_class

    #: Translated C++ name suitable for use as an identifier. :<>= are
    #: turned into underscores.
    full_cpp_name_identifier: str  # was x_qualname_

    #: comma separated list of template parameters for this base, or empty string
    template_params: str


@dataclass
class TrampolineData:
    name: str
    var: str
    inline_code: typing.Optional[str]


@dataclass
class ClassContext:

    parent: typing.Optional["ClassContext"]

    #: C++ name, including namespace/classname
    full_cpp_name: str

    #: Translated C++ name suitable for use as an identifier. :<>= are
    #: turned into underscores.
    full_cpp_name_identifier: str

    #: Python name
    py_name: str

    #: Name of parent variable in initializer
    scope_var: str

    #: Name of variable in initializer
    var_name: str

    # used for dealing with methods/etc
    has_constructor: bool

    #: If the object shouldn't be deleted by pybind11, use this. Disables
    #: implicit constructors.
    nodelete: bool

    final: bool

    #: Documentation
    doc: Documentation

    bases: typing.List[BaseClassData]

    #: was x_has_trampoline
    trampoline: typing.Optional[TrampolineData]

    public_properties: typing.List[PropContext]
    protected_properties: typing.List[PropContext]

    # pub + protected + final (ignore doesn't matter)
    # private + final or override (ignore doesn't matter)
    # -> to delete, only needs signature
    methods_to_disable = typing.List[FunctionContext]

    # pub + protected + not final + not ignore

    # protected + not ignore + constructor

    # public + protected + not ignore + (virtual + override) + not final + not buffers

    # add default constructor
    # {% if not cls.x_has_constructor and not cls.data.nodelete and not cls.data.force_no_default_constructor %}

    # template_params
    #

    # don't add protected things if trampoline not enabled
    # .. more nuance than that

    enums: typing.List[EnumContext]

    #: <typename N, .. >
    template_parameter_list: str

    #: If this is a template class, the specified C++ code is inserted
    #: into the template definition
    template_inline_code: str

    #: Extra 'using' directives to insert into the trampoline and the
    #: wrapping scope
    user_typealias: typing.List[str]

    #: Extra autodetected 'using' directives
    auto_typealias: typing.List[str]

    #: Extra constexpr to insert into the trampoline and wrapping scopes
    constants: typing.List[str]

    #: Extra code to insert into the class scope
    inline_code: str

    vcheck_fns: typing.List[FunctionContext]


@dataclass
class TemplateInstanceContext:

    #: Name of parent variable in initializer
    scope_var: str

    #: Name of variable in initializer
    var_name: str

    py_name: str

    #: binding object
    binding_object: str

    params: typing.List[str]

    doc_set: Documentation
    doc_add: Documentation


@dataclass
class HeaderContext:

    extra_includes_first: typing.List[str]
    extra_includes: typing.List[str]
    inline_code: typing.Optional[str]

    trampoline_signature: typing.Callable[[FunctionContext], str]
    using_signature: typing.Callable[[ClassContext, FunctionContext], str]

    #
    rel_fname: str = ""

    #: True if <pybind11/operators.h> is needed
    need_operators_h: bool = False

    # TODO: anon enums?
    enums: typing.List[EnumContext] = field(default_factory=list)

    # classes
    classes: typing.List[ClassContext] = field(default_factory=list)

    functions: typing.List[FunctionContext] = field(default_factory=list)

    # trampolines

    # template_classes
    template_instances: typing.List[TemplateInstanceContext] = field(
        default_factory=list
    )

    type_caster_includes: typing.List[str] = field(default_factory=list)
    user_typealias: typing.List[str] = field(default_factory=list)

    using_ns: typing.List[str] = field(default_factory=list)

    subpackages: typing.Dict[str, str] = field(default_factory=dict)

    # key: class name, value: list of classes this class depends on
    class_hierarchy: typing.Dict[str, typing.List[str]] = field(default_factory=dict)

    has_vcheck: bool = False
