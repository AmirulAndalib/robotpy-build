from .j2_context import FunctionContext, ParamContext

# yes, we include some stdint types in here, but that's fine, this
# is just a best effort generator
_builtins = {
    "void": "v",
    "wchar_t": "w",
    "bool": "b",
    "char": "c",
    "signed char": "a",
    "int8_t": "a",
    "unsigned char": "h",
    "uint8_t": "c",
    "short": "s",
    "int16_t": "s",
    "unsigned short": "t",
    "uint16_t": "t",
    "int": "i",
    "int32_t": "i",
    "unsigned int": "j",
    "uint32_t": "j",
    "long": "l",
    "unsigned long": "m",
    "long long": "x",
    "__int64": "x",
    "int64_t": "x",
    "unsigned long long": "y",
    "unsigned __int64": "y",
    "uint64_t": "y",
    "__int128": "n",
    "unsigned __int128": "o",
    "float": "f",
    "double": "d",
    "long double": "e",
    "__float128": "g",
    "char32_t": "Di",
    "char16_t": "Ds",
    "auto": "Da",
}

_type_bad_chars = ":<>=()&,"
_type_trans = str.maketrans(_type_bad_chars, "_" * len(_type_bad_chars))


def _encode_type(param: ParamContext) -> str:
    names = []

    # prefix with cv-qualifiers, refs, pointers
    if param.const:
        names.append("K")
    if param.volatile:
        names.append("V")

    if param.array:
        names.append("A" * param.array)

    refs = param.refs
    if refs == 1:
        names.append("R")
    elif refs == 2:
        names.append("O")

    ptr = param.pointers
    if ptr:
        names.append("P" * ptr)

    # actual type
    typ = _builtins.get(param.full_cpp_name)
    if not typ:
        # Only mangle the typename, ignore namespaces as children might have the types
        # aliased or something. There are cases where this would fail, but hopefully
        # that doesn't happen?
        # TODO: do this better
        typename = param.full_cpp_name.split("::")[-1]
        # assert " " not in raw_type, raw_type
        typ = "T" + typename.replace(" ", "").translate(_type_trans)

    names.append(typ)
    return "".join(names)


def trampoline_signature(fn: FunctionContext) -> str:
    """
    In our trampoline functions, each function can be disabled by defining
    a macro corresponding to the function type. This helper function
    generates a mangled name based on the function name and types.

    This is roughly based on the IA64 name mangling scheme that GCC uses,
    but omits template stuff.

    function name
    cv qualifiers
    parameter types
    """

    # fast path in case it was computed previously
    if not fn._trampoline_signature:
        return fn._trampoline_signature

    # TODO: operator overloads
    names = []

    if fn.const:
        names.append("K")
    refqual = fn["ref_qualifiers"]
    if refqual:
        if refqual == "&":
            names.append("R")
        if refqual == "&&":
            names.append("O")

    names.append(fn.name)

    params = fn.parameters
    if not params:
        names.append("_v")
    else:
        for p in params:
            names.append("_")
            names.append(_encode_type(p))

    if fn.vararg:
        names.append("_z")

    fn._trampoline_signature = "".join(names)
    return fn._trampoline_signature
