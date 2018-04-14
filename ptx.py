import pyparsing as p
from functools import reduce

def literals_of(*args):
    return reduce(lambda x, y: x | y, map(p.Literal, args))

def all_concats(*toks):
    def helper(left, right):
        return [i + j for i in left for j in right]

    return reduce(helper, toks)


follow_sym = p.Word(p.alphas + p.nums + '$_')
prefix = literals_of('$', '_', '.')
identifier = p.Group(prefix * (0, 1) + follow_sym)

hexadecimal = "0" + p.CaselessLiteral('x') + p.Word(p.hexnums) + p.Literal('U') * (0, 1)
octal = "0" + p.Word(''.join(map(str, range(8)))) + p.Literal('U') * (0, 1)
binary = "0" + p.CaselessLiteral('b') + p.Word('01') + p.Literal('U') * (0, 1)
decimal = literals_of(*(str(i) for i in range(1, 10))) + p.Word(''.join(map(str, range(10)))) + p.Literal('U') * (0, 1)
integer_literal = p.Group(hexadecimal | octal | binary | decimal)

float_literal = p.Group("0" + p.CaselessLiteral('f') + p.Literal(p.hexnums) * 8)
double_literal = p.Group("0" + p.CaselessLiteral('f') + p.Literal(p.hexnums) * 16)

predicate_const = literals_of('True', 'False')

ptx_literal = integer_literal | float_literal | double_literal | predicate_const

instruction = literals_of(
        'abs', 'div', 'or', 'sin', 'vavrg2', 'vavrg4',
        'add', 'ex2', 'pmevent', 'slct', 'vmad',
        'addc', 'exit', 'popc', 'sqrt', 'vmax',
        'and', 'fma', 'prefetch', 'st', 'vmax2', 'vmax4',
        'atom', 'isspacep', 'prefetchu', 'sub', 'vmin',
        'bar', 'ld', 'prmt', 'subc', 'vmin2', 'vmin4',
        'bfe', 'ldu', 'rcp', 'suld', 'vote', 'bfi',
        'lg2', 'red', 'suq', 'vset', 'bfind', 'mad',
        'rem', 'sured', 'vset2', 'vset4', 'bra', 'mad24',
        'ret', 'sust', 'vshl', 'brev', 'madc', 'rsqrt',
        'testp', 'vshr', 'brkpt', 'max', 'sad', 'tex',
        'vsub', 'call', 'membar', 'selp', 'tld4', 'vsub2', 'vsub4',
        'clz', 'min', 'set', 'trap', 'xor', 'cnot', 'mov', 'setp',
        'txq', 'copysign', 'mul', 'shf', 'vabsdiff', 'cos', 'mul24',
        'shfl', 'vabsdiff2', 'vabsdiff4', 'cvt', 'neg', 'shl', 'vadd',
        'cvta', 'not', 'shr', 'vadd2', 'vadd4')

types = ['.u16', '.u32', '.u64', '.s16', '.s32', '.s64']
float_bits = all_concats(['.rn', '.rz', '.rm', '.rp'], all_concats(['.ftz', ''], ['.sat', ''], ['.f32']) + ['.f32'])
add = literals_of(*all_concats(["add"], types + ['.sat.s32']))
sub = literals_of(*all_concats(["sub"], types + ['.sat.s32']))
mul = literals_of(*all_concats(["mul"], [".hi", ".lo", ".wide"], types))
mad = literals_of(*all_concats(["mad"], [".hi", ".lo", ".wide"], types + ['.sat.s32']))
div = literals_of(*all_concats(["div"], types))
rem = literals_of(*all_concats(["rem"], types))
abs_instr = literals_of(*all_concats(["abs"], [i for i in types if i[0] == 's']))
neg = literals_of(*all_concats(["neg"], [i for i in types if i[0] == 's']))
popc = literals_of(*all_concats(["popc"], [".b32", ".b64"]))

float_types = ['.finite', '.infinite', '.number', '.notanumber', '.normal', '.subnormal']
float_testp = literals_of(*all_concats(["testp"], float_types, ['.f32', '.f64']))
copysign = literals_of(*all_concats(['copysign'], ['.f32', '.f64']))

label = p.Group(identifier + ':')
gaurd = p.Group('@' + p.Literal('!') * (0, 1) + identifier)
statement = (label | gaurd) * (0, 1) + instruction + p.delimitedList(identifier | ptx_literal) * (0, 1) + ';'
