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
decimal = literals_of(*(str(i) for i in range(10))) + p.Word(''.join(map(str, range(10)))) * (0, 1) + p.Literal('U') * (0, 1)
integer_literal = p.Group(hexadecimal | octal | binary | decimal)

float_literal = p.Group("0" + p.CaselessLiteral('f') + p.Literal(p.hexnums) * 8)
double_literal = p.Group("0" + p.CaselessLiteral('f') + p.Literal(p.hexnums) * 16)

predicate_const = literals_of('True', 'False')

ptx_literal = integer_literal | float_literal | double_literal | predicate_const

# instruction = literals_of(
#         'abs', 'div', 'or', 'sin', 'vavrg2', 'vavrg4',
#         'add', 'ex2', 'pmevent', 'slct', 'vmad',
#         'addc', 'exit', 'popc', 'sqrt', 'vmax',
#         'and', 'fma', 'prefetch', 'st', 'vmax2', 'vmax4',
#         'atom', 'isspacep', 'prefetchu', 'sub', 'vmin',
#         'bar', 'ld', 'prmt', 'subc', 'vmin2', 'vmin4',
#         'bfe', 'ldu', 'rcp', 'suld', 'vote', 'bfi',
#         'lg2', 'red', 'suq', 'vset', 'bfind', 'mad',
#         'rem', 'sured', 'vset2', 'vset4', 'bra', 'mad24',
#         'ret', 'sust', 'vshl', 'brev', 'madc', 'rsqrt',
#         'testp', 'vshr', 'brkpt', 'max', 'sad', 'tex',
#         'vsub', 'call', 'membar', 'selp', 'tld4', 'vsub2', 'vsub4',
#         'clz', 'min', 'set', 'trap', 'xor', 'cnot', 'mov', 'setp',
#         'txq', 'copysign', 'mul', 'shf', 'vabsdiff', 'cos', 'mul24',
#         'shfl', 'vabsdiff2', 'vabsdiff4', 'cvt', 'neg', 'shl', 'vadd',
#         'cvta', 'not', 'shr', 'vadd2', 'vadd4')

types_not64 = ['.u16', '.u32', '.s16', '.s32']
types = ['.u16', '.u32', '.u64', '.s16', '.s32', '.s64']
float_bits = all_concats(['.rn', '.rz', '.rm', '.rp'],
        all_concats(['.ftz', ''], ['.sat', ''], ['.f32']) + ['.f64'])
add = literals_of(*all_concats(["add"], types + ['.sat.s32'] + float_bits))
sub = literals_of(*all_concats(["sub"], types + ['.sat.s32'] + float_bits))
mul = literals_of(*all_concats(["mul"], all_concats([".wide"], types_not64) + float_bits + all_concats([".hi", ".lo"], types)))
mad = literals_of(*all_concats(["mad"],
    all_concats([".hi", ".lo", ".wide"], types + ['.sat.s32'])
    + float_bits + all_concats(['.ftz', ''], ['.sat', ''], ['.f32'])))

div_float_types = all_concats(['.approx', '.full'], ['.ftz', ''], ['.f32'])\
        + [i for i in float_bits if '.sat' not in i]
div = literals_of(*all_concats(["div"], types + div_float_types))
rem = literals_of(*all_concats(["rem"], types))
abs_instr = literals_of(*all_concats(["abs"], [i for i in types if i[1] == 's']))
neg = literals_of(*all_concats(["neg"], [i for i in types if i[1] == 's']
    + all_concats(['.ftz', ''], ['.f32']) + ['.f64']))
popc = literals_of(*all_concats(["popc"], [".b32", ".b64"]))

float_types = ['.finite', '.infinite', '.number', '.notanumber', '.normal', '.subnormal']
float_testp = literals_of(*all_concats(["testp"], float_types, ['.f32', '.f64']))
copysign = literals_of(*all_concats(['copysign'], ['.f32', '.f64']))

cmp_op = [ '.eq', '.ne', '.lt', '.gt', '.ge', '.lo', '.ls', '.hi', '.hs',
        '.equ', '.neu', '.ltu', '.leu', '.gtu', '.geu', '.num', '.nan']
bool_op = [ '.and', '.or', '.xor', '']
dtype = ['.u32', '.s32', '.f32']
stype = all_concats(['.u', '.s', '.b'], ['16', '32', '64']) + ['.f32', '.f64']
set_instr = literals_of(*all_concats(['set'], cmp_op, bool_op, ['', '.ftz'], dtype, stype))

instruction = add | sub | mul | mad | div | rem\
        | abs_instr | neg | popc | float_testp | copysign\
        | set_instr
label = p.Group(identifier + ':')
gaurd = p.Group('@' + p.Literal('!') * (0, 1) + identifier)
statement = (label | gaurd) * (0, 1) + instruction + p.delimitedList(identifier | ptx_literal) * (0, 1) + ';'

def handle_file(path):
    with open(path) as fil:
        for l in fil:
            l = l.strip()
            yield statement.parseString(l)

def get_instr(parsed):
    if parsed[0].startswith('.') or parsed[0].startswith('@'):
        return parsed[1], 1
    return parsed[0], 0

try:
    statement.parseString("mul.hi.u32 a, b, c;")
except:
    #TODO: figure out better caching hack.
    #(it basically has too many possible instructions so seems to recurse
    #too much until it caches stuff).
    pass

if __name__ == "__main__":
    from sys import argv
    statement.parseString("mul.hi.u32 a, b, c;")
    test = list(handle_file(argv[1]))
    print(test)
    print(integer_literal.parseString('0'))
