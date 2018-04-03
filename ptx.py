import pyparsing as p

follow_sym = p.Word(p.alphas + p.nums + '$_')
prefix = p.Literal('_') | p.Literal('$') | p.Literal('%')
identifier = (p.Word(p.alphas) + p.ZeroOrMore(follow_sym)) | (prefix + follow_sym)

hexadecimal = "0" + p.CaselessLiteral('x') + p.Word(p.hexnums)
