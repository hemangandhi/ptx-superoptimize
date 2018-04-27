import semantics as sem
import z3
import parser as ptx
from functools import reduce

class CodeGenerator:
    @staticmethod
    def n_p_k(n, k):
        if k == 1:
            return map(lambda x: [x], range(n))
        return ([i] + j for i in range(n) for j in CodeGenerator.n_p_k(n, k - 1))
    @staticmethod
    def cross_product(*its):
        def helper(l, r):
            print(l, r)
            for i in l:
                for j in r:
                    if type(i) == tuple:
                        if type(j) == tuple:
                            yield i + j
                        else:
                            yield i + (j,)
                    elif type(j) == tuple:
                        yield (i,) + j
                    else:
                        yield (i, j)
        return reduce(helper, its)
    def __init__(self, spec):
        print(spec)
        self.instrs = list(sem.Instr.instrs)
        self.ctrs = (0,)
        self.ins = list(spec[2])
        self.outs = list(spec[1])
    def __call__(self, examples):
        return []

def envs_and_instrs(path):
    def one_more_from(it):
        acc = []
        for i in it:
            yield acc
            acc = acc + [i]
        yield acc

    instrs = list(ptx.handle_file(path))
    thingy = sem.read_from_parsed(instrs)
    all_envs = zip(thingy, one_more_from(instrs))
    return all_envs

def example_and_code_to_query(example, code):
    meaning = sem.read_from_parsed([code])[-1]
    in_state = z3.And(*(i() == example[0][i] for i in example[0] if i() in meaning[2]))
    out_state = z3.And(*(i() == example[0][i] for i in example[0] if i() in meaning[1]))
    return z3.Implies(z3.And(sem.env_to_query(meaning), in_state), out_state)

def keep_trying(spec, example_gen, code_maker):
    examples = [next(example_gen)]
    curr_code = []
    while True:
        example = examples[-1]
        curr_code = code_maker(examples)
        meaning = sem.read_from_parsed(curr_code)[-1]
        in_state = z3.And(*(i() == example[0][i] for i in example[0] if i() in meaning[2]))
        prog = sem.env_to_query(meaning)
        try:
            examples.append(example_gen.send(z3.And(spec, z3.Not(prog))))
        except StopIteration:
            return curr_code

if __name__ == "__main__":
    eis = list(envs_and_instrs("test.ptx"))
    ex = sem.get_examples(eis[-1][0])
    print(keep_trying(sem.env_to_query(eis[-1][0]), ex, CodeGenerator(eis[-1][0])))
    p1 = list(CodeGenerator.n_p_k(3, 4))
    p2 = list(CodeGenerator.n_p_k(4, 4))
    p3 = list(CodeGenerator.n_p_k(2, 4))
    for i in CodeGenerator.cross_product(p1, p2, p3):
        print(i)
