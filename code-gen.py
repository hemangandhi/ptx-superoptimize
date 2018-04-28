import semantics as sem
import z3
import parser as ptx
from functools import reduce

class RememberingIter:
    def __init__(self, it):
        self.it = it
        self.acc = []
        self.stopped = False
    def __iter__(self):
        if not self.stopped:
            return self
        return iter(self.acc)
    def __next__(self):
        try:
            n = next(self.it)
            self.acc.append(n)
            return n
        except StopIteration:
            self.stopped = True
            raise StopIteration

class CodeGenerator:
    @staticmethod
    def n_p_k(n, k):
        if k == 1:
            return map(lambda x: [x], range(n))
        return ([i] + j for j in CodeGenerator.n_p_k(n, k - 1) for i in range(n))
    @staticmethod
    def cross_product(*its):
        def helper(l, r):
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
    @staticmethod
    def check_input_vec(input_vec, output, num_out_vars, num_in_vars, loc):
        for var in input_vec:
            if var < num_in_vars:
                continue
            if output[var - num_in_vars] < num_out_vars or var >= loc:
                return False
        return True
    @staticmethod
    def check_output(output_vec, num_out_vars):
        return set(output_vec) >= set(range(num_out_vars))
    @staticmethod
    def make_n_instrs(n, instrs, n_outs, n_ins):
        inst_gen = CodeGenerator.n_p_k(len(instrs), n)
        out_gen = RememberingIter(filter(lambda o: CodeGenerator.check_output(o, n_outs), CodeGenerator.n_p_k(n_outs + 1, n)))
        for insts in inst_gen :
            for outs in out_gen:
                p_ks = (filter(lambda i: CodeGenerator.check_input_vec(i, outs, n_outs, n_ins, idx), CodeGenerator.n_p_k(n + n_ins, agc - 1))\
                        for idx in range(n) for agc in sem.Instr.instrs[instrs[insts[idx]]].argparser)
                yield from ((insts, outs, i) for i in CodeGenerator.cross_product(*map(list, p_ks)))
    @staticmethod
    def format_instrs(vec, instrs, ins, outs):
        def if_in_list_else(idx, lst, els):
            if 0 <= idx < len(lst):
                return lst[idx]
            return els

        def do_line_i(i):
            instr = instrs[vec[0][i]]
            out = if_in_list_else(vec[1][i], outs, 't' + str(i))
            inps = map(lambda x: if_in_list_else(x, ins, 't' + str(i)), vec[2][i])
            return [instr, out] + list(inps)

        return [do_line_i(i) for i in range(len(vec[0]))]
    @staticmethod
    def mk_fmt_instr(n, instrs, ins, outs):
        return map(lambda v: CodeGenerator.format_instrs(v, instrs, ins, outs),
                CodeGenerator.make_n_instrs(n, instrs, len(outs), len(ins)))

    def __init__(self, spec):
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
        if not curr_code:
            return False
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
    for i in CodeGenerator.mk_fmt_instr(2, list(sem.Instr.instrs), ['a', 'b'], ['c']):
        print(i)

