import semantics as sem
import z3
import parser as ptx
from functools import reduce
from itertools import permutations

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

        if len(its) > 1:
            return reduce(helper, its)
        else:
            return ((i, ) for i in its[0])
    @staticmethod
    def check_input_vec(input_vec, output, num_out_vars, num_in_vars, loc):
        for var in input_vec:
            if var < num_in_vars:
                continue
            if output[var - num_in_vars] < num_out_vars or var - num_in_vars >= loc:
                return False
        return True
    @staticmethod
    def check_output(output_vec, num_out_vars):
        return set(output_vec) >= set(range(num_out_vars))
    @staticmethod
    def make_n_instrs(n, instrs, n_outs, n_ins):
        inst_gen = RememberingIter(CodeGenerator.n_p_k(len(instrs), n))
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
                return str(lst[idx])
            return els

        def do_line_i(i):
            instr = instrs[vec[0][i]]
            out = if_in_list_else(vec[1][i], outs, 't' + str(i))
            inps = map(lambda x: if_in_list_else(x, ins, 't' + str(x - len(ins))), vec[2][i])
            return [instr, out] + list(inps) + [';']

        return [do_line_i(i) for i in range(len(vec[0]))]
    @staticmethod
    def mk_fmt_instr(n, instrs, ins, outs):
        return map(lambda v: CodeGenerator.format_instrs(v, instrs, ins, outs),
                CodeGenerator.make_n_instrs(n, instrs, len(outs), len(ins)))
    @staticmethod
    def generate_identities(ins, outs):
        for i in ins:
            for o in outs:
                for instr in sem.Instr.instrs:
                    if 'add' in instr:
                        yield [[instr, str(o), str(i), '0', ';']]

    def __init__(self, spec, init_code = []):
        self.using_examples = False
        self.ins = list(spec[2])
        self.instrs = list(filter(lambda i: int(i[-2:]) == self.ins[0].size(), sem.Instr.instrs))
        self.outs = list(spec[1])
        self.len = 0
        self.curr_gen = CodeGenerator.generate_identities(self.ins, self.outs)
        self.init_code = init_code
    def __call__(self, examples):
        try:
            return self.init_code + next(self.curr_gen)
        except StopIteration:
            self.len = max(self.len + 1, len(self.outs))
            self.curr_gen = CodeGenerator.mk_fmt_instr(self.len, self.instrs, self.ins, self.outs)
            print('cgl', self.len)
            #I'll be damned if this ever stops iteration.
            return self.init_code + next(self.curr_gen)
    def __len__(self):
        return self.len

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

#BRUTE FORCE - slow, "works"
def keep_trying(spec, example_gen, code_maker, max_len):
    examples = [next(example_gen)]
    curr_code = []
    while len(code_maker) <= max_len:
        example = examples[-1]
        curr_code = code_maker(examples)
        if not curr_code:
            return False
        try:
            meaning = sem.read_from_parsed(curr_code)
            meaning = meaning[-1]
            in_state = z3.And(*(i() == example[0][i] for i in example[0] if i() in meaning[2]))
            prog = sem.env_to_query(meaning)
            # print('cc', curr_code)
            # print('specs', spec, 'XOR', prog)
            examples.append(example_gen.send((z3.Xor(spec, prog), code_maker.using_examples)))
        except StopIteration:
            #this means that the example generator couldn't make an example
            #the code matches the spec
            return curr_code
        except z3.z3types.Z3Exception:
            #LOL - I'm too dumb for strongly typing
            continue
    return False

def output_by_output(spec_env, max_len):
    tot_outs = len(spec_env[1])
    prg = []
    min_prg = []
    for outs in permutations(spec_env[1]):
        curr_spec = ({}, set(), spec_env[2], spec_env[3] - spec_env[1])
        prg = []
        for n, out in enumerate(outs):
            curr_spec = sem.union_envs(curr_spec, ({out: spec_env[0][out]}, {out}, {out} | spec_env[2]))
            prg_spec = sem.read_from_parsed(prg)[-1]
            cg_spec = sem.union_envs(curr_spec, ({}, set(), prg_spec[3], prg_spec[3]))
            cg_spec = (cg_spec[0], {out}, cg_spec[2], cg_spec[3])
            cg = CodeGenerator(cg_spec, prg)
            prg = keep_trying(sem.env_to_query(curr_spec), sem.get_examples(curr_spec), cg, max_len - (tot_outs - n) + 1)
            if not prg:
                break
        else:
            if len(prg) < len(min_prg) or len(min_prg) == 0:
                min_prg = prg
    return min_prg

def get_out_equiv_classes(spec_env, max_len):
    eq_classes = {o: {o} for o in spec_env[1]}
    seen = set()
    for o1 in spec_env[1]:
        for o2 in spec_env[1]:
            if o1 == o2 or {o1, o2} <= seen:
                continue

            #gen o1 then o2
            curr_spec = ({}, set(), spec_env[2], spec_env[3] - spec_env[1])
            curr_spec = sem.union_envs(curr_spec, ({o1: spec_env[0][o1]}, {o1}, {o1} | spec_env[2]))
            cg_spec = (curr_spec[0], {o1}, curr_spec[2], curr_spec[3])
            cg = CodeGenerator(cg_spec)
            prg1 = keep_trying(sem.env_to_query(curr_spec), sem.get_examples(curr_spec), cg, max_len - 1)

            curr_spec = sem.union_envs(curr_spec, ({o2: spec_env[0][o2]}, {o2}, {o2} | spec_env[2]))
            prg_spec = sem.read_from_parsed(prg1)[-1]
            cg_spec = sem.union_envs(curr_spec, ({}, set(), prg_spec[3], prg_spec[3]))
            cg_spec = (cg_spec[0], {o2}, cg_spec[2], cg_spec[3])
            cg = CodeGenerator(cg_spec, prg1)
            prg2 = keep_trying(sem.env_to_query(curr_spec), sem.get_examples(curr_spec), cg, max_len - len(prg1))

            #o2 then o1
            curr_spec = ({}, set(), spec_env[2], spec_env[3] - spec_env[1])
            curr_spec = sem.union_envs(curr_spec, ({o2: spec_env[0][o2]}, {o2}, {o2} | spec_env[2]))
            cg_spec = (curr_spec[0], {o2}, curr_spec[2], curr_spec[3])
            cg = CodeGenerator(cg_spec)
            prg3 = keep_trying(sem.env_to_query(curr_spec), sem.get_examples(curr_spec), cg, max_len - 1)

            curr_spec = sem.union_envs(curr_spec, ({o1: spec_env[0][o1]}, {o1}, {o1} | spec_env[2]))
            prg_spec = sem.read_from_parsed(prg3)[-1]
            cg_spec = sem.union_envs(curr_spec, ({}, set(), prg_spec[3], prg_spec[3]))
            cg_spec = (cg_spec[0], {o1}, cg_spec[2], cg_spec[3])
            cg = CodeGenerator(cg_spec, prg3)
            prg4 = keep_trying(sem.env_to_query(curr_spec), sem.get_examples(curr_spec), cg, max_len - len(prg3))

            if len(prg4) != len(prg2):
                eq_classes[o2].add(o1)
                eq_classes[o1].add(o2)
            seen.add(o1)
            seen.add(o2)
    return eq_classes

def use_equiv_outs(spec_env, max_len):
    classes = get_out_equiv_classes(spec_env, max_len)
    fin_prg = []
    seen = set()
    for i in classes:
        if i in seen:
            continue

        seen |= classes[i]
        class_spec = ({o: spec_env[0][o] for o in classes[i]}, classes[i], spec_env[2], spec_env[3])
        prg = output_by_output(class_spec, max_len)
        if not prg:
            return False
        fin_prg += prg
    return fin_prg

def pretty_print(code):
    return "FINAL OUTPUT: \n" + '\n'.join(' '.join(i for i in j) for j in code)

if __name__ == "__main__":
    from sys import argv
    eis = list(envs_and_instrs(argv[1]))
    print(pretty_print(use_equiv_outs(eis[-1][0], len(eis) - 1)))
