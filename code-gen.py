import semantics as sem
import z3
import parser as ptx

class CodeGenerator:
    def __init__(self, spec):
        self.known_code = ["mul.hi.u32 test, e, 2;", "sub.u32 b, e, 77;", "div.u32 f, b, 0xa9;"]
    def __call__(self, examples):
        code = list(map(lambda l: ptx.statement.parseString(l), self.known_code))
        return code

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
    print(keep_trying(sem.env_to_query(eis[-1][0]), ex, CodeGenerator(eis[-1])))
