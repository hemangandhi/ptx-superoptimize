import semantics as sem
import z3
import parser as ptx


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
    meaning = sem.read_from_parsed(code)[-1]
    in_state = z3.And(*(i() == v[i] for i in example[0] if i() in meaning[2]))
    out_state = z3.And(*(i() == v[i] for i in example[0] if i() in meaning[1]))
    return z3.Implies(z3.And(sem.env_to_query(meaning), in_state), out_state)

if __name__ == "__main__":
    eis = list(envs_and_instrs("test.ptx"))
    for i in eis:
        print(i)

    ex = sem.get_examples(eis[-1][0])
    code = ptx.statement.parseString("mul.hi.u32 e, f, test")
