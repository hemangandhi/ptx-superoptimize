import semantics as sem
import z3

def get_examples(path):
    s = z3.Solver()
    ev = sem.read_file(path)
    s.add(sem.env_to_query(ev))
    while s.check() == z3.sat:
        v = s.model()
        yield v, ev[1], ev[2]
        s.add(z3.Or(*(i() != v[i] for i in v)))

if __name__ == "__main__":
    print('\n'.join(str(i[0]) for i in zip(get_examples("test.ptx"), range(1))))
