import parser as ptx
from pyparsing import ParseException
from functools import reduce
import z3
import struct

def to_z3_obj(arg, typ, ident_t = None, bitlen = 32):
    def intern_int(x):
        if len(x) == 3:
            return z3.IntVal(int(x[2], 16))
        elif len(x) == 2:
            return z3.IntVal(int(x[1], 8))
        else:
            return z3.IntVal(int(x[0]))

    id_t_2_z3 = {
        ptx.integer_literal: lambda x: z3.BitVec(x, bitlen),
        ptx.float_literal: z3.Real,
        ptx.double_literal: z3.Real,
        ptx.predicate_const: z3.Bool
    }
    return {
        ptx.integer_literal: intern_int,
        ptx.float_literal: lambda x: z3.RealVal(struct.unpack('f', x)[0]),
        ptx.double_literal: lambda x: z3.RealVal(struct.unpack('d', x)[0]),
        ptx.predicate_const: lambda x: z3.BoolVal(bool(x)),
        ptx.identifier: lambda x: id_t_2_z3[ident_t](''.join(x))
    }[typ](arg)

class Instr:
    instrs = dict()
    def __init__(self, name, parser, call_on_env, argparser, size=32):
        self.parser = parser
        self.call_on_env = call_on_env
        self.argparser = argparser
        self.size = size
        Instr.instrs[name] = self
    def __call__(self, args, env):
        def proc_arg(parser, arg):
            arg = arg[0]
            if parser[0] == ptx.identifier:
                return to_z3_obj(parser[0].parseString(arg)[0], ptx.identifier, parser[1], self.size)
            elif parser[1]:
                try:
                    return to_z3_obj(parser[0].parseString(arg)[0], parser[0], bitlen=self.size)
                except ParseException:
                    return to_z3_obj((parser[0] | ptx.identifier).parseString(arg)[0], ptx.identifier, parser[0], self.size)
            return to_z3_obj(parser[0].parseString(arg)[0], parser, bitlen=self.size)
        try:
            z3_objs = list(map(proc_arg, self.argparser[len(args)], args))
        except ParseException:
            return None
        else:
            return self.call_on_env(z3_objs, env)

def mk_for_all_types(prefix, parser, call_on_env, argparser, types = ptx.types):
    for i in ptx.all_concats([prefix], types):
        Instr(i, parser, call_on_env, argparser, int(i[-2:]))

def dict_with_upd(d, upd):
    r = d.copy()
    r.update(upd)
    return r

mk_for_all_types('add', ptx.add, lambda ag, ev: dict_with_upd(ev, {ag[0]: ev.get(ag[1], ag[1]) + ev.get(ag[2], ag[2])}),
        {3: ((ptx.identifier, ptx.integer_literal), (ptx.integer_literal, True), (ptx.integer_literal, True))})
mk_for_all_types('sub', ptx.sub, lambda ag, ev: dict_with_upd(ev, {ag[0]: ev.get(ag[1], ag[1]) - ev.get(ag[2], ag[2])}),
        {3: ((ptx.identifier, ptx.integer_literal), (ptx.integer_literal, True), (ptx.integer_literal, True))})
mk_for_all_types('mul.hi', ptx.mul, lambda ag, ev: dict_with_upd(ev, {ag[0]: z3.Extract(63, 32, z3.Concat(z3.BitVecVal(0, 32), ev.get(ag[1], ag[1])) * z3.Concat(z3.BitVecVal(0, 32), ev.get(ag[2], ag[2])))}),
        {3: ((ptx.identifier, ptx.integer_literal), (ptx.integer_literal, True), (ptx.integer_literal, True))})
mk_for_all_types('mul.lo', ptx.mul, lambda ag, ev: dict_with_upd(ev, {ag[0]: z3.Extract(31, 0, z3.Concat(z3.BitVecVal(0, 32), ev.get(ag[1], ag[1])) * z3.Concat(z3.BitVecVal(0, 32), ev.get(ag[2], ag[2])))}),
        {3: ((ptx.identifier, ptx.integer_literal), (ptx.integer_literal, True), (ptx.integer_literal, True))})
mk_for_all_types('mul.wide', ptx.mul, lambda ag, ev: dict_with_upd(ev, {ag[0]: z3.Extract(31, 0, z3.Concat(z3.BitVecVal(0, 32), ev.get(ag[1], ag[1])) * z3.Concat(z3.BitVecVal(0, 32), ev.get(ag[2], ag[2])))}),
        {3: ((ptx.identifier, ptx.integer_literal), (ptx.integer_literal, True), (ptx.integer_literal, True))}, types = [i for i in ptx.types if '64' not in i])
mk_for_all_types('div', ptx.div, lambda ag, ev: dict_with_upd(ev, {ag[0]: ev.get(ag[1], ag[1]) / ev.get(ag[2], ag[2])}),
        {3: ((ptx.identifier, ptx.integer_literal), (ptx.integer_literal, True), (ptx.integer_literal, True))})

def read_file(path):
    def process_instr(env, instr):
        instr_p, idx = ptx.get_instr(instr)
        fnd = Instr.instrs.get(instr_p, None)
        if fnd is None: return env
        return fnd(instr[idx + 1:len(instr)-1], env)

    return reduce(process_instr, ptx.handle_file(path), {})

def env_to_query(env):
    return z3.And(*(i == env[i] for i in env))

if __name__ == "__main__":
    print(env_to_query(read_file('test.ptx')))
