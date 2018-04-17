import parser as ptx
from pyparsing import ParseException
from functools import reduce
import z3
import struct

def to_z3_obj(arg, typ, ident_t = None):
    def intern_int(x):
        if len(x) == 3:
            return int(x[2], 16)
        elif len(x) == 2:
            return int(x[1], 8)
        else:
            return int(x[0])
    id_t_2_z3 = {
        ptx.integer_literal: z3.Int,
        ptx.float_literal: z3.Real,
        ptx.double_literal: z3.Real,
        ptx.predicate_const: z3.Bool
    }
    return {
        ptx.integer_literal: intern_int,
        ptx.float_literal: lambda x: struct.unpack('f', arg)[0],
        ptx.double_literal: lambda x: struct.unpack('d', arg)[0],
        ptx.predicate_const: bool,
        ptx.identifier: lambda x: id_t_2_z3[ident_t](''.join(x))
    }[typ](arg)

class Instr:
    instrs = dict()
    def __init__(self, name, parser, call_on_env, argparser):
        self.parser = parser
        self.call_on_env = call_on_env
        self.argparser = argparser
        Instr.instrs[name] = self
    def __call__(self, args, env):
        def proc_arg(parser, arg):
            arg = arg[0]
            if parser[0] == ptx.identifier:
                return to_z3_obj(parser[0].parseString(arg)[0], ptx.identifier, parser[1])
            elif parser[1]:
                return to_z3_obj((parser[0] | ptx.identifier).parseString(arg)[0], ptx.identifier, parser[0])
            return to_z3_obj(parser[0].parseString(arg)[0], parser)
        try:
            z3_objs = list(map(proc_arg, self.argparser[len(args)], args))
        except ParseException:
            return None
        else:
            return self.call_on_env(z3_objs, env)

def dict_with_upd(d, upd):
    r = d.copy()
    r.update(upd)
    return r

add = Instr('add', ptx.add, lambda ag, ev: dict_with_upd(ev, {ag[0]: ag[1] + ag[2]}),
        {3: ((ptx.identifier, ptx.integer_literal), (ptx.integer_literal, True), (ptx.integer_literal, True))})
sub = Instr('sub', ptx.sub, lambda ag, ev: dict_with_upd(ev, {ag[0]: ag[1] - ag[2]}),
        {3: ((ptx.identifier, ptx.integer_literal), (ptx.integer_literal, True), (ptx.integer_literal, True))})
mul = Instr('mul', ptx.sub, lambda ag, ev: dict_with_upd(ev, {ag[0]: ag[1] * ag[2]}),
        {3: ((ptx.identifier, ptx.integer_literal), (ptx.integer_literal, True), (ptx.integer_literal, True))})
div = Instr('div', ptx.sub, lambda ag, ev: dict_with_upd(ev, {ag[0]: ag[1] / ag[2]}),
        {3: ((ptx.identifier, ptx.integer_literal), (ptx.integer_literal, True), (ptx.integer_literal, True))})

def read_file(path):
    def process_instr(env, instr):
        instr_p, idx = ptx.get_instr(instr)
        instr_nm = instr_p.split('.')[0]
        fnd = Instr.instrs.get(instr_nm, None)
        if fnd is None: return env
        return fnd(instr[idx + 1:len(instr)-1], env)

    return reduce(process_instr, ptx.handle_file(path), {})

def env_to_query(env):
    return z3.And(*(i == env[i] for i in env))

if __name__ == "__main__":
    print(env_to_query(read_file('test.ptx')))
