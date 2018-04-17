import parser as ptx
from pyparsing import ParseException
from functools import reduce
import z3
import struct

def to_z3_obj(arg, typ, ident_t = None):
    id_t_2_z3 = {
        ptx.integer_literal: z3.Int,
        ptx.float_literal: z3.Real,
        ptx.double_literal: z3.Real,
        ptx.predicate_const: z3.Bool
    }
    return {
        ptx.integer_literal: lambda x: int(ptx.integer_literal.parseString(arg)[0][2], 16),
        ptx.float_literal: lambda x: struct.unpack('f', arg)[0],
        ptx.double_literal: lambda x: struct.unpack('d', arg)[0],
        ptx.predicate_const: bool,
        ptx.identifier: lambda x: id_t_2_z3[ident_t](arg)
    }[typ](arg)

class Instr:
    instrs = []
    def __init__(self, parser, call_on_env, argparser):
        self.parser = parser
        self.call_on_env = call_on_env
        self.argparser = argparser
        Instr.instrs.append(self)
    def __call__(self, args, env):
        def proc_arg(parser, arg):
            if parser[1]:
                return to_z3_obj((parser[0] | ptx.identifier).parseString(arg)[0], ptx.identifier, parser)
            elif parser[0] == ptx.identifier:
                return to_z3_obj(parser[0].parseString(arg)[0], ptx.identifier, parser[1])
            return to_z3_obj(parser[0].parseString(arg)[0], parser)
        try:
            z3_objs = list(map(proc_arg, self.argparser[len(args)], args))
        except ParseException:
            return None
        else:
            return self.call_on_env(z3_objs, env)

def upd_1_key(d, upd):
    r = d.copy()
    r.update(upd)
    return r

add = Instr(ptx.add, lambda ag, ev: upd_1_key(ev, {ag[0]: ag[1] + ag[2]}),
        {3: ((ptx.identifier, ptx.integer_literal), (ptx.integer_literal, True), (ptx.integer_literal, True))})
sub = Instr(ptx.add, lambda ag, ev: upd_1_key(ev, {ag[0]: ag[1] - ag[2]}),
        {3: ((ptx.identifier, ptx.integer_literal), (ptx.integer_literal, True), (ptx.integer_literal, True))})

def read_file(path):
    # reduce(
    pass
