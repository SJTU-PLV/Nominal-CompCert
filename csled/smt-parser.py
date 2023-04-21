from z3 import *

error = False


def byte_seq_to(x, i):
    return LShR(x, 120 - i * 8)


def interp_bp(s, x, bps):
    for (rel, mask, value) in bps:
        if rel == 0:
            s.assert_exprs(x & mask != value)
        else:
            s.assert_exprs(x & mask == value)


def verify_class(contrs):
    s = Solver()

    size = len(contrs)
    for i in range(0, size):
        for k in range(i, size):
            if i != k:
                s.reset()
                x = BitVec('x', 120)
                interp_bp(s, x, contrs[i])
                interp_bp(s, x, contrs[k])
                sat = s.check()
                if sat.r != -1:
                    print("Error!")
                    print(contrs[i])
                    print(contrs[k])
                    print(s.model())
                    global error
                    error = True


if __name__ == '__main__':
    print("Start Solving Proof Conditions with Z3....")
    klasses = []
    current_klass_bps = []
    current_constr_bps = []
    relation = None
    mask = None
    value = None
    with open('generated/bp_in_smt.txt') as f:
        for line in f:
            if line[0] == "+":
                if current_klass_bps:
                    klasses.append(current_klass_bps)
                    current_klass_bps = []
            elif line[0] == '*':
                if relation is not None:
                    current_constr_bps.append((relation, mask, value))
                    relation = None
                    mask = None
                    value = None
            elif line[0] == '-':
                if current_constr_bps:
                    current_klass_bps.append(current_constr_bps)
                    current_constr_bps = []
            elif line[0] == 'M':
                mask = int(line[1:], 2)
            elif line[0] == 'V':
                value = int(line[1:], 2)
            elif line[0:2] == 'NE':
                relation = 0
            elif line[0:2] == 'EQ':
                relation = 1
    for k in klasses:
        verify_class(k)

    if not error:
        print("Success!")
    else:
        print("This spec is not well-formed")
