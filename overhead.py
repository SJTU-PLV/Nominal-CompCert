import os
import re

# Returns (spec, proof) lines for the given git object
def counts(objs):
    c = os.popen("git show " + " ".join(objs) + " | coqwc")
    c.readline()
    (spec, proof) = map(int, re.split(' +', c.readline())[1:3])
    c.close()
    return (spec, proof, spec+proof)

def stats(fs):
    def summarize(x, y):
        diff = y - x
        if x >= 10:
            return "{0:+4d} ({1:5.0f}%)".format(diff, 100 * diff / x)
        else:
            return "{0:+4d}".format(diff)
#        if y > 10:
#            fmt = "{0:4d}/{1:4d} ({2:+6.0f}%)"
#            return fmt.format(y, x, 100 * (y - x) / x)
#        else:
#            return "{0:4d}/{1:4d}          ".format(y, x)
#
    before = counts(map("v3.5:{0}.v".format, fs));
    after = counts(map("compcerto:{0}.v".format, fs));
    return list(map(summarize, before, after));

passes = [
  ["cfrontend/Clight"],
  ["cfrontend/SimplLocalsproof"],
  ["cfrontend/Cshmgenproof"],
  ["cfrontend/Csharpminor"],
  ["cfrontend/Cminorgenproof"],
  ["backend/Cminor"],
  ["backend/Selectionproof",
   "x86/SelectOpproof",
   "x86/SelectLongproof",
   "backend/SelectDivproof",
   "backend/SplitLongproof"],
  ["backend/CminorSel"],
  ["backend/RTLgenspec",
   "backend/RTLgenproof"],
  ["backend/RTL"],
  ["backend/Tailcallproof"],
  ["backend/Inliningspec",
   "backend/Inliningproof"],
  ["backend/Renumberproof"],
  ["backend/Constpropproof", "x86/ConstpropOpproof"],
  ["backend/CSEproof", "x86/CombineOpproof"],
  ["backend/Deadcodeproof"],
  ["backend/Unusedglobproof"],
  ["backend/Allocproof"],
  ["backend/LTL"],
  ["backend/Tunnelingproof"],
  ["backend/Linearizeproof"],
  ["backend/Linear"],
  ["backend/CleanupLabelsproof"],
  ["backend/Debugvarproof"],
  ["backend/Stackingproof", "common/Separation"],
  ["backend/Mach"],
  ["backend/Asmgenproof0", "x86/Asmgenproof1", "x86/Asmgenproof"],
  ["x86/Asm"],
]

for p in passes:
  print(p[0] + ", etc.")
  print("  ", " & ".join(stats(p)))




