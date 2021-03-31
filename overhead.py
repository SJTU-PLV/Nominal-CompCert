import os
import re

# Returns (spec, proof) lines for the given git object
def counts(objs):
    fn = list(objs)
    if len(fn) == 0:
        return (0, 0, 0)

    c = os.popen("git show " + " ".join(fn) + " | coqwc")
    c.readline()
    s = c.readline()
    c.close()
    if s == "":
        return (0, 0, 0)
    else:
        (spec, proof) = map(int, re.split(' +', s)[1:3])
        return (spec, proof, spec+proof)

def stats(fs):
    def summarize(x, y):
        diff = y - x
        if x >= 10:
            return "{0:+4d} ({1:5.0f}%)".format(diff, 100 * diff / x)
        else:
            return "{0:+4d}         ".format(diff)
#        if y > 10:
#            fmt = "{0:4d}/{1:4d} ({2:+6.0f}%)"
#            return fmt.format(y, x, 100 * (y - x) / x)
#        else:
#            return "{0:4d}/{1:4d}          ".format(y, x)
#

    def notnew(s):
        return s[0] != '+'
    def unnew(s):
        return s if notnew(s) else s[1:]

    before = counts(map("origin/compcerto-ref:{0}.v".format, filter(notnew, fs)));
    after = counts(map("HEAD:{0}.v".format, map(unnew, fs)));
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
  ["backend/CSEproof", "backend/CSEdomain", "x86/CombineOpproof"],
  ["backend/Deadcodeproof"],
  #["backend/Unusedglobproof"],
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

all_passes = []
for p in passes:
  all_passes += p

groups = passes + [
  # Semantic model
  ["common/AST",
   #"common/Behaviors",
   #"common/Determinism",
   #"common/Loader",
   "common/Events",
   "common/Globalenvs",
   "common/Linking",
   "common/Smallstep",
   "+common/LanguageInterface"],
  # Horizontal composition
  ["+x86/AsmLinking",
   "+common/SmallstepLinking"],
  # Simulation convention algebra
  ["+common/CallconvAlgebra",
   "+cklr/CKLRAlgebra"],
  # CKLR basics
  ["+cklr/CKLR",
   "+cklr/Extends",
   "+cklr/Inject",
   "+cklr/InjectFootprint",
   "+cklr/VAExtends",
   "+cklr/VAInject"],
  # Parametricity
  ["+cklr/Clightrel",
   "+cklr/Coprel",
   "+cklr/Builtinsrel",
   "+cklr/Eventsrel",
   "+cklr/Mapsrel",
   "+cklr/RTLrel",
   "+cklr/Registersrel",
   "+cklr/Valuesrel",
   "+x86/Asmrel"],
  # Invariants proofs
  ["+common/Invariant",
   "backend/Cminortyping",
   "backend/ValueAnalysis",
   "backend/ValueDomain",
   "backend/RTLtyping",
   "backend/Lineartyping"],
  # Correctness proofs
  all_passes,
  # Calling convention
  ["+driver/CallConv",
   "common/Memory",
   "backend/Conventions",  # not really the right place but where is?
   "driver/Compiler"],
]

for p in groups:
  print(p[0] + ", etc.")
  print("  ", " & ".join(stats(p)))

