# Build R7Check.lean: source copies of SylowTwo, SylowTwoRows, N79, N80 (headers stripped), axioms, key checks.
import re, csv, math
P = "../../../"
LD = P + "lean/SignedDifferenceSets/"
def body(name, rename=None):
    out = []
    for line in open(LD + name, encoding="utf-8").read().split("\n"):
        if line.strip() in ("module", "@[expose] public section") or line.startswith("public import"):
            continue
        if rename: line = line.replace(rename[0], rename[1])
        out.append(line)
    return "\n".join(out)
inst = {}
with open(P + "instances.csv", newline="", encoding="utf-8") as f:
    for r in csv.DictReader(f): inst[r["id"]] = r["key"]
KEY = re.compile(r"^SDS\((-?\d+),(-?\d+),(-?\d+),\[([\d,]*)\]\)$")
src = open(LD + "SylowTwoRows.lean", encoding="utf-8").read()
parts = re.split(r"def sylowTwoRows(\d+) : List", src)
keys = {}
for j in range(1, len(parts), 2):
    ids = ["N" + x for x in re.findall(r"\(⟨(\d+), \[", parts[j + 1].split("theorem")[0])]
    lst = []
    for i in ids:
        g = KEY.match(inst[i]); ms = g[4].split(",")
        lst.append(f"({i[1:]}, [{', '.join(ms)}], {g[2]}, ({g[3]} : ℤ))")
    keys[int(parts[j])] = lst
o = ["import SignedDifferenceSets.SylowCheck", "import SignedDifferenceSets.Answer.N79",
     "import SignedDifferenceSets.Answer.N80", ""]
o.append(body("SylowTwo.lean"))
o.append(body("SylowTwoRows.lean"))
o.append(body("Answer/N79.lean", ("SignedDifferenceSets.Answer.N79", "SignedDifferenceSets.R7.N79")))
o.append(body("Answer/N80.lean", ("SignedDifferenceSets.Answer.N80", "SignedDifferenceSets.R7.N80")))
o.append("""
open SignedDifferenceSets
#print axioms SignedDifferenceSets.not_hasSDS_of_sylow_two
#print axioms SignedDifferenceSets.SyTwoCert.not_hasSDS
#print axioms SignedDifferenceSets.sylowTwoRows1_not_hasSDS
#print axioms SignedDifferenceSets.sylowTwoRows2_not_hasSDS
#print axioms SignedDifferenceSets.sylowTwoRows1_kill
#print axioms SignedDifferenceSets.sylowTwoRows2_kill
#print axioms SignedDifferenceSets.Answer.N79.not_hasSDS
#print axioms SignedDifferenceSets.Answer.N80.not_hasSDS
#print axioms SignedDifferenceSets.R7.N79.not_hasSDS
#print axioms SignedDifferenceSets.R7.N80.not_hasSDS
#check @SignedDifferenceSets.not_hasSDS_of_sylow_two
#check @SignedDifferenceSets.Answer.N79.not_hasSDS
#check @SignedDifferenceSets.Answer.N80.not_hasSDS
""")
for c, lst in keys.items():
    o.append(f"set_option maxRecDepth 100000 in\nexample : sylowTwoRows{c}.map (fun x => (x.1.id, x.1.ms, x.1.k, x.1.lam)) =\n  [" + ",\n  ".join(lst) + "] := by decide +kernel\n")
o.append("""-- plain types
example : ¬ HasSDS (ZMod 120) 18 2 :=
  sylowTwoRows1_not_hasSDS (x := (⟨2993, [120], 18, 2⟩, ⟨4, 4, 2, 3, 16, [8]⟩)) (by decide +kernel) inferInstance
example : ¬ HasSDS (ZMod 4 × ZMod 120) 392 136 :=
  sylowTwoRows2_not_hasSDS (x := (⟨65026, [4, 120], 392, 136⟩, ⟨4, 16, 4, 5, 256, [4, 8]⟩)) (by decide +kernel) inferInstance
example : ¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 112) 276 20 :=
  sylowTwoRows1_not_hasSDS (x := (⟨56542, [2, 2, 112], 276, 20⟩, ⟨8, 16, 4, 6, 96, [2, 2, 16]⟩)) (by decide +kernel) inferInstance
example : ¬ HasSDS (ZMod 3 × ZMod 120) 150 6 :=
  sylowTwoRows1_not_hasSDS (x := (⟨35265, [3, 120], 150, 6⟩, ⟨4, 12, 2, 3, 48, [1, 8]⟩)) (by decide +kernel) inferInstance
-- controls: each must be decided false
-- O13 (32,20,4) on C2 x C16, s = 12: 8 does not divide 12
example : ¬ (SyTwoCert.Kills ⟨0, [2, 16], 20, 4⟩ ⟨8, 4, 2, 5, 12, [2, 16]⟩) := by decide +kernel
-- N2993 with w one too small / too large
example : ¬ (SyTwoCert.Kills ⟨2993, [120], 18, 2⟩ ⟨4, 4, 1, 3, 16, [8]⟩) := by decide +kernel
example : ¬ (SyTwoCert.Kills ⟨2993, [120], 18, 2⟩ ⟨4, 4, 3, 3, 16, [8]⟩) := by decide +kernel
-- N2993 with k changed to 19, r = 3 (not in maPairs), non-2-power factor 24
example : ¬ (SyTwoCert.Kills ⟨2993, [120], 19, 2⟩ ⟨4, 4, 2, 3, 16, [8]⟩) := by decide +kernel
example : ¬ (SyTwoCert.Kills ⟨2993, [120], 18, 2⟩ ⟨3, 4, 2, 3, 16, [8]⟩) := by decide +kernel
example : ¬ (SyTwoCert.Kills ⟨2993, [120], 18, 2⟩ ⟨12, 4, 2, 3, 16, [24]⟩) := by decide +kernel
-- w = t: N2993 cert with t claimed 2 but ds [8]
example : ¬ (SyTwoCert.Kills ⟨2993, [120], 18, 2⟩ ⟨4, 4, 2, 2, 16, [8]⟩) := by decide +kernel
""")
open("R7Check.lean", "w", encoding="utf-8").write("\n".join(o))
print("written", sum(len(v) for v in keys.values()))
