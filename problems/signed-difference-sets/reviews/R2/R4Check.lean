import SignedDifferenceSets.Check

/-! Refuter's independent re-check of O6-O11. -/

namespace R4Refuter
open SignedDifferenceSets

def Pn49 : List (ZMod 5 × ZMod 5) := [((0 : ZMod 5), (0 : ZMod 5)), ((1 : ZMod 5), (4 : ZMod 5)), ((2 : ZMod 5), (1 : ZMod 5)), ((3 : ZMod 5), (0 : ZMod 5)), ((3 : ZMod 5), (1 : ZMod 5)), ((3 : ZMod 5), (3 : ZMod 5)), ((4 : ZMod 5), (1 : ZMod 5)), ((4 : ZMod 5), (3 : ZMod 5)), ((4 : ZMod 5), (4 : ZMod 5))]
def Mn49 : List (ZMod 5 × ZMod 5) := [((2 : ZMod 5), (3 : ZMod 5)), ((2 : ZMod 5), (4 : ZMod 5)), ((4 : ZMod 5), (2 : ZMod 5))]
def Dn49 (x : ZMod 5 × ZMod 5) : SignType := if x ∈ Pn49 then 1 else if x ∈ Mn49 then -1 else 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem has_n49 : HasSDS (ZMod 5 × ZMod 5) 12 1 := ⟨Dn49, by decide⟩
#print axioms has_n49

def Pn61 : List (ZMod 3 × ZMod 3 × ZMod 3) := [((0 : ZMod 3), (0 : ZMod 3), (0 : ZMod 3)), ((1 : ZMod 3), (2 : ZMod 3), (0 : ZMod 3)), ((1 : ZMod 3), (2 : ZMod 3), (1 : ZMod 3)), ((2 : ZMod 3), (1 : ZMod 3), (0 : ZMod 3)), ((2 : ZMod 3), (1 : ZMod 3), (2 : ZMod 3)), ((2 : ZMod 3), (2 : ZMod 3), (0 : ZMod 3)), ((2 : ZMod 3), (2 : ZMod 3), (1 : ZMod 3)), ((2 : ZMod 3), (2 : ZMod 3), (2 : ZMod 3))]
def Mn61 : List (ZMod 3 × ZMod 3 × ZMod 3) := [((1 : ZMod 3), (2 : ZMod 3), (2 : ZMod 3)), ((2 : ZMod 3), (1 : ZMod 3), (1 : ZMod 3))]
def Dn61 (x : ZMod 3 × ZMod 3 × ZMod 3) : SignType := if x ∈ Pn61 then 1 else if x ∈ Mn61 then -1 else 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem has_n61 : HasSDS (ZMod 3 × ZMod 3 × ZMod 3) 10 1 := ⟨Dn61, by decide⟩
#print axioms has_n61

def Pn62 : List (ZMod 3 × ZMod 9) := [((0 : ZMod 3), (0 : ZMod 9)), ((1 : ZMod 3), (5 : ZMod 9)), ((1 : ZMod 3), (6 : ZMod 9)), ((2 : ZMod 3), (1 : ZMod 9)), ((2 : ZMod 3), (3 : ZMod 9)), ((2 : ZMod 3), (4 : ZMod 9)), ((2 : ZMod 3), (5 : ZMod 9)), ((2 : ZMod 3), (7 : ZMod 9))]
def Mn62 : List (ZMod 3 × ZMod 9) := [((1 : ZMod 3), (8 : ZMod 9)), ((2 : ZMod 3), (2 : ZMod 9))]
def Dn62 (x : ZMod 3 × ZMod 9) : SignType := if x ∈ Pn62 then 1 else if x ∈ Mn62 then -1 else 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem has_n62 : HasSDS (ZMod 3 × ZMod 9) 10 1 := ⟨Dn62, by decide⟩
#print axioms has_n62

def Pn67 : List (ZMod 3 × ZMod 3 × ZMod 3) := [((0 : ZMod 3), (0 : ZMod 3), (0 : ZMod 3)), ((0 : ZMod 3), (2 : ZMod 3), (2 : ZMod 3)), ((1 : ZMod 3), (1 : ZMod 3), (1 : ZMod 3)), ((1 : ZMod 3), (1 : ZMod 3), (2 : ZMod 3)), ((1 : ZMod 3), (2 : ZMod 3), (0 : ZMod 3)), ((1 : ZMod 3), (2 : ZMod 3), (1 : ZMod 3)), ((1 : ZMod 3), (2 : ZMod 3), (2 : ZMod 3)), ((2 : ZMod 3), (0 : ZMod 3), (1 : ZMod 3)), ((2 : ZMod 3), (0 : ZMod 3), (2 : ZMod 3)), ((2 : ZMod 3), (1 : ZMod 3), (1 : ZMod 3)), ((2 : ZMod 3), (1 : ZMod 3), (2 : ZMod 3)), ((2 : ZMod 3), (2 : ZMod 3), (0 : ZMod 3)), ((2 : ZMod 3), (2 : ZMod 3), (1 : ZMod 3))]
def Mn67 : List (ZMod 3 × ZMod 3 × ZMod 3) := [((2 : ZMod 3), (1 : ZMod 3), (0 : ZMod 3))]
def Dn67 (x : ZMod 3 × ZMod 3 × ZMod 3) : SignType := if x ∈ Pn67 then 1 else if x ∈ Mn67 then -1 else 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem has_n67 : HasSDS (ZMod 3 × ZMod 3 × ZMod 3) 14 5 := ⟨Dn67, by decide⟩
#print axioms has_n67

def Pn68 : List (ZMod 3 × ZMod 9) := [((0 : ZMod 3), (0 : ZMod 9)), ((0 : ZMod 3), (8 : ZMod 9)), ((1 : ZMod 3), (1 : ZMod 9)), ((1 : ZMod 3), (4 : ZMod 9)), ((1 : ZMod 3), (5 : ZMod 9)), ((1 : ZMod 3), (6 : ZMod 9)), ((1 : ZMod 3), (7 : ZMod 9)), ((2 : ZMod 3), (1 : ZMod 9)), ((2 : ZMod 3), (3 : ZMod 9)), ((2 : ZMod 3), (4 : ZMod 9)), ((2 : ZMod 3), (5 : ZMod 9)), ((2 : ZMod 3), (7 : ZMod 9)), ((2 : ZMod 3), (8 : ZMod 9))]
def Mn68 : List (ZMod 3 × ZMod 9) := [((2 : ZMod 3), (2 : ZMod 9))]
def Dn68 (x : ZMod 3 × ZMod 9) : SignType := if x ∈ Pn68 then 1 else if x ∈ Mn68 then -1 else 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem has_n68 : HasSDS (ZMod 3 × ZMod 9) 14 5 := ⟨Dn68, by decide⟩
#print axioms has_n68

def Pn73 : List (ZMod 3 × ZMod 3 × ZMod 3) := [((0 : ZMod 3), (0 : ZMod 3), (0 : ZMod 3)), ((0 : ZMod 3), (2 : ZMod 3), (1 : ZMod 3)), ((0 : ZMod 3), (2 : ZMod 3), (2 : ZMod 3)), ((1 : ZMod 3), (0 : ZMod 3), (2 : ZMod 3)), ((1 : ZMod 3), (1 : ZMod 3), (0 : ZMod 3)), ((1 : ZMod 3), (1 : ZMod 3), (1 : ZMod 3)), ((1 : ZMod 3), (1 : ZMod 3), (2 : ZMod 3)), ((1 : ZMod 3), (2 : ZMod 3), (0 : ZMod 3)), ((1 : ZMod 3), (2 : ZMod 3), (1 : ZMod 3)), ((2 : ZMod 3), (0 : ZMod 3), (0 : ZMod 3)), ((2 : ZMod 3), (0 : ZMod 3), (2 : ZMod 3)), ((2 : ZMod 3), (1 : ZMod 3), (0 : ZMod 3)), ((2 : ZMod 3), (1 : ZMod 3), (2 : ZMod 3)), ((2 : ZMod 3), (2 : ZMod 3), (0 : ZMod 3)), ((2 : ZMod 3), (2 : ZMod 3), (1 : ZMod 3)), ((2 : ZMod 3), (2 : ZMod 3), (2 : ZMod 3))]
def Mn73 : List (ZMod 3 × ZMod 3 × ZMod 3) := [((2 : ZMod 3), (1 : ZMod 3), (1 : ZMod 3))]
def Dn73 (x : ZMod 3 × ZMod 3 × ZMod 3) : SignType := if x ∈ Pn73 then 1 else if x ∈ Mn73 then -1 else 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem has_n73 : HasSDS (ZMod 3 × ZMod 3 × ZMod 3) 17 8 := ⟨Dn73, by decide⟩
#print axioms has_n73

end R4Refuter
