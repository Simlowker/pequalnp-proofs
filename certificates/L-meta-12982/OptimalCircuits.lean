import Mathlib
import PEqualNP.Outside.L_meta_12981

/-!
# Minimum size, depth, and optimal monotone formulas for L-meta-12982

The binary gate-count lower bound is due to NotoriousH2 (L-meta-12981).
Hemmurs also gives a seven-gate upper bound for the same function.
The formula classification and depth bound below use independent finite certificates.
The accompanying LRAT certificate covers normalized DAGs with sharing.
-/

namespace Simlowker.Optimal12982
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12981

/-- A size-seven witness that also realizes binary depth four. -/
def optimal : Circuit := ⟨[⟨.or,[2,4]⟩,⟨.and,[1,5]⟩,⟨.or,[3,7]⟩,⟨.and,[0,6]⟩,
  ⟨.and,[8,9]⟩,⟨.and,[1,2]⟩,⟨.or,[10,11]⟩],12⟩

theorem legal : FanInTwo optimal := by simp [FanInTwo,optimal]
theorem balanced : optimal.size=7 ∧ optimal.depth 6=4 := by decide +kernel
set_option maxRecDepth 16000 in
theorem computes : ∀ x : Fin 6 → Bool,optimal.eval (List.ofFn x)=graph x := by decide +kernel

theorem exact_size (s : Nat) : HasCircuitSize 6 graph s ↔ 7 ≤ s := by
  constructor
  · rintro ⟨C,h,sz,ev⟩
    have lb := circuitLower C.gates C.output h ev
    have le : cost C.gates ≤ C.size := List.length_filter_le _ _
    omega
  · intro h
    exact ⟨optimal, legal, balanced.1 ▸ h, computes⟩

theorem optimum_is_monotone (C : Circuit) (h : FanInTwo C) (sz : C.size≤7)
    (ev : ∀ x : Fin 6 → Bool,C.eval (List.ofFn x)=graph x) : Monotone2 C := by
  have lb := circuitLower C.gates C.output h ev
  intro g mem
  obtain ⟨op,cap⟩ := h g mem
  change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
  refine ⟨?_,cap⟩
  rcases op with a | b | n
  · exact Or.inl a
  · exact Or.inr b
  · have lt : cost C.gates < C.size := List.length_filter_lt_length_iff_exists.mpr ⟨g,mem,by simp [useBinary,n]⟩
    omega
end Simlowker.Optimal12982

namespace Simlowker.Formulas12982
abbrev Row := BitVec 9
def column : Fin 6 → Row := ![126,185,323,422,476,488]
def mask : Fin 9 → Nat := ![6,13,25,51,19,43,53,58,60]
def assignment (j : Fin 9) (i : Fin 6) := (mask j).testBit i.val

def target (x : Fin 6 → Bool) := Nat.testBit (3939033280 * 2^32 + 3938508992)
  (∑ i : Fin 6, if x i then 2^i.val else 0)

inductive Tree where
  | input (i : Fin 6)
  | join (conj : Bool) (left right : Tree)
  deriving Repr, DecidableEq

def op (c a b : Bool) := if c then a && b else a || b
def merge (c : Bool) (a b : Row) := if c then a &&& b else a ||| b
def name (c : Bool) (a b : String) :=
  let sep := if c then "&" else "|"
  if a ≤ b then "("++a++sep++b++")" else "("++b++sep++a++")"
def Tree.eval (x : Fin 6 → Bool) : Tree → Bool
  | .input i => x i
  | .join c a b => op c (a.eval x) (b.eval x)
def Tree.row : Tree → Row
  | .input i => column i
  | .join c a b => merge c a.row b.row
def Tree.code : Tree → String
  | .input i => toString i.val
  | .join c a b => name c a.code b.code
def Tree.leaves : Tree → Nat
  | .input _ => 1
  | .join _ a b => a.leaves+b.leaves

theorem positive (t : Tree) : 0<t.leaves := by induction t <;> simp_all [Tree.leaves]

theorem bit_eval (t : Tree) (j : Fin 9) : t.row[j.val]=t.eval (assignment j) := by
  have base : ∀ (i : Fin 6) (k : Fin 9), (column i)[k.val] = assignment k i := by decide +kernel
  induction t with
  | input i => exact base i j
  | join c a b ha hb => cases c <;> simp [Tree.row,Tree.eval,merge,op,ha,hb]

theorem target_signature (t : Tree) (h : ∀ x,t.eval x=target x) : t.row=15 := by
  have sample : ∀ j : Fin 9, target (assignment j)=(15 : Row)[j.val] := by decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro i hi
  exact (bit_eval t ⟨i,hi⟩).trans ((h _).trans (sample ⟨i,hi⟩))

/-- A packed overapproximation of attainable signatures at each leaf budget. -/
def book : Nat → Nat
  | 1 => 0x100100000000000004000000000000000000000000800000000000000000000000000000000020000000000000040000000000000000000000000000000
  | 2 => 0x7a004980900001008000004100000010800000000000000900000000000000048000000000000000020001010100000040000100100000040100004000000002
  | 3 => 0xfb00dfc9f9001990ea0041d510000051c80009809000000f000000400000000dea000100100000008300034303000101d50045405000010d4300014101000017
  | 4 => 0xff00dffffb00dfd9fb00ddd795001175fb00cdc9d900099f840000450000005ffb004d8495000100eb00435713000313d50057457500155f570043d71300015f
  | 5 => 0xff00ffffff00ffffff00ffffff005df7ff00dffbfb00dd9fef004dd59500005fff00dfefff001d95fb00dfd797001357ff00dfd5f500575fd70057d75700137f
  | 6 => 0xff00ffffff00ffffff00ffffff00ffffff00ffffff00dfffff00dfffff005dffff00ffffff00dfffff00ffffff005ff7ff00ffffff007fffff00dffff70057ff
  | 7 => 0xff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00dfffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff007fff
  | 8 => 0xff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffff
  | _ => 0

/-- Exact shape lists for the signatures which can lead to an optimum formula. -/
def palette : Nat → Nat → Option (List String)
  | 1, 126 => some ["0"]
  | 1, 185 => some ["1"]
  | 1, 323 => some ["2"]
  | 1, 422 => some ["3"]
  | 1, 476 => some ["4"]
  | 1, 488 => some ["5"]
  | 2, 1 => some ["(1&2)"]
  | 2, 38 => some ["(0&3)"]
  | 2, 92 => some ["(0&4)"]
  | 2, 104 => some ["(0&5)"]
  | 2, 168 => some ["(1&5)"]
  | 2, 479 => some ["(2|4)"]
  | 2, 491 => some ["(2|5)"]
  | 2, 494 => some ["(3|5)"]
  | 3, 94 => some ["((2|4)&0)"]
  | 3, 110 => some ["((3|5)&0)"]
  | 3, 169 => some ["((2|5)&1)"]
  | 3, 191 => some ["((0&3)|1)"]
  | 3, 351 => some ["((0&4)|2)"]
  | 3, 363 => some ["((0&5)|2)"]
  | 3, 430 => some ["((1&5)|3)"]
  | 3, 460 => some ["((3|5)&4)"]
  | 4, 41 => some ["(((0&5)|2)&1)"]
  | 4, 46 => some ["(((1&5)|3)&0)"]
  | 4, 76 => some ["(((3|5)&0)&4)","(((3|5)&4)&0)","((0&4)&(3|5))"]
  | 5, 175 => some ["(((2|5)&1)|(0&3))"]
  | 5, 335 => some ["((((3|5)&0)&4)|2)","((((3|5)&4)&0)|2)","(((0&4)&(3|5))|2)"]
  | 5, 398 => some ["(((1&5)|3)&(2|4))"]
  | 6, 14 => some ["((((1&5)|3)&(2|4))&0)","((((1&5)|3)&0)&(2|4))","(((1&5)|3)&((2|4)&0))"]
  | 6, 47 => some ["((((0&5)|2)&1)|(0&3))","((((1&5)|3)&0)|(1&2))"]
  | 8, 15 => some ["(((((0&5)|2)&1)|(0&3))&(2|4))","(((((1&5)|3)&(2|4))&0)|(1&2))","(((((1&5)|3)&0)&(2|4))|(1&2))","(((((1&5)|3)&0)|(1&2))&(2|4))","(((((3|5)&0)&4)|2)&((0&3)|1))","(((((3|5)&4)&0)|2)&((0&3)|1))","((((0&4)&(3|5))|2)&((0&3)|1))","((((1&5)|3)&((2|4)&0))|(1&2))","((((2|5)&1)|(0&3))&((0&4)|2))"]
  | _,_ => none

def dom (k : Nat) : List Row := ((List.range 512).filter (book k).testBit).map (BitVec.ofNat 9)
def Cons (k : Nat) (v : Row) (key : String) : Prop :=
  (book k).testBit v.toNat=true ∧ ∀ xs,palette k v.toNat=some xs → key∈xs

theorem member {k v key} (h : Cons k v key) : v∈dom k := by
  apply List.mem_map.mpr
  exact ⟨v.toNat,List.mem_filter.mpr ⟨List.mem_range.mpr v.isLt,h.1⟩,by simp⟩

def valid (i j : Nat) (a b : Row) (c : Bool) : Bool :=
  let v := merge c a b
  (book (i+j)).testBit v.toNat &&
    match palette (i+j) v.toNat with
    | none => true
    | some out => match palette i a.toNat, palette j b.toNat with
      | some left, some right => left.all (fun x => right.all (fun y => out.contains (name c x y)))
      | _,_ => false

def pairsOK (i j : Nat) := (dom i).all (fun a => (dom j).all (fun b => valid i j a b true && valid i j a b false))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
theorem checked1 : ∀ j : Fin 8, 1+ (j.val+1) ≤8 → pairsOK 1 (j.val+1)=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
theorem checked2 : ∀ j : Fin 8, 2+ (j.val+1) ≤8 → pairsOK 2 (j.val+1)=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
theorem checked3 : ∀ j : Fin 8, 3+ (j.val+1) ≤8 → pairsOK 3 (j.val+1)=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
theorem checked4 : ∀ j : Fin 8, 4+ (j.val+1) ≤8 → pairsOK 4 (j.val+1)=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
theorem checked5 : ∀ j : Fin 8, 5+ (j.val+1) ≤8 → pairsOK 5 (j.val+1)=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
theorem checked6 : ∀ j : Fin 8, 6+ (j.val+1) ≤8 → pairsOK 6 (j.val+1)=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
theorem checked7 : ∀ j : Fin 8, 7+ (j.val+1) ≤8 → pairsOK 7 (j.val+1)=true := by decide +kernel


end Simlowker.Formulas12982

set_option maxRecDepth 16000
namespace Simlowker.Formulas12982
theorem checked (i j : Nat) (a : 0 < i) (b : 0 < j) (budget : i+j≤8) : pairsOK i j = true := by
  obtain ⟨x,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
  have jj : x < 8 := by omega
  have hi : i ≤ 7 := by omega
  interval_cases i
  · exact checked1 ⟨x,jj⟩ budget
  · exact checked2 ⟨x,jj⟩ budget
  · exact checked3 ⟨x,jj⟩ budget
  · exact checked4 ⟨x,jj⟩ budget
  · exact checked5 ⟨x,jj⟩ budget
  · exact checked6 ⟨x,jj⟩ budget
  · exact checked7 ⟨x,jj⟩ budget

theorem combine {i j a b x y c} (left : Cons i a x) (right : Cons j b y) (v : valid i j a b c=true) :
    Cons (i+j) (merge c a b) (name c x y) := by
  obtain ⟨ok,rest⟩ := Bool.and_eq_true_iff.mp v
  refine ⟨ok,?_⟩
  intro out hp
  simp only [hp] at rest
  cases l : palette i a.toNat with
  | none => simp [l] at rest
  | some ls =>
    cases r : palette j b.toNat with
    | none => simp [l,r] at rest
    | some rs =>
      simp only [l,r] at rest
      exact List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp rest x (left.2 ls l)) y (right.2 rs r))

theorem invariant (t : Tree) (budget : t.leaves≤8) : Cons t.leaves t.row t.code := by
  induction t with
  | input i =>
    have base : ∀ v : Fin 6,(book 1).testBit (column v).toNat=true ∧ palette 1 (column v).toNat=some [toString v.val] := by decide +kernel
    refine ⟨(base i).1,?_⟩
    intro xs hx
    change palette 1 (column i).toNat=some xs at hx
    rw [(base i).2] at hx
    cases hx; simp [Tree.code]
  | join c a b ha hb =>
    change a.leaves+b.leaves≤8 at budget
    have la := ha (by omega); have lb := hb (by omega)
    have all := checked _ _ (positive a) (positive b) budget
    have test := Bool.and_eq_true_iff.mp (List.all_eq_true.mp (List.all_eq_true.mp all a.row (member la)) b.row (member lb))
    apply combine la lb
    cases c <;> first | exact test.1 | exact test.2

def winners : List String := ["(((((0&5)|2)&1)|(0&3))&(2|4))","(((((1&5)|3)&(2|4))&0)|(1&2))","(((((1&5)|3)&0)&(2|4))|(1&2))","(((((1&5)|3)&0)|(1&2))&(2|4))","(((((3|5)&0)&4)|2)&((0&3)|1))","(((((3|5)&4)&0)|2)&((0&3)|1))","((((0&4)&(3|5))|2)&((0&3)|1))","((((1&5)|3)&((2|4)&0))|(1&2))","((((2|5)&1)|(0&3))&((0&4)|2))"]

theorem all_minimum_trees (t : Tree) (works : ∀ x,t.eval x=target x) (budget : t.leaves≤8) :
    t.leaves=8 ∧ t.code∈winners := by
  have h := invariant t budget
  rw [target_signature t works] at h
  have k : t.leaves=8 := by
    have lower : ∀ j : Fin 8, (book j.val).testBit 15=false := by decide +kernel
    by_contra ne
    have lo := lower ⟨t.leaves,by omega⟩
    have bad : (book t.leaves).testBit 15=true := h.1
    simp [bad] at lo
  rw [k] at h
  exact ⟨k,h.2 winners rfl⟩

def representatives : List Tree := [(.join true (.join false (.join true (.join false (.join true (.input 0) (.input 5)) (.input 2)) (.input 1)) (.join true (.input 0) (.input 3))) (.join false (.input 2) (.input 4))),
  (.join false (.join true (.join true (.join false (.join true (.input 1) (.input 5)) (.input 3)) (.join false (.input 2) (.input 4))) (.input 0)) (.join true (.input 1) (.input 2))),
  (.join false (.join true (.join true (.join false (.join true (.input 1) (.input 5)) (.input 3)) (.input 0)) (.join false (.input 2) (.input 4))) (.join true (.input 1) (.input 2))),
  (.join true (.join false (.join true (.join false (.join true (.input 1) (.input 5)) (.input 3)) (.input 0)) (.join true (.input 1) (.input 2))) (.join false (.input 2) (.input 4))),
  (.join true (.join false (.join true (.join true (.join false (.input 3) (.input 5)) (.input 0)) (.input 4)) (.input 2)) (.join false (.join true (.input 0) (.input 3)) (.input 1))),
  (.join true (.join false (.join true (.join true (.join false (.input 3) (.input 5)) (.input 4)) (.input 0)) (.input 2)) (.join false (.join true (.input 0) (.input 3)) (.input 1))),
  (.join true (.join false (.join true (.join true (.input 0) (.input 4)) (.join false (.input 3) (.input 5))) (.input 2)) (.join false (.join true (.input 0) (.input 3)) (.input 1))),
  (.join false (.join true (.join false (.join true (.input 1) (.input 5)) (.input 3)) (.join true (.join false (.input 2) (.input 4)) (.input 0))) (.join true (.input 1) (.input 2))),
  (.join true (.join false (.join true (.join false (.input 2) (.input 5)) (.input 1)) (.join true (.input 0) (.input 3))) (.join false (.join true (.input 0) (.input 4)) (.input 2)))]

set_option maxRecDepth 16000 in
theorem all_attained : representatives.map Tree.code=winners ∧ winners.Nodup ∧ winners.length=9 ∧
    representatives.all (fun t => decide (t.leaves=8 ∧ ∀ x : Fin 6 → Bool,t.eval x=target x))=true := by decide +kernel
end Simlowker.Formulas12982

namespace Simlowker.Depth12982
open PEqualNP.CircuitLowerBounds
abbrev W := BitVec 9
def cols : Fin 6 → W := ![245, 408, 14, 303, 496, 448]
def rows : Fin 9 → Nat := ![9, 12, 13, 14, 19, 25, 49, 51, 58]
def goal : W := 172
def table : Nat → Nat
  | 0 => 0x8003000000000001000000000100000000000000000000000000800000000400002000000001000000000000000000000000008000000000800000000000c001
  | 1 => 0xefa380800501c40180000000c50100010000800000000000800080030000c50180a30000c00100010000000000010000800080a300000001802380a00101c5f7
  | 2 => 0xffffefeffff7fff7efa380a3fff7c5f78000efa30000c501efa3efffc501fff7efff80a3fff7c5f780a30000c5f70001efa3efffc501c5f7efffeffff7f7ffff
  | _ => 0
def good (d : Nat) (v : W) :=
  if d<3 then (table d).testBit v.toNat else if d=3 then v != goal && v != (~~~goal) else true

def dom (d : Nat) := ((List.range 512).filter (table d).testBit).map (BitVec.ofNat 9)
lemma member {d : Nat} {v : W} (h : d<3) (ok : good d v=true) : v∈dom d := by
  apply List.mem_map.mpr
  exact ⟨v.toNat,List.mem_filter.mpr ⟨List.mem_range.mpr v.isLt,by simpa [good,h] using ok⟩,by simp⟩

def join (c : Bool) (a b : W) := if c then a &&& b else a ||| b

def jointest (d : Nat) := (dom d).all (fun a => (dom d).all (fun b => good (d+1) (join true a b) && good (d+1) (join false a b)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check0 : jointest 0=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem check1 : jointest 1=true := by decide +kernel
def slice (i : Nat) := ((dom 2).drop (8*i) |>.take 8).all (fun a => (dom 2).all (fun b => good 3 (join true a b) && good 3 (join false a b)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf0 : slice 0=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf1 : slice 1=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf2 : slice 2=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf3 : slice 3=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf4 : slice 4=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf5 : slice 5=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf6 : slice 6=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf7 : slice 7=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf8 : slice 8=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf9 : slice 9=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf10 : slice 10=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf11 : slice 11=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf12 : slice 12=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf13 : slice 13=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf14 : slice 14=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf15 : slice 15=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf16 : slice 16=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf17 : slice 17=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf18 : slice 18=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf19 : slice 19=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf20 : slice 20=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf21 : slice 21=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf22 : slice 22=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf23 : slice 23=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf24 : slice 24=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf25 : slice 25=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf26 : slice 26=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf27 : slice 27=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf28 : slice 28=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf29 : slice 29=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf30 : slice 30=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf31 : slice 31=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf32 : slice 32=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf33 : slice 33=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf34 : slice 34=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf35 : slice 35=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf36 : slice 36=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf37 : slice 37=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf38 : slice 38=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf39 : slice 39=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf40 : slice 40=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem leaf41 : slice 41=true := by decide +kernel
end Simlowker.Depth12982

set_option maxRecDepth 16000
namespace Simlowker.Depth12982
open PEqualNP.CircuitLowerBounds
theorem check2 : jointest 2=true := by
  apply List.all_eq_true.mpr
  intro a ha
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp ha
  have size : (dom 2).length=330 := by decide +kernel
  have row : i/8<42 := by omega
  have sub : a∈((dom 2).drop (8*(i/8))).take 8 := by
    apply List.mem_iff_getElem.mpr
    refine ⟨i%8,by simp; omega,?_⟩
    simp only [List.getElem_take, List.getElem_drop]
    convert eq using 2; omega
  have all : slice (i/8)=true := by
    generalize h : i/8=j at *
    interval_cases j
    · exact leaf0
    · exact leaf1
    · exact leaf2
    · exact leaf3
    · exact leaf4
    · exact leaf5
    · exact leaf6
    · exact leaf7
    · exact leaf8
    · exact leaf9
    · exact leaf10
    · exact leaf11
    · exact leaf12
    · exact leaf13
    · exact leaf14
    · exact leaf15
    · exact leaf16
    · exact leaf17
    · exact leaf18
    · exact leaf19
    · exact leaf20
    · exact leaf21
    · exact leaf22
    · exact leaf23
    · exact leaf24
    · exact leaf25
    · exact leaf26
    · exact leaf27
    · exact leaf28
    · exact leaf29
    · exact leaf30
    · exact leaf31
    · exact leaf32
    · exact leaf33
    · exact leaf34
    · exact leaf35
    · exact leaf36
    · exact leaf37
    · exact leaf38
    · exact leaf39
    · exact leaf40
    · exact leaf41
  exact List.all_eq_true.mp all a sub

theorem lift1 {d : Nat} {a : W} (ok : good d a=true) : good (d+1) a=true := by
  have steps : ∀ (k : Fin 4) (v : W), good k.val v=true → good (k.val+1) v=true := by decide +kernel
  by_cases h : d<4
  · exact steps ⟨d,h⟩ a ok
  · simp [good,show ¬d+1<3 by omega,show d+1≠3 by omega]
theorem liftGood {d h : Nat} {v : W} (lo : d≤h) (ok : good d v=true) : good h v=true := by
  induction lo with | refl => exact ok | step _ ih => exact lift1 ih

theorem notGood {d : Nat} {v : W} (ok : good d v=true) : good d (~~~v)=true := by
  have casesChecked : ∀ (k : Fin 4) (x : W), good k.val x=true → good k.val (~~~x)=true := by decide +kernel
  by_cases h : d<4
  · exact casesChecked ⟨d,h⟩ v ok
  · simp [good,show ¬d<3 by omega,show d≠3 by omega]
theorem joinGood {d : Nat} {a b : W} (c : Bool) (aa : good d a=true) (bb : good d b=true) : good (d+1) (join c a b)=true := by
  by_cases h : d<3
  · have hs : jointest d=true := by
      interval_cases d
      · exact check0
      · exact check1
      · exact check2
    have ans := Bool.and_eq_true_iff.mp (List.all_eq_true.mp (List.all_eq_true.mp hs a (member h aa)) b (member h bb))
    cases c <;> first | exact ans.1 | exact ans.2
  · simp [good,show ¬d+1<3 by omega,show d+1≠3 by omega]

inductive Expr where
  | var (i : Fin 6)
  | constant (c : Bool)
  | neg (t : Expr)
  | branch (andGate : Bool) (a b : Expr)
  deriving Repr

def Expr.dep : Expr → Nat
  | .var _ | .constant _ => 0
  | .neg t => t.dep
  | .branch _ a b => max a.dep b.dep + 1
def Expr.word : Expr → W
  | .var i => cols i
  | .constant c => if c then 511 else 0
  | .neg a => ~~~a.word
  | .branch c a b => join c a.word b.word

def Expr.eval (x : Fin 6 → Bool) : Expr → Bool
  | .var i => x i
  | .constant c => c
  | .neg a => !a.eval x
  | .branch c a b => if c then a.eval x && b.eval x else a.eval x || b.eval x

theorem bounded (t : Expr) : good t.dep t.word=true := by
  induction t with
  | var i => exact (by decide +kernel : ∀ j : Fin 6,good 0 (cols j)=true) i
  | constant c => cases c <;> decide +kernel
  | neg a ih => exact notGood ih
  | branch c a b ha hb => exact joinGood c (liftGood (Nat.le_max_left _ _) ha) (liftGood (Nat.le_max_right _ _) hb)

theorem agrees (t : Expr) (j : Fin 9) : t.word[j.val]=t.eval (fun i => (rows j).testBit i.val) := by
  induction t with
  | var i => exact (by decide +kernel : ∀ (k : Fin 6) (r : Fin 9), (cols k)[r.val]=(rows r).testBit k.val) i j
  | constant c => exact (by decide +kernel : ∀ (v : Bool) (r : Fin 9), (Expr.constant v).word[r.val]=v) c j
  | neg a h => simp [Expr.word,Expr.eval,h]
  | branch c a b ha hb => cases c <;> simp [Expr.word,Expr.eval,join,ha,hb]

def target (x : Fin 6 → Bool) := Nat.testBit (3939033280 * 2^32 + 3938508992) (∑ i : Fin 6, if x i then 2^i.val else 0)

theorem at_least_four (t : Expr) (correct : ∀ x,t.eval x=target x) : 4≤t.dep := by
  have sample : ∀ j : Fin 9,target (fun i => (rows j).testBit i.val)=goal[j.val] := by decide +kernel
  have eq : t.word=goal := BitVec.eq_of_getElem_eq fun i hi => (agrees t ⟨i,hi⟩).trans ((correct _).trans (sample ⟨i,hi⟩))
  by_contra! low
  have yes := liftGood (by omega : t.dep≤3) (bounded t)
  rw [eq] at yes
  exact Bool.noConfusion (show false=true from yes)
end Simlowker.Depth12982

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Simlowker.Depth12982
abbrev Annot := Expr × Nat
def dummy : Annot := (.constant false,0)
def choose (o : GateOp) (es : List Expr) : Expr :=
  match o, es with
  | .and, [] => .constant true
  | .or, [] => .constant false
  | .and, [a] | .or, [a] => a
  | .and, a::b::_ => .branch true a b
  | .or, a::b::_ => .branch false a b
  | .not, a::_ => .neg a
  | .not, [] => .constant true
  | _, _ => .constant false
def make (o : GateOp) (ps : List Annot) : Annot :=
  (choose o (ps.map Prod.fst), (ps.map Prod.snd).foldr max 0 + 1)
def validOp (o : GateOp) := o = .and ∨ o = .or ∨ o = .not
def readout (x : Fin 6 → Bool) (p : Annot) := p.1.eval x
theorem gateEval (o : GateOp) (ps : List Annot) (x : Fin 6 → Bool) (op : validOp o) (arity : ps.length≤2) :
    readout x (make o ps)=o.eval (ps.map (readout x)) := by
  rcases op with rfl | rfl | rfl <;> rcases ps with _ | ⟨a,_|⟨b,_|⟨c,cs⟩⟩⟩ <;>
    simp_all [make,choose,readout,Expr.eval,GateOp.eval]
def safe (p : Annot) := p.1.dep ≤ p.2
theorem gateSafe (o : GateOp) (ps : List Annot) (each : ∀ p ∈ ps,safe p) (op : validOp o) (arity : ps.length≤2) :
    safe (make o ps) := by
  rcases op with rfl | rfl | rfl <;> rcases ps with _ | ⟨a,_|⟨b,_|⟨c,cs⟩⟩⟩ <;>
    simp_all [make,choose,safe,Expr.dep] <;> omega

def reading (ps : List Annot) (g : Gate) := g.inputs.map fun i => ps.getD i dummy
def step (ps : List Annot) (g : Gate) := ps ++ [make g.op (reading ps g)]
def initial : List Annot := List.ofFn fun i : Fin 6 => (Expr.var i,0)
def unfoldCircuit (C : Circuit) := (C.gates.foldl step initial).getD C.output dummy

theorem traceMap {α : Type} (proj : Annot → α) (extend : List α → Gate → List α) (gs : List Gate)
    (ok : ∀ g∈gs, validOp g.op ∧ g.inputs.length≤2)
    (comm : ∀ ps g, validOp g.op → g.inputs.length≤2 → (step ps g).map proj=extend (ps.map proj) g)
    (ps : List Annot) : (gs.foldl step ps).map proj=gs.foldl extend (ps.map proj) := by
  induction gs generalizing ps with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (fun h hm => ok h (by simp [hm])),comm ps g (ok g (by simp)).1 (ok g (by simp)).2]

theorem unfold_eval (C : Circuit) (h : FanInTwo C) (x : Fin 6 → Bool) :
    (unfoldCircuit C).1.eval x=C.eval (List.ofFn x) := by
  let f := fun (v : List Bool) (g : Gate) => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]
  have comm (ps : List Annot) (g : Gate) (op : validOp g.op) (ar : g.inputs.length≤2) :
      (step ps g).map (readout x)= f (ps.map (readout x)) g := by
    have e := gateEval g.op (reading ps g) x op (by simpa [reading] using ar)
    have m (i : Nat) : (ps.map (readout x)).getD i false=readout x (ps.getD i dummy) :=
      List.getD_map ps dummy (readout x)
    simp only [step,f,List.map_append,List.map_cons,List.map_nil,e]
    simp only [reading,List.map_map,Function.comp_def,m]
  have t := traceMap (readout x) f C.gates h comm initial
  have start : initial.map (readout x)=List.ofFn x := by simp [initial,readout,Expr.eval]
  rw [start] at t
  have out := congrArg (fun ps : List Bool => ps.getD C.output false) t
  calc readout x (unfoldCircuit C) = ((C.gates.foldl step initial).map (readout x)).getD C.output false :=
         (List.getD_map _ dummy (readout x)).symm
       _ = C.eval (List.ofFn x) := out

theorem unfold_depth (C : Circuit) (h : FanInTwo C) : (unfoldCircuit C).2=C.depth 6 := by
  let f := fun (v : List Nat) (g : Gate) => v ++ [(g.inputs.map fun i => v.getD i 0).foldr max 0+1]
  have comm (ps : List Annot) (g : Gate) (_ : validOp g.op) (_ : g.inputs.length≤2) :
      (step ps g).map Prod.snd=f (ps.map Prod.snd) g := by
    have m (i : Nat) : (ps.map Prod.snd).getD i 0=(ps.getD i dummy).2 := List.getD_map ps dummy Prod.snd
    simp only [step,f,make,List.map_append,List.map_nil,List.map_cons,reading,List.map_map,Function.comp_def,m]
  have t := traceMap Prod.snd f C.gates h comm initial
  have start : initial.map Prod.snd=List.replicate 6 0 := by decide +kernel
  rw [start] at t
  calc (unfoldCircuit C).2 = ((C.gates.foldl step initial).map Prod.snd).getD C.output 0 :=
         (List.getD_map _ dummy Prod.snd).symm
       _ = C.depth 6 := congrArg (fun ps : List Nat => ps.getD C.output 0) t

theorem readSafe (ps : List Annot) (all : ∀ p∈ps,safe p) (i : Nat) : safe (ps.getD i dummy) := by
  by_cases h : i<ps.length
  · rw [List.getD_eq_getElem _ _ h]; exact all _ (List.getElem_mem _)
  · have hi : ps.length ≤ i := by omega
    rw [List.getD_eq_default _ _ hi]
    exact Nat.le_refl 0
theorem traceSafe (gs : List Gate) (h : ∀ g∈gs,validOp g.op ∧ g.inputs.length≤2)
    (ps : List Annot) (all : ∀ p∈ps,safe p) : ∀ p∈gs.foldl step ps,safe p := by
  induction gs generalizing ps with
  | nil => exact all
  | cons g gs ih =>
    apply ih (fun q hq => h q (by simp [hq]))
    intro p hp
    rcases List.mem_append.mp hp with old | new
    · exact all p old
    · obtain rfl := List.mem_singleton.mp new
      apply gateSafe _ _ _ (h g (by simp)).1 (by simpa [reading] using (h g (by simp)).2)
      intro s hs
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hs
      exact readSafe ps all i
theorem circuit_depth_at_least_four (C : Circuit) (h : FanInTwo C)
    (computes : ∀ x : Fin 6 → Bool,C.eval (List.ofFn x)=target x) : 4≤C.depth 6 := by
  have bound := at_least_four (unfoldCircuit C).1 fun x => (unfold_eval C h x).trans (computes x)
  have safeInit : ∀ p∈initial,safe p := by
    intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact Nat.le_refl 0
  have sound := readSafe _ (traceSafe C.gates h initial safeInit) C.output
  exact (bound.trans sound).trans_eq (unfold_depth C h)
end Simlowker.Depth12982

#print axioms Simlowker.Optimal12982.exact_size
#print axioms Simlowker.Optimal12982.balanced
#print axioms Simlowker.Optimal12982.computes
#print axioms Simlowker.Optimal12982.optimum_is_monotone
#print axioms Simlowker.Formulas12982.all_minimum_trees
#print axioms Simlowker.Formulas12982.all_attained
#print axioms Simlowker.Depth12982.at_least_four
#print axioms Simlowker.Depth12982.circuit_depth_at_least_four
