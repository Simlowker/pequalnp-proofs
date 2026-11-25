import Mathlib
import PEqualNP.Defs

/-! Minimum depth for the table 0xfeeaeeeafeeaecc8. Nine sampled assignments suffice
to exclude every signed AND/OR formula of binary depth three. -/

namespace Simlowker.Depth16756
open PEqualNP.CircuitLowerBounds
abbrev W := BitVec 9
def cols : Fin 6 → W := ![75, 188, 339, 386, 28, 480]
def rows : Fin 9 → Nat := ![5, 13, 18, 19, 22, 34, 37, 42, 44]
def goal : W := 218
def table : Nat → Nat
  | 0 => 0x80000009000000000010000000000004000000000008000800000000000000000000000000000000100010000000000020000000000008000000000090000001
  | 1 => 0xb098980d00080808d0504001c000000580000000880808090000000000010005a0008000000000009010101100000001a000000380020a0b10101000b019190d
  | 2 => 0xf8ffffdfc88b8b0ff0dddd5df0dddd0db89b980fbb9b9b0fd0505001fd5d5d0db0bababf800a0a0bf0d9d9ddf019d91db0bbbb0fbabbbb0ff0d1d113fbffff1f
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
end Simlowker.Depth16756
set_option maxRecDepth 16000
namespace Simlowker.Depth16756
open PEqualNP.CircuitLowerBounds
theorem check2 : jointest 2=true := by
  apply List.all_eq_true.mpr
  intro a ha
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp ha
  have size : (dom 2).length=294 := by decide +kernel
  have row : i/8<37 := by omega
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

def target (x : Fin 6 → Bool) := Nat.testBit (4276809450 * 2^32 + 4276808904) (∑ i : Fin 6, if x i then 2^i.val else 0)

theorem at_least_four (t : Expr) (correct : ∀ x,t.eval x=target x) : 4≤t.dep := by
  have sample : ∀ j : Fin 9,target (fun i => (rows j).testBit i.val)=goal[j.val] := by decide +kernel
  have eq : t.word=goal := BitVec.eq_of_getElem_eq fun i hi => (agrees t ⟨i,hi⟩).trans ((correct _).trans (sample ⟨i,hi⟩))
  by_contra! low
  have yes := liftGood (by omega : t.dep≤3) (bounded t)
  rw [eq] at yes
  exact Bool.noConfusion (show false=true from yes)
end Simlowker.Depth16756
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Simlowker.Depth16756
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
end Simlowker.Depth16756

#print axioms Simlowker.Depth16756.circuit_depth_at_least_four
