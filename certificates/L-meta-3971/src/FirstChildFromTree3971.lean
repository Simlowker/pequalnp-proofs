import UnfoldCircuit3971
namespace PetersenNegated3971
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 4000
set_option maxHeartbeats 5000000

theorem noNeg_fit3971 (f : Formula) (h : marked f=0) (r : Nat) :
  f.eval (literal 0 r)=f.eval (leafValue r) := by
  have no : (12 : Fin 13)∉labels f := by
    intro mem
    have n := List.count_pos_iff.mpr mem
    change 0<marked f at n
    omega
  have agree (i : Fin 13) (hi : i∈labels f) : literal 0 r i=leafValue r i := by
    have n : i.val≠12 := fun eq => no ((Fin.ext eq : i=12) ▸ hi)
    simp [leafValue,n]
  apply Bool.eq_iff_iff.mpr
  exact ⟨eval_mono_on f _ _ (fun i hi => (agree i hi) ▸ id),eval_mono_on f _ _ (fun i hi => (agree i hi) ▸ id)⟩

theorem first_child_given3971
    (lower : ∀ o t : Formula, marked o=1 →
        (∀ r : Fin 512, o.eval (outerValue t r.val)=edge r.val) → 14<o.leaves-1+t.leaves) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → let init : List (Nat × Nat) := List.replicate 10 (1,0)
    let ws := C.gates.foldl (fun (s : List (Nat × Nat)) g =>
      let col := fun j => (g.inputs[j]?.bind fun i => s[i]?).getD (1,0)
      let a := col 0
      let b := col 1
      s ++ [ite (g.op.eval [false]=true) (a.1,a.2+1) (a.1+b.1,a.2+b.2)]) init
    let z := ws.getD C.output (1,0)
    z.2≤1 → z.1+z.2≤15 → ∃ r : Nat, r<512 ∧ C.eval ((([1,0,4,7,5,2,8,6,3] : List Nat).map (fun i => r.testBit i)) ++ [r.testBit 1 || r.testBit 8]) ≠ (13407807929942597095939831376727811673905304651018912648022854022873869787405066962725179222507908767667956533170508564710083788841651696458571261487544520 : Nat).testBit r := by
  intro C fan
  dsimp only
  intro n budget
  by_contra! all_fit
  have good (g : Gate) (hg : g∈C.gates) : goodGate3971 g := fan g hg
  let e := unfold3971 C
  have stat := fold_map3971 Expr3971.stat sizeNode3971 project_stat3971 C.gates good treeInit3971
  have projection := (List.getD_map (l:=C.gates.foldl treeStep3971 treeInit3971) (n:=C.output)
    (d:=.atom 10) Expr3971.stat).symm
  rw [stat] at projection
  change e.stat= _ at projection
  have n' : e.stat.2≤1 := by rw [projection]; exact n
  have b' : e.stat.1+e.stat.2≤15 := by rw [projection]; exact budget
  have spec (r : Fin 512) : e.ev r.val=edge r.val := by
    let p := Expr3971.ev r.val
    let q (ws : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => ws.getD i false)
    have vals := fold_map3971 p q (fun ws g h => project_val3971 ws g h r.val) C.gates good treeInit3971
    have out := read_val3971 (C.gates.foldl treeStep3971 treeInit3971) C.output r.val
    change e.ev r.val=(_ : List Bool).getD C.output false at out
    rw [vals] at out
    have inputs : treeInit3971.map p = (([1,0,4,7,5,2,8,6,3] : List Nat).map (fun i => r.val.testBit i)) ++ [r.val.testBit 1 || r.val.testBit 8] := by rfl
    rw [inputs] at out
    have goalAt := all_fit r.val r.isLt
    have t : ∀ u : Fin 512, (13407807929942597095939831376727811673905304651018912648022854022873869787405066962725179222507908767667956533170508564710083788841651696458571261487544520 : Nat).testBit u.val=edge u.val := by decide +kernel
    exact out.trans (goalAt.trans (t r))
  by_cases zero : e.stat.2=0
  · obtain ⟨f,m,len,sem⟩ := (tree_decomp e).1 zero
    have bound := from_certificate 0 15 w0 121 (by decide) cert0.2 cert0.1 f
      (fun r => (noNeg_fit3971 f m r.val).trans ((sem r.val).trans (spec r)))
    omega
  · obtain ⟨o,t,m,len,sem⟩ := (tree_decomp e).2 (by omega)
    have bound := lower o t m (fun r => (sem r.val).trans (spec r))
    omega
end PetersenNegated3971
