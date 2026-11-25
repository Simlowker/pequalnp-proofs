import RenameRows2585
namespace IncidenceCover.Three
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def resize {n m : Nat} (σ : Fin n → Fin m) (i : Nat) :=
  if h : i<n then (σ ⟨i,h⟩).val else m+(i-n)

theorem resize_rel_append {n m : Nat} (σ : Fin n → Fin m)
    (v w : List Bool) (k : Nat) (hl : v.length=n+k) (hr : w.length=m+k)
    (rel : wireRel (resize σ) v w) (b : Bool) : wireRel (resize σ) (v++[b]) (w++[b]) := by
  intro i
  by_cases hi : i<v.length
  · have small : resize σ i<w.length := by
      by_cases raw : i<n
      · simp [resize,raw,hr]; have h := (σ ⟨i,raw⟩).isLt; omega
      · simp [resize,raw,hr]; omega
    simpa only [List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ small] using rel i
  · have nonraw : ¬i<n := by omega
    have off : resize σ i-w.length=i-v.length := by simp [resize,nonraw,hr,hl]; omega
    have big : w.length≤resize σ i := by simp [resize,nonraw,hr]; omega
    rw [List.getD_append_right _ _ _ _ big,List.getD_append_right _ _ _ _ (by omega),off]

theorem resize_gates {n m : Nat} (σ : Fin n → Fin m) (gs : List Gate) (v w : List Bool)
    (k : Nat) (hl : v.length=n+k) (hr : w.length=m+k) (rel : wireRel (resize σ) v w) :
    wireRel (resize σ)
      (gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) v)
      ((gs.map (renameGate (resize σ))).foldl
        (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) w) := by
  induction gs generalizing k v w with
  | nil => exact rel
  | cons g gs ih =>
    simp only [List.foldl_cons,List.map_cons]
    have eq : (renameGate (resize σ) g).op.eval
        ((renameGate (resize σ) g).inputs.map fun i => w.getD i false)=
        g.op.eval (g.inputs.map fun i => v.getD i false) := by
      simp only [renameGate,List.map_map]
      congr 2
      exact funext rel
    rw [eq]
    exact ih _ _ (k+1) (by simp [hl,Nat.add_assoc]) (by simp [hr,Nat.add_assoc])
      (resize_rel_append σ v w k hl hr rel _)

theorem resize_eval {n m : Nat} (σ : Fin n → Fin m) (C : Circuit) (z : Fin m → Bool) :
    circuitFun m (renameCircuit (resize σ) C) z = circuitFun n C (fun i => z (σ i)) := by
  apply resize_gates σ C.gates _ _ 0 (by simp) (by simp) _ C.output
  intro i
  by_cases h : i<n
  · rw [show resize σ i = (σ ⟨i,h⟩).val by simp [resize,h],input_get]
    exact (input_get (fun j => z (σ j)) ⟨i,h⟩).symm
  · have large : m≤resize σ i := by simp [resize,h]
    simp [List.getD_eq_default,show ¬i<(List.ofFn (fun j => z (σ j))).length by simpa using h,
      List.getD_eq_getElem?_getD,h,Nat.not_lt.mpr large]

theorem resize_ao {n m : Nat} (σ : Fin n → Fin m) (C : Circuit) (ao : IsAO2 n C) :
    IsAO2 m (renameCircuit (resize σ) C) := by
  refine ⟨?_,?_,?_⟩
  · intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact ao.1 a ha
  · intro j hj i hi
    change j < (C.gates.map (renameGate (resize σ))).length at hj
    have hj' : j<C.gates.length := by simpa using hj
    have hin : i∈(C.gates[j].inputs.map (resize σ)) := by
      simpa [renameCircuit,PEqualNP.MetaComplexity.NestedCover.gateAt,renameGate,List.getD_eq_getElem?_getD,hj'] using hi
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hin
    have bx := ao.2.1 j hj' x (by simpa [PEqualNP.MetaComplexity.NestedCover.gateAt,List.getD_eq_getElem?_getD,hj'] using hx)
    by_cases h : x<n
    · simp [resize,h]; have lim := (σ ⟨x,h⟩).isLt; omega
    · simp [resize,h]; omega
  · intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    simpa [renameGate] using ao.2.2 a ha

#print axioms resize_eval
#print axioms resize_ao
end IncidenceCover.Three
