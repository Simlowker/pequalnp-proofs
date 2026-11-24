import RawNeg3971
import Mathlib.Data.Finset.Card
namespace PetersenNegated3971

def labels : Formula → List (Fin 13)
  | .var i => [i]
  | .disj a b | .conj a b => labels a ++ labels b

theorem label_count (f : Formula) : (labels f).length=f.leaves := by
  induction f with
  | var i => rfl
  | disj a b ia ib | conj a b ia ib => simp [labels,Formula.leaves,ia,ib]

theorem eval_mono_on (f : Formula) (a b : Fin 13 → Bool)
    (le' : ∀ j∈labels f, a j=true → b j=true) : f.eval a=true → f.eval b=true := by
  induction f with
  | var i => exact le' i (by simp [labels])
  | disj a b ia ib =>
    simp only [Formula.eval,Bool.or_eq_true_iff]
    exact Or.imp (ia (fun j hj => le' j (List.mem_append_left _ hj)))
      (ib (fun j hj => le' j (List.mem_append_right _ hj)))
  | conj a b ia ib =>
    simp only [Formula.eval,Bool.and_eq_true_iff]
    exact And.imp (ia (fun j hj => le' j (List.mem_append_left _ hj)))
      (ib (fun j hj => le' j (List.mem_append_right _ hj)))

def outside (v : Nat → Bool) (r : Nat) (j : Fin 13) := if j.val=12 then v r else literal 0 r j
def loRows (i : Fin 9) := ([2,260,2,4,1,2,4,8,10] : List Nat).getD i.val 0
def hiRows (i : Fin 9) := loRows i ||| 2^i.val

theorem essential (f : Formula) (v : Nat → Bool)
    (anti : ∀ i, v (hiRows i)=true → v (loRows i)=true)
    (spec : ∀ r : Fin 512, f.eval (outside v r.val)=edge r.val) :
    ∀ i : Fin 9, (⟨i.val,by omega⟩ : Fin 13)∈labels f := by
  have data' : ∀ i : Fin 9, loRows i<512 ∧ hiRows i<512 ∧
      edge (loRows i)=false ∧ edge (hiRows i)=true ∧
      ∀ j : Fin 13, j.val≠i.val → j.val≠12 → literal 0 (hiRows i) j=literal 0 (loRows i) j := by decide +kernel
  intro i
  obtain ⟨small,big,off,on',rest⟩ := data' i
  by_contra missing
  have rev := eval_mono_on f (outside v (hiRows i)) (outside v (loRows i)) (by
    intro j mem
    by_cases h : j.val=12
    · simpa [outside,h] using anti i
    have ne : j.val≠i.val := by
      intro same
      exact missing ((Fin.ext same : j=⟨i.val,by omega⟩) ▸ mem)
    simp [outside,h,rest j ne h])
  have yes := rev ((spec ⟨_,big⟩).trans on')
  exact Bool.false_ne_true (((spec ⟨_,small⟩).trans off).symm.trans yes)

def required : Finset (Fin 13) := {0,1,2,3,4,5,6,7,8,12}

theorem negative_budget (outer : Formula) (v : Nat → Bool)
    (anti : ∀ i, v (hiRows i)=true → v (loRows i)=true)
    (spec : ∀ r : Fin 512, outer.eval (outside v r.val)=edge r.val)
    (uses : 12∈labels outer) (k : Nat) (size : outer.leaves - 1 + k ≤14) : k≤5 := by
  have ess := essential outer v anti spec
  have classify : ∀ j∈required, j.val<9 ∨ j=12 := by decide +kernel
  have sub : required ⊆ (labels outer).toFinset := by
    intro j hj
    apply List.mem_toFinset.mpr
    rcases classify j hj with small|rfl
    · exact ess ⟨j.val,small⟩
    · exact uses
  have a := Finset.card_le_card sub
  have n : required.card=10 := by decide +kernel
  have b := List.toFinset_card_le (labels outer)
  rw [n] at a
  rw [label_count] at b
  omega

end PetersenNegated3971
