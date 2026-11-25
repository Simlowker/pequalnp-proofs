import TightIncidence3722
import Mathlib.Data.Nat.Bitwise
namespace IncidenceBudget
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def pairLib : Nat → List Nat
  | 0 => [0, 7, 56, 63]
  | 1 => [0, 2, 5, 7, 16, 21, 23, 40, 42, 47, 56, 58, 61, 63]
  | 2 => [0, 1, 6, 7, 24, 25, 31, 32, 38, 39, 56, 57, 62, 63]
  | 3 => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 16, 17, 20, 21, 22, 23, 24, 25, 26, 27, 29, 31, 32, 34, 36, 37, 38, 39, 40, 41, 42, 43, 46, 47, 48, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
  | _ => []

def bag (a b : Bool) := pairLib (a.toNat+2*b.toNat)
theorem closure : ∀ a b c d : Bool, ¬(a=true ∧ c=true) → ¬(b=true ∧ d=true) →
    ∀ v∈bag a b, ∀ w∈bag c d, v &&& w∈bag (a||c) (b||d) ∧ v ||| w∈bag (a||c) (b||d) := by
  decide +kernel

def pack (rs : List Nat) (f : Nat → Bool) := rs.foldr (fun r n => Nat.bit (f r) n) 0
theorem pack_op (rs : List Nat) (d : Bool) (f g : Nat → Bool) :
    pack rs (fun r => op d (f r) (g r)) =
      if d then pack rs f &&& pack rs g else pack rs f ||| pack rs g := by
  induction rs with
  | nil => cases d <;> simp [pack]
  | cons a rs ih => cases d <;> simp [pack,op,List.foldr_cons,Nat.land_bit,Nat.lor_bit] at ih ⊢ <;> rw [ih]

def vword (u v s t j : Nat) :=
  if j=u then 21 else if j=v then 38 else if j=s ∨ j=t then 56 else 0
def word (u v s t : Nat) (e : Tree) :=
  pack [0,1,2,3,4,5] (fun r => ev (fun j => (vword u v s t j).testBit r) e)

theorem word_bound (u v s t : Nat) (uv : u≠v) (e : Tree) (tight : (sig e).2≤(sig e).1.card) :
    word u v s t e ∈ bag (decide (u∈(sig e).1)) (decide (v∈(sig e).1)) := by
  induction e with
  | dead => change 0 ∈ bag false false; decide +kernel
  | var j =>
    simp only [sig,Finset.mem_singleton,word,ev,vword]
    by_cases ju : j=u
    · subst j
      simp only [ite_true,decide_true,ite_false,uv,Ne.symm uv,decide_false]
      decide +kernel
    · by_cases jv : j=v
      · subst j
        simp only [ite_true,ite_false,decide_true,decide_false,ju,Ne.symm ju]
        decide +kernel
      · by_cases rest : j=s ∨ j=t
        all_goals simp only [ite_true,ite_false,ju,jv,Ne.symm ju,Ne.symm jv,rest,decide_false]
        all_goals decide +kernel
  | node d a b ia ib =>
    have ha := card_le a
    have hb := card_le b
    change (sig a).2+(sig b).2≤((sig a).1∪(sig b).1).card at tight
    have upper := Finset.card_union_le (sig a).1 (sig b).1
    have dis := Finset.card_union_eq_card_add_card.mp (show ((sig a).1∪(sig b).1).card =
        (sig a).1.card+(sig b).1.card by omega)
    have sep (k : Nat) : ¬(decide (k∈(sig a).1)=true ∧ decide (k∈(sig b).1)=true) := by
      rintro ⟨ak,bk⟩
      exact Finset.disjoint_left.mp dis (of_decide_eq_true ak) (of_decide_eq_true bk)
    have p := closure _ _ _ _ (sep u) (sep v) _ (ia (by omega)) _ (ib (by omega))
    have eq : word u v s t (.node d a b)=
        (if d then word u v s t a &&& word u v s t b else word u v s t a ||| word u v s t b) :=
      pack_op _ d _ _
    rw [eq]
    have decOr (A B : Prop) [Decidable A] [Decidable B] : decide (A ∨ B) = (decide A || decide B) := by by_cases h : A <;> simp [h]
    simp only [sig,join,Finset.mem_union,decOr]
    cases d
    · exact p.2
    · exact p.1

#print axioms word_bound
end IncidenceBudget
