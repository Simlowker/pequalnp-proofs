import PruneColumns2585
import OneOverlap2585
namespace IncidenceCover.Profiles
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

def has (t : Fin 8) (p : Fin 3) := t.val.testBit p.val=true
def shared (t : Fin 8) := ∃ p q : Fin 3, p≠q ∧ has t p ∧ has t q
instance (t p) : Decidable (has t p) := by unfold has; infer_instance
instance (t) : Decidable (shared t) := by unfold shared; infer_instance
def signature (E : Finset (Fin 3 × Fin L)) (l : Fin L) : Fin 8 :=
    Fin.ofNat 8 ((if (0,l)∈E then 1 else 0)+(if (1,l)∈E then 2 else 0)+(if (2,l)∈E then 4 else 0))
theorem sig_has (E : Finset (Fin 3 × Fin L)) (p : Fin 3) (l : Fin L) :
    has (signature E l) p ↔ (p,l)∈E := by
  fin_cases p <;> by_cases a : (0,l)∈E <;> by_cases b : (1,l)∈E <;> by_cases c : (2,l)∈E <;>
    simp [signature,has,a,b,c] <;> decide
def types (E : Finset (Fin 3 × Fin L)) := Finset.univ.image (signature E)
theorem unique_shared {E : Finset (Fin 3 × Fin L)} (r : rectangleFree E) {l m : Fin L}
    (eq : signature E l=signature E m) (sh : shared (signature E l)) : l=m := by
  obtain ⟨p,q,pq,hp,hq⟩ := sh
  by_contra lm
  exact r p q l m pq lm ⟨(sig_has _ _ _).mp hp,(sig_has _ _ _).mp (eq ▸ hp),
    (sig_has _ _ _).mp hq,(sig_has _ _ _).mp (eq ▸ hq)⟩
def possible (T : Finset (Fin 8)) :=
  ∀ t∈T, ∀ u∈T, t≠u → ∀ p q : Fin 3,p≠q → ¬(has t p ∧ has t q ∧ has u p ∧ has u q)
theorem types_possible {E : Finset (Fin 3 × Fin L)} (rect : rectangleFree E) : possible (types E) := by
  intro t ht u hu ne p q pq h
  obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨m,_,rfl⟩ := Finset.mem_image.mp hu
  exact rect p q l m pq (fun eq => ne (congrArg _ eq))
    ⟨(sig_has _ _ _).mp h.1,(sig_has _ _ _).mp h.2.2.1,(sig_has _ _ _).mp h.2.1,(sig_has _ _ _).mp h.2.2.2⟩

def part (n a : Nat) := Finset.univ.filter (fun i : Fin n => a.testBit i.val)
def pick (a : Nat) (i : Fin 3) := Fin.ofNat 8 ((a >>> (3*i.val)) % 8)
inductive Plan where | invalid | small (rows cols : Nat) | core (indices : Nat)
def plans : Array Plan := #[
(.small 0 0),(.small 0 0),(.small 1 0),(.small 1 0),(.small 2 0),(.small 2 0),(.small 3 0),(.small 3 0),
(.small 0 8),(.small 0 8),(.small 1 8),(.small 1 8),(.small 2 8),(.small 2 8),(.small 3 0),(.small 3 0),
(.small 4 0),(.small 4 0),(.small 5 0),(.small 5 0),(.small 6 0),(.small 6 0),(.core 273),(.core 273),
(.small 4 8),(.small 4 8),(.core 281),(.core 281),(.core 275),(.core 275),(.core 281),(.core 281),
(.small 0 32),(.small 0 32),(.small 1 32),(.small 1 32),(.small 2 32),(.small 2 32),(.core 337),(.core 337),
(.small 0 40),(.small 0 40),(.core 345),(.core 345),(.core 339),(.core 339),(.core 345),(.core 345),
(.small 4 32),(.small 4 32),(.small 5 0),(.small 5 0),(.core 277),(.core 277),(.core 337),(.core 337),
(.core 285),(.core 285),(.core 345),(.core 345),(.core 339),(.core 339),(.core 345),(.core 345),
(.small 0 64),(.small 0 64),(.small 1 64),(.small 1 64),(.small 2 64),(.small 2 64),(.core 401),(.core 401),
(.small 0 72),(.small 0 72),(.core 409),(.core 409),(.core 403),(.core 403),(.core 409),(.core 409),
(.small 4 64),(.small 4 64),(.core 305),(.core 305),(.small 6 0),(.small 6 0),(.core 401),(.core 401),
(.core 307),(.core 307),(.core 409),(.core 409),(.core 403),(.core 403),(.core 409),(.core 409),
(.small 0 96),(.small 0 96),(.core 369),(.core 369),(.core 405),(.core 405),(.core 369),(.core 369),
(.core 371),(.core 371),(.core 371),(.core 371),(.core 371),(.core 371),(.core 371),(.core 371),
(.core 309),(.core 309),(.core 369),(.core 369),(.core 405),(.core 405),(.core 369),(.core 369),
(.core 371),(.core 371),(.core 371),(.core 371),(.core 371),(.core 371),(.core 371),(.core 371),
(.small 0 128),(.small 0 128),(.small 1 128),(.small 1 128),(.small 2 128),(.small 2 128),(.core 465),(.core 465),
.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,
(.small 4 128),(.small 4 128),(.core 313),(.core 313),(.core 279),(.core 279),(.core 465),(.core 465),
.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,
.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,
.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,
.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,
.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,
.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,
.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,
.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,
.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,
.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,
.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,
.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,
.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid,.invalid]
def plan (T : Finset (Fin 8)) : Plan := plans[(∑ t∈T,2^t.val : Nat)]?.getD .invalid
def okay (T : Finset (Fin 8)) : Plan → Prop
  | .invalid => ¬possible T
  | .small r s => (part 3 r).card+(part 8 s).card≤2 ∧ (∀ t∈part 8 s, t∈T ∧ shared t) ∧
      ∀ t∈T,∀ p, has t p → p∈part 3 r ∨ t∈part 8 s
  | .core f => (∀ i, pick f i∈T ∧ has (pick f i) i) ∧
      (∀ i j,pick f i=pick f j → i=j) ∧ ∀ t∈T,shared t → ∃ i, pick f i=t
instance (T) (x) : Decidable (okay T x) := by
  cases x <;> unfold okay
  · unfold possible; infer_instance
  all_goals infer_instance
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem table : ∀ T : Finset (Fin 8),okay T (plan T) := by decide +kernel
#print axioms table
end IncidenceCover.Profiles
