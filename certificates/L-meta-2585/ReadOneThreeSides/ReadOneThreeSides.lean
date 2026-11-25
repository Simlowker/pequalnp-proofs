import ThreeByThree2585
import Transpose2585

namespace IncidenceCover.Three
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem three_side {P L : Nat} (E : Finset (Fin P × Fin L)) (C : Circuit)
    (r : rectangleFree E) (ao : IsAO2 (P+L) C) (w : computes E C) (side : P≤3 ∨ L≤3) :
    replacement E C := by
  rcases side with p|l
  · rcases Nat.lt_or_eq_of_le p with small|rfl
    · apply small_cover r ao w Finset.univ ∅ (fun e _ => Or.inl (Finset.mem_univ e.1))
      simp only [Finset.card_univ,Fintype.card_fin,Finset.card_empty,Nat.add_zero]
      omega
    · exact all_rows_of_three three_by_three E C r ao w
  · rcases Nat.lt_or_eq_of_le l with small|rfl
    · apply small_cover r ao w ∅ Finset.univ (fun e _ => Or.inr (Finset.mem_univ e.2))
      simp only [Finset.card_univ,Fintype.card_fin,Finset.card_empty,Nat.zero_add]
      omega
    · apply unswap_replacement r ao w
      exact fun Z za zw => all_rows_of_three three_by_three _ Z (rect_flip r) za zw

theorem posted_three_side (P L : Nat) (I : Fin P → Fin L → Prop) [DecidableRel I] (C : Circuit)
    (rect : ∀ p p' l l', p≠p' → l≠l' → ¬(I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (ao : IsAO2 (P+L) C) (w : ∀ z,circuitFun (P+L) C z =
      decide (∃ p l,I p l ∧ z (Fin.castAdd L p)=true ∧ z (Fin.natAdd P l)=true))
    (side : P≤3 ∨ L≤3) :
    ∃ D : Circuit, IsAO2 (P+L) D ∧ (∀ z,circuitFun (P+L) D z =
      decide (∃ p l,I p l ∧ z (Fin.castAdd L p)=true ∧ z (Fin.natAdd P l)=true)) ∧
      D.size≤C.size ∧ PEqualNP.ReadK.IsReadK (P+L) D 1 := by
  let E := Finset.univ.filter (fun e : Fin P × Fin L => I e.1 e.2)
  have r : rectangleFree E := by simpa [E,rectangleFree] using rect
  have good : computes E C := by simpa [E,computes] using w
  simpa [E,replacement,computes] using three_side E C r ao good side

#print axioms three_side
#print axioms posted_three_side
end IncidenceCover.Three
