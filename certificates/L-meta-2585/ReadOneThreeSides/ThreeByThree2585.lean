import ClassifyThree2585
import Pattern87
import Pattern94
import RupPart238_9

namespace IncidenceCover.Three
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

theorem certified : ∀ t, lowerCert t := by
  intro t
  cases t with
  | g87 => exact Pattern87.unsat
  | g94 => exact Pattern94.unsat
  | g238 => exact Pattern238.unsat

theorem three_by_three {E : Finset (Fin 3 × Fin 3)} {C : Circuit}
    (rect : rectangleFree E) (ao : IsAO2 6 C) (correct : computes E C) : replacement E C :=
  finished certified rect ao correct

theorem posted_three_by_three (I : Fin 3 → Fin 3 → Prop) [DecidableRel I] (C : Circuit)
    (rect : ∀ p p' l l', p≠p' → l≠l' → ¬(I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (ao : IsAO2 6 C) (works : ∀ z, PEqualNP.MetaComplexity.circuitFun 6 C z =
      decide (∃ p l, I p l ∧ z (Fin.castAdd 3 p)=true ∧ z (Fin.natAdd 3 l)=true)) :
    ∃ D : Circuit, IsAO2 6 D ∧ (∀ z, PEqualNP.MetaComplexity.circuitFun 6 D z =
      decide (∃ p l, I p l ∧ z (Fin.castAdd 3 p)=true ∧ z (Fin.natAdd 3 l)=true)) ∧
      D.size≤C.size ∧ PEqualNP.ReadK.IsReadK 6 D 1 := by
  let E := Finset.univ.filter (fun e : Fin 3 × Fin 3 => I e.1 e.2)
  have r : rectangleFree E := by simpa [E,rectangleFree] using rect
  have w : computes E C := by simpa [E,computes] using works
  simpa [E,replacement,computes] using three_by_three r ao w

#print axioms posted_three_by_three
end IncidenceCover.Three
