import MixedCover2585
namespace IncidenceCover
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

theorem small_cover {P L} {E : Finset (Fin P × Fin L)} {C : Circuit}
    (rect : rectangleFree E) (ao : IsAO2 (P+L) C) (works : computes E C)
    (A : Finset (Fin P)) (B : Finset (Fin L)) (hit : ∀ e∈E, e.1∈A ∨ e.2∈B)
    (small : A.card+B.card≤2) : replacement E C := by
  classical
  by_cases ea : A=∅
  · subst A
    have sub : E.image Prod.snd ⊆ B := by
      intro l hl
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hl
      simpa using hit e he
    exact symmetric_case rect ao works (Or.inr (Or.inr (Or.inr ((Finset.card_le_card sub).trans (by simpa using small)))))
  by_cases eb : B=∅
  · subst B
    have sub : E.image Prod.fst ⊆ A := by
      intro p hp
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hp
      simpa using hit e he
    exact symmetric_case rect ao works (Or.inr (Or.inr (Or.inl ((Finset.card_le_card sub).trans (by simpa using small)))))
  have ap := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr ea)
  have bp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr eb)
  obtain ⟨p,rfl⟩ := Finset.card_eq_one.mp (show A.card=1 by omega)
  obtain ⟨l,rfl⟩ := Finset.card_eq_one.mp (show B.card=1 by omega)
  exact mixed_centers ao works p l (by simpa using hit)

theorem posted_small_cover (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit)
    (rect : ∀ p p' l l',p≠p' → l≠l' → ¬(I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (ao : IsAO2 (P+L) C) (works : ∀ z, PEqualNP.MetaComplexity.circuitFun (P+L) C z =
      decide (∃ p l,I p l ∧ z (Fin.castAdd L p)=true ∧ z (Fin.natAdd P l)=true))
    (A : Finset (Fin P)) (B : Finset (Fin L)) (hit : ∀ p l, I p l → p∈A ∨ l∈B)
    (small : A.card+B.card≤2) :
    ∃ D : Circuit, IsAO2 (P+L) D ∧
      (∀ z,PEqualNP.MetaComplexity.circuitFun (P+L) D z =
        decide (∃ p l,I p l ∧ z (Fin.castAdd L p)=true ∧ z (Fin.natAdd P l)=true)) ∧
      D.size≤C.size ∧ PEqualNP.ReadK.IsReadK (P+L) D 1 := by
  let E := Finset.univ.filter (fun e : Fin P × Fin L => I e.1 e.2)
  have r : rectangleFree E := by simpa [rectangleFree,E] using rect
  have w : computes E C := by simpa [computes,E] using works
  have h : ∀ e∈E,e.1∈A ∨ e.2∈B := by
    rintro ⟨p,l⟩ he
    exact hit p l (by simpa [E] using he)
  simpa [replacement,computes,E] using small_cover r ao w A B h small

#print axioms small_cover
#print axioms posted_small_cover
end IncidenceCover
