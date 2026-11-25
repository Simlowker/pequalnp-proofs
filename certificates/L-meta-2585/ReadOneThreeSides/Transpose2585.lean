import AllThreeRows2585
namespace IncidenceCover.Three
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem swap_instance {P L : Nat} {E : Finset (Fin P × Fin L)} {C : Circuit}
    (ao : IsAO2 (P+L) C) (correct : computes E C) :
    ∃ Z : Circuit, IsAO2 (L+P) Z ∧ computes (flip E) Z ∧ Z.size=C.size := by
  let σ : Fin (P+L) → Fin (L+P) := Fin.addCases (Fin.natAdd L) (Fin.castAdd P)
  refine ⟨renameCircuit (resize σ) C,resize_ao σ C ao,?_,size_rename _ _⟩
  intro z
  rw [resize_eval,correct]
  congr 1
  apply propext
  constructor
  · rintro ⟨p,l,h,hp,hl⟩
    exact ⟨l,p,flip_mem.mpr h,by simpa [σ] using hl,by simpa [σ] using hp⟩
  · rintro ⟨l,p,h,hl,hp⟩
    exact ⟨p,l,flip_mem.mp h,by simpa [σ] using hp,by simpa [σ] using hl⟩

theorem unswap_replacement {P L} {E : Finset (Fin P × Fin L)} {C : Circuit}
    (rect : rectangleFree E) (ao : IsAO2 (P+L) C) (correct : computes E C)
    (other : ∀ Z : Circuit, IsAO2 (L+P) Z → computes (flip E) Z → replacement (flip E) Z) :
    replacement E C := by
  obtain ⟨Z,za,zw,same⟩ := swap_instance ao correct
  obtain ⟨D,da,dw,sz,read⟩ := other Z za zw
  obtain ⟨A,B,hit,bd⟩ := PEqualNP.Outside.L_meta_4897 L P _ D (rect_flip rect) da dw read
  have cov : Cover (flip E) C.size := ⟨A,B,hit,by omega⟩
  obtain ⟨B',A',hit',bd'⟩ := cover_unflip cov
  exact from_cover B' A' hit' bd'

#print axioms swap_instance
#print axioms unswap_replacement
end IncidenceCover.Three
