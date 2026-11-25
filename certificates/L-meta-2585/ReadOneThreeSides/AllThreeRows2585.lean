import CompressCore2585
import SelectCore2585
namespace IncidenceCover.Three
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem matched_budget {F : Finset (Fin 3 × Fin 3)} (r : rectangleFree F)
    (diag : ∀ i,(i,i)∈F) (Z : Circuit) (za : IsAO2 6 Z) (w : computes F Z)
    (rep : replacement F Z) : F.card+3 ≤ Z.size+1 := by
  obtain ⟨R,ra,rw,sz,read⟩ := rep
  obtain ⟨A,B,hit,cap⟩ := PEqualNP.Outside.L_meta_4897 3 3 F R r ra rw read
  have all : (Finset.univ : Finset (Fin 3))⊆A∪B := by
    intro i _
    exact Finset.mem_union.mpr (hit (i,i) (diag i))
  have h := (Finset.card_le_card all).trans (Finset.card_union_le A B)
  simp only [Finset.card_univ,Fintype.card_fin] at h
  omega

theorem all_rows_of_three (finite : ∀ {F : Finset (Fin 3 × Fin 3)} {Z : Circuit},
    rectangleFree F → IsAO2 6 Z → computes F Z → replacement F Z)
    {L} (E : Finset (Fin 3 × Fin L)) (C : Circuit)
    (rect : rectangleFree E) (ao : IsAO2 (3+L) C) (works : computes E C) : replacement E C := by
  classical
  rcases Profiles.select_core E rect with cov|big
  · obtain ⟨A,B,sz,hit⟩ := cov
    exact small_cover rect ao works A B hit sz
  obtain ⟨sel,inj,diagonal,single⟩ := big
  let S := removed E sel
  let F := coreEdges E sel
  have di (i) : (i,i)∈F := by simpa [F,coreEdges] using diagonal i
  have rf : rectangleFree F := by
    intro p q j k pq jk all
    simp only [F,coreEdges,Finset.mem_filter,Finset.mem_univ,true_and] at all
    exact rect p q (sel j) (sel k) pq (fun eq => jk (inj eq)) all
  have active (l) (hl : l∈S) : ∃ p,(p,l)∈E := by
    obtain ⟨⟨p,j⟩,h,eq⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hl).1
    exact ⟨p,(show j=l from eq) ▸ h⟩
  have keep : (E.filter fun e => e.2∉S).Nonempty := by
    refine ⟨(0,sel 0),Finset.mem_filter.mpr ⟨diagonal _,?_⟩⟩
    exact fun rm => (Finset.mem_sdiff.mp rm).2 (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  obtain ⟨D,da,saving,dw⟩ := prune_columns S ao works active keep
  obtain ⟨Z,za,zw,same⟩ := compress_selected sel inj D da dw
  have bound := matched_budget rf di Z za zw (finite rf za zw)
  have count : E.card=F.card+S.card := core_card E sel inj single
  apply from_cover Finset.univ ∅ (fun e _ => Or.inl (Finset.mem_univ _))
  simp only [Finset.card_univ,Fintype.card_fin,Finset.card_empty,Nat.add_zero]
  omega

#print axioms all_rows_of_three
end IncidenceCover.Three
