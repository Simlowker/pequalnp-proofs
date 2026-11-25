import ActiveSide2585
namespace IncidenceCover.Three
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

def sole {P L} (E : Finset (Fin P × Fin L)) (p : Fin P) (l : Fin L) :=
  (p,l)∈E ∧ ∀ q, (q,l)∈E → q=p

theorem rectangle_subset {P L} {E F : Finset (Fin P × Fin L)}
    (r : rectangleFree E) (sub : F⊆E) : rectangleFree F :=
  fun _ _ _ _ pq lm h => r _ _ _ _ pq lm ⟨sub h.1, sub h.2.1, sub h.2.2.1, sub h.2.2.2⟩

theorem leaf_count {P L} {E : Finset (Fin P × Fin L)} {p : Fin P} (S : Finset (Fin L))
    (leaves : ∀ l∈S, sole E p l) : E.card=(E.filter fun e => e.2∉S).card+S.card := by
  let removed := E.filter (fun e => e.2∈S)
  have map_eq : removed.image Prod.snd=S := by
    ext l
    constructor
    · intro h
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp he).2
    · intro h
      exact Finset.mem_image_of_mem Prod.snd (Finset.mem_filter.mpr ⟨(leaves _ h).1,h⟩ : (p,l)∈removed)
  have inj : Set.InjOn Prod.snd (↑removed : Set (Fin P × Fin L)) := by
    rintro ⟨q,l⟩ ql ⟨a,j⟩ aj eq
    change l=j at eq; subst j
    obtain ⟨qe,ls⟩ := Finset.mem_filter.mp ql
    exact Prod.ext (((leaves l ls).2 _ qe).trans (((leaves l ls).2 _ (Finset.mem_filter.mp aj).1).symm)) rfl
  have count := Finset.card_image_of_injOn inj
  rw [map_eq] at count
  have split := Finset.card_filter_add_card_filter_not (s:=E) (fun e => e.2∈S)
  change removed.card+_=E.card at split
  omega

theorem lift_twin_leaves {P L} (E : Finset (Fin P × Fin L)) (C : Circuit)
    (rect : rectangleFree E) (ao : IsAO2 (P+L) C) (works : computes E C)
    (p : Fin P) (l : Fin L) (S : Finset (Fin L)) (kept : l∉S)
    (anchor : sole E p l) (leaves : ∀ j∈S,sole E p j)
    (core : ∀ D : Circuit, IsAO2 (P+L) D → computes (E.filter fun e => e.2∉S) D →
      replacement (E.filter fun e => e.2∉S) D) : replacement E C := by
  classical
  let F := E.filter (fun e => e.2∉S)
  have e0 : (p,l)∈F := Finset.mem_filter.mpr ⟨anchor.1,kept⟩
  obtain ⟨D,da,saved,dw⟩ := prune_columns S ao works (fun j hj => ⟨p,(leaves j hj).1⟩) ⟨_,e0⟩
  obtain ⟨A,B,hit,bd⟩ := replacement_cover (rectangle_subset rect (Finset.filter_subset _ _)) (core D da dw)
  change F.card+A.card+B.card ≤ D.size+1 at bd
  have count : E.card=F.card+S.card := leaf_count S leaves
  by_cases has : p∈A
  · apply from_cover A B
    · rintro ⟨q,j⟩ e
      by_cases inS : j∈S
      · exact Or.inl ((leaves j inS).2 q e ▸ has)
      · exact hit _ (Finset.mem_filter.mpr ⟨e,inS⟩)
    · omega
  · have lb : l∈B := (hit (p,l) e0).resolve_left has
    apply from_cover (insert p A) (B.erase l)
    · rintro ⟨q,j⟩ e
      by_cases qp : q=p
      · exact Or.inl (Finset.mem_insert.mpr (Or.inl qp))
      have no : j∉S := fun hj => qp ((leaves j hj).2 _ e)
      have ne : j≠l := by rintro rfl; exact qp (anchor.2 _ e)
      rcases hit (q,j) (Finset.mem_filter.mpr ⟨e,no⟩) with qa|jb
      · exact Or.inl (Finset.mem_insert_of_mem qa)
      · exact Or.inr (Finset.mem_erase.mpr ⟨ne,jb⟩)
    · have cnt := Finset.card_erase_add_one lb
      rw [Finset.card_insert_of_notMem has]; omega

#print axioms lift_twin_leaves
end IncidenceCover.Three
