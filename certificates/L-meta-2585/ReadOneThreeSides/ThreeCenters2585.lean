import LeafTwins2585
namespace IncidenceCover.Three
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity

theorem one_point_two_lines {P L} {E : Finset (Fin P × Fin L)} (C : Circuit)
    (rect : rectangleFree E) (ao : IsAO2 (P+L) C) (works : computes E C)
    (p : Fin P) (B : Finset (Fin L)) (small : B.card≤2)
    (hit : ∀ e∈E, e.1=p ∨ e.2∈B) : replacement E C := by
  classical
  let T := E.image Prod.snd
  by_cases sub : T⊆B
  · apply active_columns E C rect ao works
    exact (Finset.card_le_card sub).trans (by omega)
  obtain ⟨l,active,lb⟩ := Finset.not_subset.mp sub
  let S := (T \ B).erase l
  have leaf {j} (act : j∈T) (out : j∉B) : sole E p j := by
    obtain ⟨⟨q,i⟩,e,eq⟩ := Finset.mem_image.mp act
    change i=j at eq; subst i
    have qp : q=p := (hit _ e).resolve_right out
    exact ⟨qp ▸ e,fun a aj => (hit _ aj).resolve_right out⟩
  apply lift_twin_leaves E C rect ao works p l S (Finset.notMem_erase _ _) (leaf active lb)
    (fun j h => leaf (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase h)).1
      (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase h)).2)
  intro D da dw
  let F := E.filter (fun e => e.2∉S)
  have rf : rectangleFree F := rectangle_subset rect (Finset.filter_subset _ _)
  apply active_columns F D rf da dw
  have bounds : F.image Prod.snd ⊆ insert l B := by
    intro j hj
    obtain ⟨⟨q,b⟩,qe,eq⟩ := Finset.mem_image.mp hj
    change b=j at eq; subst b
    obtain ⟨ed,kept⟩ := Finset.mem_filter.mp qe
    by_contra missing
    have out : j≠l ∧ j∉B := by simpa using missing
    apply kept
    exact Finset.mem_erase.mpr ⟨out.1,Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem Prod.snd ed,out.2⟩⟩
  have cap := Finset.card_le_card bounds
  rw [Finset.card_insert_of_notMem lb] at cap
  omega

theorem three_centers {P L} (E : Finset (Fin P × Fin L)) (C : Circuit)
    (r : rectangleFree E) (ao : IsAO2 (P+L) C) (w : computes E C)
    (A : Finset (Fin P)) (B : Finset (Fin L)) (small : A.card+B.card≤3)
    (hit : ∀ e∈E,e.1∈A ∨ e.2∈B) : replacement E C := by
  classical
  by_cases ea : A=∅
  · subst A
    apply active_columns E C r ao w
    have sub : E.image Prod.snd⊆B := by
      intro j hj; obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hj; simpa using hit e he
    exact (Finset.card_le_card sub).trans (by simpa using small)
  by_cases eb : B=∅
  · subst B
    apply unswap_replacement r ao w
    intro Z za zw
    apply active_columns _ Z (rect_flip r) za zw
    rw [flip_right]
    have sub : E.image Prod.fst⊆A := by
      intro i hi; obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi; simpa using hit e he
    exact (Finset.card_le_card sub).trans (by simpa using small)
  have posA := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr ea)
  have posB := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr eb)
  by_cases ap : A.card=1
  · obtain ⟨p,rfl⟩ := Finset.card_eq_one.mp ap
    apply one_point_two_lines C r ao w p B (by simp at small; omega)
    simpa using hit
  · obtain ⟨l,rfl⟩ := Finset.card_eq_one.mp (show B.card=1 by omega)
    apply unswap_replacement r ao w
    intro Z za zw
    apply one_point_two_lines Z (rect_flip r) za zw l A (by simp at small; omega)
    rintro ⟨j,i⟩ h
    simpa using (hit (i,j) (flip_mem.mp h)).symm

theorem posted_three_centers (P L : Nat) (I : Fin P → Fin L → Prop) [DecidableRel I] (C : Circuit)
    (rect : ∀ p p' l l',p≠p' → l≠l' → ¬(I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (ao : IsAO2 (P+L) C) (w : ∀ z,circuitFun (P+L) C z =
      decide (∃ p l,I p l ∧ z (Fin.castAdd L p)=true ∧ z (Fin.natAdd P l)=true))
    (A : Finset (Fin P)) (B : Finset (Fin L)) (small : A.card+B.card≤3)
    (hit : ∀ p l,I p l → p∈A ∨ l∈B) :
    ∃ D : Circuit, IsAO2 (P+L) D ∧ (∀ z,circuitFun (P+L) D z =
      decide (∃ p l,I p l ∧ z (Fin.castAdd L p)=true ∧ z (Fin.natAdd P l)=true)) ∧
      D.size≤C.size ∧ PEqualNP.ReadK.IsReadK (P+L) D 1 := by
  let E := Finset.univ.filter (fun e : Fin P × Fin L => I e.1 e.2)
  have r : rectangleFree E := by simpa [E,rectangleFree] using rect
  have correct : computes E C := by simpa [E,computes] using w
  have covered : ∀ e∈E,e.1∈A ∨ e.2∈B := by
    rintro ⟨p,l⟩ he; exact hit p l (by simpa [E] using he)
  simpa [E,replacement,computes] using three_centers E C r ao correct A B small covered
#print axioms posted_three_centers
end IncidenceCover.Three
