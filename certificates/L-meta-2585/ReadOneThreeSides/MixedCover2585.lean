import SymmetricCover2585

namespace IncidenceCover
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

theorem cross_count {P L} {E : Finset (Fin P × Fin L)} {p : Fin P} {l : Fin L}
    (hit : ∀ e∈E, e.1=p ∨ e.2=l) (pa : p∈E.image Prod.fst) (la : l∈E.image Prod.snd) :
    (E.erase (p,l)).card+2≤(E.image Prod.fst).card+(E.image Prod.snd).card := by
  classical
  let A := E.image Prod.fst
  let B := E.image Prod.snd
  let f : Fin P × Fin L → Fin P ⊕ Fin L := fun e => if e.1=p then .inr e.2 else .inl e.1
  have maps : ∀ e∈E.erase (p,l),f e∈(A.erase p).disjSum (B.erase l) := by
    rintro ⟨i,j⟩ he
    obtain ⟨ne,ij⟩ := Finset.mem_erase.mp he
    by_cases ip : i=p
    · subst i
      have jl : j≠l := by rintro rfl; exact ne rfl
      simpa [f] using (show j≠l ∧ j∈B from ⟨jl,Finset.mem_image_of_mem Prod.snd ij⟩)
    · simpa [f,ip] using (show i≠p ∧ i∈A from ⟨ip,Finset.mem_image_of_mem Prod.fst ij⟩)
  have inj : Set.InjOn f (↑(E.erase (p,l)) : Set (Fin P × Fin L)) := by
    rintro ⟨i,j⟩ he ⟨a,b⟩ hg eq
    have one := hit (i,j) (Finset.mem_of_mem_erase he)
    have two := hit (a,b) (Finset.mem_of_mem_erase hg)
    change i=p ∨ j=l at one
    change a=p ∨ b=l at two
    by_cases ip : i=p <;> by_cases ap : a=p <;> simp_all [f]
  have le := Finset.card_le_card_of_injOn f maps inj
  rw [Finset.card_disjSum] at le
  have one := Finset.card_erase_add_one pa
  have two := Finset.card_erase_add_one la
  change (E.erase (p,l)).card+2≤A.card+B.card
  change (A.erase p).card+1=A.card at one
  change (B.erase l).card+1=B.card at two
  omega

theorem mixed_centers {P L} {E : Finset (Fin P × Fin L)} {C : Circuit}
    (ao : IsAO2 (P+L) C) (works : computes E C) (p : Fin P) (l : Fin L)
    (hit : ∀ e∈E, e.1=p ∨ e.2=l) : replacement E C := by
  classical
  have b := circuit_budget ao works
  by_cases op : ∃ m, m≠l ∧ (p,m)∈E
  swap
  · apply from_cover ∅ {l}
    · rintro ⟨i,j⟩ e
      right
      rcases hit (i,j) e with eq|eq
      · change i=p at eq; subst i
        by_contra nope
        exact op ⟨j,by simpa using nope,e⟩
      · exact Finset.mem_singleton.mpr eq
    · have uniq : Set.InjOn Prod.fst (↑E : Set (Fin P × Fin L)) := by
        rintro ⟨i,j⟩ e ⟨a,b⟩ h eq
        change i=a at eq
        subst a
        have same (j : Fin L) (ij : (i,j)∈E) : j=l := by
          rcases hit (i,j) ij with ep|el
          · change i=p at ep; subst i; by_contra jl; exact op ⟨j,jl,ij⟩
          · exact el
        rw [same j e,same b h]
      have eq := Finset.card_image_of_injOn uniq
      by_cases em : E=∅
      · simp [em]
      · obtain ⟨e,he⟩ := Finset.nonempty_iff_ne_empty.mpr em
        have pos := Finset.card_pos.mpr ((Finset.nonempty_iff_ne_empty.mpr em).image Prod.snd)
        have bd := b.support
        simp only [Finset.card_empty,Finset.card_singleton,Nat.add_zero]
        omega
  obtain ⟨m,ml,pm⟩ := op
  by_cases oq : ∃ q, q≠p ∧ (q,l)∈E
  swap
  · apply unique_columns ao works
    rintro ⟨i,j⟩ he ⟨a,b⟩ hg eq
    change j=b at eq
    subst b
    have same (a : Fin P) (aj : (a,j)∈E) : a=p := by
      rcases hit (a,j) aj with ep|el
      · exact ep
      · change j=l at el; subst j; by_contra ap; exact oq ⟨a,ap,aj⟩
    rw [same i he,same a hg]
  obtain ⟨q,qp,ql⟩ := oq
  have count := cross_count hit (Finset.mem_image_of_mem Prod.fst pm) (Finset.mem_image_of_mem Prod.snd ql)
  apply from_cover {p} {l}
  · exact fun e he => by simpa using hit e he
  · simp only [Finset.card_singleton]
    by_cases center : (p,l)∈E
    · have diag : (q,m)∉E := fun e => (hit (q,m) e).elim qp ml
      have bd := b.path center pm ql ml qp diag
      have eq := Finset.card_erase_add_one center
      omega
    · rw [Finset.erase_eq_of_notMem center] at count
      have bd := b.support
      omega

#print axioms mixed_centers
end IncidenceCover
