import OneOverlap2585
namespace IncidenceCover
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

def Cover {P L : ℕ} (E : Finset (Fin P × Fin L)) (k : ℕ) :=
  ∃ A : Finset (Fin P), ∃ B : Finset (Fin L),
    (∀ e∈E,e.1∈A ∨ e.2∈B) ∧ E.card+A.card+B.card≤k+1

structure Budget {P L : ℕ} (E : Finset (Fin P × Fin L)) (k : ℕ) : Prop where
  support : (E.image Prod.fst).card+(E.image Prod.snd).card≤k+1
  path : ∀ {p q : Fin P} {l m : Fin L}, (p,l)∈E → (p,m)∈E → (q,l)∈E →
    m≠l → q≠p → (q,m)∉E → (E.image Prod.fst).card+(E.image Prod.snd).card≤k

theorem circuit_budget {P L} {E : Finset (Fin P × Fin L)} {C : Circuit}
    (ao : IsAO2 (P+L) C) (works : computes E C) : Budget E C.size :=
  ⟨support_bound ao works,fun e f g mp qp diag => path_bound ao works e f g mp qp diag⟩

theorem one_extra_cover {P L k} {E : Finset (Fin P × Fin L)}
    (rect : rectangleFree E) (bounds : Budget E k)
    (extra : E.card≤(E.image Prod.snd).card+1) : Cover E k := by
  classical
  by_cases share : ∃ p q l, p≠q ∧ (p,l)∈E ∧ (q,l)∈E
  swap
  · refine ⟨E.image Prod.fst,∅,fun e he => Or.inl (Finset.mem_image_of_mem _ he),?_⟩
    have eq := Finset.card_image_of_injOn (with_distinct_columns E share)
    have b := bounds.support
    simp only [Finset.card_empty,Nat.add_zero]
    omega
  obtain ⟨p,q,l,pq,pl,ql⟩ := share
  let A := E.image Prod.fst
  have pa : p∈A := Finset.mem_image_of_mem Prod.fst pl
  have qa : q∈A := Finset.mem_image_of_mem Prod.fst ql
  have row (i j : Fin P) (ne : i≠j) (il : (i,l)∈E) (jl : (j,l)∈E)
      (other : ∃ m, m≠l ∧ (i,m)∈E) : Cover E k := by
    obtain ⟨m,ml,im⟩ := other
    have diag : (j,m)∉E := fun jm => rect i j l m ne ml.symm ⟨il,im,jl,jm⟩
    have budget := bounds.path il im jl ml ne.symm diag
    refine ⟨E.image Prod.fst, ∅, fun a ha => Or.inl (Finset.mem_image_of_mem _ ha), ?_⟩
    simp only [Finset.card_empty, Nat.add_zero]
    omega
  by_cases op : ∃ m, m≠l ∧ (p,m)∈E
  · exact row p q pq pl ql op
  by_cases oq : ∃ m, m≠l ∧ (q,m)∈E
  · exact row q p pq.symm ql pl oq
  refine ⟨(A.erase p).erase q,{l},?_,?_⟩
  · rintro ⟨i,j⟩ he
    by_cases jl : j=l
    · exact Or.inr (by simpa)
    · left
      have ip : i≠p := by rintro rfl; exact op ⟨j,jl,he⟩
      have iq : i≠q := by rintro rfl; exact oq ⟨j,jl,he⟩
      exact Finset.mem_erase.mpr ⟨iq,Finset.mem_erase.mpr ⟨ip,Finset.mem_image_of_mem Prod.fst he⟩⟩
  · have eq1 := Finset.card_erase_add_one pa
    have eq2 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨pq.symm,qa⟩ : q∈A.erase p)
    have budget := bounds.support
    change A.card+_≤_ at budget
    simp only [Finset.card_singleton]
    omega


def flip {P L} (E : Finset (Fin P × Fin L)) := E.map (Equiv.prodComm _ _).toEmbedding

@[simp] theorem flip_mem {P L} {E : Finset (Fin P × Fin L)} {p l} :
    (l,p)∈flip E ↔ (p,l)∈E := by simp [flip]
@[simp] theorem flip_card {P L} (E : Finset (Fin P × Fin L)) : (flip E).card=E.card := by simp [flip]
@[simp] theorem flip_left {P L} (E : Finset (Fin P × Fin L)) :
    (flip E).image Prod.fst=E.image Prod.snd := by
  ext a
  simp only [Finset.mem_image,Prod.exists,flip_mem]
  aesop
@[simp] theorem flip_right {P L} (E : Finset (Fin P × Fin L)) :
    (flip E).image Prod.snd=E.image Prod.fst := by
  ext a
  simp only [Finset.mem_image,Prod.exists,flip_mem]
  aesop

theorem rect_flip {P L} {E : Finset (Fin P × Fin L)} (r : rectangleFree E) : rectangleFree (flip E) := by
  intro l m p q lm pq h
  simp only [flip_mem] at h
  exact r p q l m pq lm ⟨h.1,h.2.2.1,h.2.1,h.2.2.2⟩

theorem budget_flip {P L k} {E : Finset (Fin P × Fin L)} (b : Budget E k) : Budget (flip E) k := by
  refine ⟨by simpa [Nat.add_comm] using b.support,?_⟩
  intro l m p q e f g qp ml diag
  simp only [flip_mem] at e f g diag
  simpa [Nat.add_comm] using b.path e g f ml qp diag

theorem cover_unflip {P L k} {E : Finset (Fin P × Fin L)} (h : Cover (flip E) k) : Cover E k := by
  obtain ⟨B,A,hit,bound⟩ := h
  refine ⟨A,B,?_,?_⟩
  · rintro ⟨p,l⟩ e
    exact (hit (l,p) (flip_mem.mpr e)).symm
  · rw [flip_card] at bound; omega

theorem symmetric_case {P L} {E : Finset (Fin P × Fin L)} {C : Circuit}
    (rect : rectangleFree E) (ao : IsAO2 (P+L) C) (works : computes E C)
    (easy : E.card≤(E.image Prod.snd).card+1 ∨ E.card≤(E.image Prod.fst).card+1 ∨
        (E.image Prod.fst).card≤2 ∨ (E.image Prod.snd).card≤2) : replacement E C := by
  have b := circuit_budget ao works
  suffices h : Cover E C.size by obtain ⟨A,B,hit,bd⟩ := h; exact from_cover A B hit bd
  rcases easy with h|h|h|h
  · exact one_extra_cover rect b h
  · exact cover_unflip (one_extra_cover (rect_flip rect) (budget_flip b) (by simpa using h))
  · exact one_extra_cover rect b (two_rows_extra E rect h)
  · exact cover_unflip (one_extra_cover (rect_flip rect) (budget_flip b)
      (two_rows_extra _ (rect_flip rect) (by simpa using h)))

#print axioms symmetric_case
end IncidenceCover
