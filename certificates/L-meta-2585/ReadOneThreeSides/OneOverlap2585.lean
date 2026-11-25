import IncidenceCover2585

namespace IncidenceCover
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

def rectangleFree {P L} (E : Finset (Fin P × Fin L)) :=
  ∀ p q l m, p≠q → l≠m → ¬ ((p,l)∈E ∧ (p,m)∈E ∧ (q,l)∈E ∧ (q,m)∈E)

theorem with_distinct_columns {P L} (E : Finset (Fin P × Fin L))
    (h : ¬∃ p q l, p≠q ∧ (p,l)∈E ∧ (q,l)∈E) :
    Set.InjOn Prod.snd (↑E : Set (Fin P × Fin L)) := by
  rintro ⟨p,l⟩ hp ⟨q,m⟩ hq hm
  change l=m at hm
  subst m
  congr 1
  by_contra ne
  exact h ⟨p,q,l,ne,hp,hq⟩

theorem at_most_one_extra {P L} {E : Finset (Fin P × Fin L)} {C : Circuit}
    (rect : rectangleFree E) (ao : IsAO2 (P+L) C) (works : computes E C)
    (extra : E.card≤(E.image Prod.snd).card+1) : replacement E C := by
  classical
  by_cases share : ∃ p q l, p≠q ∧ (p,l)∈E ∧ (q,l)∈E
  swap
  · exact unique_columns ao works (with_distinct_columns E share)
  obtain ⟨p,q,l,pq,pl,ql⟩ := share
  let A := E.image Prod.fst
  have pa : p∈A := Finset.mem_image_of_mem Prod.fst pl
  have qa : q∈A := Finset.mem_image_of_mem Prod.fst ql
  have row (i j : Fin P) (ne : i≠j) (il : (i,l)∈E) (jl : (j,l)∈E)
      (other : ∃ m, m≠l ∧ (i,m)∈E) : replacement E C := by
    obtain ⟨m,ml,im⟩ := other
    have diag : (j,m)∉E := fun jm => rect i j l m ne ml.symm ⟨il,im,jl,jm⟩
    have budget := path_bound ao works il im jl ml ne.symm diag
    apply from_cover (E.image Prod.fst) ∅ (fun a ha => Or.inl (Finset.mem_image_of_mem _ ha))
    simp only [Finset.card_empty, Nat.add_zero]
    omega
  by_cases op : ∃ m, m≠l ∧ (p,m)∈E
  · exact row p q pq pl ql op
  by_cases oq : ∃ m, m≠l ∧ (q,m)∈E
  · exact row q p pq.symm ql pl oq
  apply from_cover ((A.erase p).erase q) {l}
  · rintro ⟨i,j⟩ he
    by_cases jl : j=l
    · exact Or.inr (by simpa)
    · left
      have ip : i≠p := by rintro rfl; exact op ⟨j,jl,he⟩
      have iq : i≠q := by rintro rfl; exact oq ⟨j,jl,he⟩
      exact Finset.mem_erase.mpr ⟨iq,Finset.mem_erase.mpr ⟨ip,Finset.mem_image_of_mem Prod.fst he⟩⟩
  · have eq1 := Finset.card_erase_add_one pa
    have eq2 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨pq.symm,qa⟩ : q∈A.erase p)
    have budget := support_bound ao works
    change A.card+_≤_ at budget
    simp only [Finset.card_singleton]
    omega

theorem two_rows_extra {P L} (E : Finset (Fin P × Fin L)) (rect : rectangleFree E)
    (two : (E.image Prod.fst).card≤2) :
    E.card ≤ (E.image Prod.snd).card+1 := by
  classical
  by_cases overlapping : ∃ p q l, p≠q ∧ (p,l)∈E ∧ (q,l)∈E
  swap
  · have eq := Finset.card_image_of_injOn (with_distinct_columns E overlapping)
    omega
  obtain ⟨p,q,l,pq,pl,ql⟩ := overlapping
  have eqRows : ({p,q} : Finset (Fin P))=E.image Prod.fst := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      rcases Finset.mem_insert.mp hi with ep|eq
      · exact ep ▸ Finset.mem_image_of_mem Prod.fst pl
      · exact (Finset.mem_singleton.mp eq) ▸ Finset.mem_image_of_mem Prod.fst ql
    · simpa [pq] using two
  have sides (i : Fin P) (m : Fin L) (h : (i,m)∈E) : i=p ∨ i=q := by
    have hi : i∈E.image Prod.fst := Finset.mem_image_of_mem Prod.fst h
    simpa [←eqRows] using hi
  let F := E.erase (p,l)
  have inj : Set.InjOn Prod.snd (↑F : Set (Fin P × Fin L)) := by
    apply with_distinct_columns
    rintro ⟨a,b,m,ab,am,bm⟩
    obtain ⟨an,ae⟩ := Finset.mem_erase.mp am
    obtain ⟨bn,be⟩ := Finset.mem_erase.mp bm
    have bad (pm : (p,m)∈E) (qm : (q,m)∈E) (ne : (p,m)≠(p,l)) : False :=
      rect p q l m pq (by rintro rfl; exact ne rfl) ⟨pl,pm,ql,qm⟩
    rcases sides a m ae with a_p|a_q <;> rcases sides b m be with b_p|b_q
    · exact ab (a_p.trans b_p.symm)
    · subst a; subst b; exact bad ae be an
    · subst a; subst b; exact bad be ae bn
    · exact ab (a_q.trans b_q.symm)
  have eq := Finset.card_image_of_injOn inj
  have le : (F.image Prod.snd).card ≤ (E.image Prod.snd).card :=
    Finset.card_le_card (Finset.image_mono Prod.snd (Finset.erase_subset _ _))
  have cnt := Finset.card_erase_add_one pl
  change F.card+1=E.card at cnt
  omega

theorem two_rows {L} (E : Finset (Fin 2 × Fin L)) (rect : rectangleFree E) (C : Circuit)
    (ao : IsAO2 (2+L) C) (works : computes E C) : replacement E C :=
  at_most_one_extra rect ao works (two_rows_extra E rect (by simpa using (Finset.card_le_univ (E.image Prod.fst))))

#print axioms at_most_one_extra
#print axioms two_rows
end IncidenceCover
