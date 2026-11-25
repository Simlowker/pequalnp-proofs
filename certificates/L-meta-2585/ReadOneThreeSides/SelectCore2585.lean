import ColumnProfiles2585
namespace IncidenceCover.Profiles
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

set_option maxRecDepth 32000 in
theorem select_core {L : Nat} (E : Finset (Fin 3 × Fin L)) (rect : rectangleFree E) :
    (∃ A : Finset (Fin 3),∃ B : Finset (Fin L), A.card+B.card≤2 ∧ ∀ e∈E,e.1∈A ∨ e.2∈B) ∨
    (∃ sel : Fin 3 → Fin L, Function.Injective sel ∧ (∀ i,(i,sel i)∈E) ∧
      ∀ l, (¬∃ i,sel i=l) → ∀ p q,(p,l)∈E → (q,l)∈E → p=q) := by
  classical
  let T := types E
  have src (t : T) : ∃ l, signature E l=t.val := by
    obtain ⟨l,_,eq⟩ := Finset.mem_image.mp t.property
    exact ⟨l,eq⟩
  let rep : T → Fin L := fun t => (src t).choose
  have spec (t : T) : signature E (rep t)=t.val := (src t).choose_spec
  have member (l : Fin L) : signature E l∈T := Finset.mem_image_of_mem _ (Finset.mem_univ l)
  have ok := table T
  cases h : plan T with
  | invalid =>
    rw [h] at ok
    exact False.elim (ok (types_possible rect))
  | small a b =>
    rw [h] at ok
    obtain ⟨bound,sh,cover⟩ := ok
    let B := part 8 b
    let f : B → Fin L := fun t => rep ⟨t.val,(sh t.val t.property).1⟩
    left
    refine ⟨part 3 a,B.attach.image f,?_,?_⟩
    · have le := Finset.card_image_le (s:=B.attach) (f:=f)
      rw [Finset.card_attach] at le
      change (part 3 a).card+B.card≤2 at bound
      omega
    · rintro ⟨p,l⟩ e
      rcases cover _ (member l) p ((sig_has _ _ _).mpr e) with ha|hb
      · exact Or.inl ha
      right
      let t : B := ⟨signature E l,hb⟩
      have eq : signature E (f t)=signature E l := spec _
      have forced := unique_shared rect eq ((eq.symm) ▸ (sh _ hb).2)
      exact Finset.mem_image.mpr ⟨t,Finset.mem_attach _ _,forced⟩
  | core f =>
    rw [h] at ok
    obtain ⟨good,distinct,all⟩ := ok
    let sel : Fin 3 → Fin L := fun i => rep ⟨pick f i,(good i).1⟩
    have sig (i : Fin 3) : signature E (sel i)=pick f i := spec _
    right
    refine ⟨sel,?_,?_,?_⟩
    · intro i j eq
      exact distinct _ _ ((sig i).symm.trans ((congrArg (signature E) eq).trans (sig j)))
    · intro i
      exact (sig_has _ _ _).mp ((sig i).symm ▸ (good i).2)
    · intro l missed p q hp hq
      by_contra pq
      have sh : shared (signature E l) := ⟨p,q,pq,(sig_has _ _ _).mpr hp,(sig_has _ _ _).mpr hq⟩
      obtain ⟨i,eq⟩ := all _ (member l) sh
      have same := (sig i).trans eq
      exact missed ⟨i,unique_shared rect same (same.symm ▸ sh)⟩

#print axioms select_core
end IncidenceCover.Profiles
