import ReadOneThreeSides
namespace IncidenceCover.Three
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem replacement_cover {P L} {E : Finset (Fin P × Fin L)} {C : Circuit}
    (r : rectangleFree E) (h : replacement E C) : Cover E C.size := by
  obtain ⟨D,da,dw,sz,read⟩ := h
  obtain ⟨A,B,hit,bd⟩ := PEqualNP.Outside.L_meta_4897 _ _ E D r da dw read
  exact ⟨A,B,hit,by omega⟩

theorem active_columns {P L} (E : Finset (Fin P × Fin L)) (C : Circuit)
    (r : rectangleFree E) (ao : IsAO2 (P+L) C) (w : computes E C)
    (small : (E.image Prod.snd).card≤3) : replacement E C := by
  classical
  let S := E.image Prod.snd
  let e := Fintype.equivFin (↑S)
  have card : Fintype.card (↑S) ≤ 3 := by rw [Fintype.card_coe]; exact small
  let f : Fin L → Fin 3 := fun l => if h : l∈S then Fin.castLE card (e ⟨l,h⟩) else 0
  have inj : Set.InjOn f (↑S : Set (Fin L)) := by
    intro a ha b hb eq
    change a∈S at ha
    change b∈S at hb
    have vals := congrArg Fin.val eq
    simp only [f,dite_eq_left ha,dite_eq_left hb,Fin.val_castLE] at vals
    exact congrArg Subtype.val (e.injective (Fin.ext vals))
  let pack : Fin P × Fin L → Fin P × Fin 3 := fun x => (x.1,f x.2)
  let F := E.image pack
  have active {p l} (h : (p,l)∈E) : l∈S := Finset.mem_image_of_mem Prod.snd h
  have decode (p : Fin P) (j : Fin 3) : (p,j)∈F ↔ ∃ l,(p,l)∈E ∧ f l=j := by
    constructor
    · intro h
      obtain ⟨⟨a,b⟩,he,eq⟩ := Finset.mem_image.mp h
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (show (a,f b)=(p,j) from eq)
      exact ⟨_,he,rfl⟩
    · rintro ⟨a,h,rfl⟩
      exact Finset.mem_image_of_mem pack h
  have rf : rectangleFree F := by
    intro p q j k pq jk h
    obtain ⟨a,pa,aj⟩ := (decode _ _).mp h.1
    obtain ⟨b,pb,bk⟩ := (decode _ _).mp h.2.1
    obtain ⟨a',qa',aj'⟩ := (decode _ _).mp h.2.2.1
    obtain ⟨b',qb',bk'⟩ := (decode _ _).mp h.2.2.2
    have aa := inj (active pa) (active qa') (aj.trans aj'.symm)
    have bb := inj (active pb) (active qb') (bk.trans bk'.symm)
    exact r _ _ _ _ pq (fun eq => jk (aj.symm.trans ((congrArg f eq).trans bk)))
      ⟨pa,pb,aa ▸ qa',bb ▸ qb'⟩
  let σ : Fin (P+L) → Fin (P+3) := Fin.addCases (Fin.castAdd 3) (fun l => Fin.natAdd P (f l))
  let Z := renameCircuit (resize σ) C
  have zw : computes F Z := by
    intro z
    change circuitFun _ (renameCircuit (resize σ) C) z=_
    rw [resize_eval,w]
    congr 1
    apply propext
    constructor
    · rintro ⟨p,l,h,hp,hl⟩
      exact ⟨p,f l,(decode _ _).mpr ⟨l,h,rfl⟩,by simpa [σ] using hp,by simpa [σ] using hl⟩
    · rintro ⟨p,j,h,hp,hj⟩
      obtain ⟨l,hl,rfl⟩ := (decode _ _).mp h
      exact ⟨p,l,hl,by simpa [σ] using hp,by simpa [σ] using hj⟩
  obtain ⟨A,B,hit,budget⟩ := replacement_cover rf (three_side F Z rf (resize_ao _ _ ao) zw (Or.inr le_rfl))
  let B' := S.filter (fun l => f l∈B)
  have boundB : B'.card≤B.card := by
    exact Finset.card_le_card_of_injOn f (fun i hi => (Finset.mem_filter.mp hi).2)
      (fun a ha b hb eq => inj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 eq)
  have packInj : Set.InjOn pack (↑E : Set (Fin P × Fin L)) := by
    rintro ⟨p,l⟩ pl ⟨q,m⟩ qm eq
    exact Prod.ext (congrArg (fun x : Fin P × Fin 3 => x.1) eq)
      (inj (active pl) (active qm) (congrArg (fun x : Fin P × Fin 3 => x.2) eq))
  have ef : F.card=E.card := Finset.card_image_of_injOn packInj
  have same : Z.size=C.size := size_rename _ _
  apply from_cover A B'
  · rintro ⟨p,l⟩ he
    rcases hit (p,f l) ((decode _ _).mpr ⟨l,he,rfl⟩) with ha|hb
    · exact Or.inl ha
    · exact Or.inr (Finset.mem_filter.mpr ⟨active he,hb⟩)
  · omega

#print axioms active_columns
end IncidenceCover.Three
