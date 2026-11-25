import ResizeInputs2585
import PruneColumns2585
namespace IncidenceCover.Three
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def coreEdges {L : Nat} (E : Finset (Fin 3 × Fin L)) (sel : Fin 3 → Fin L) :=
  Finset.univ.filter (fun e : Fin 3 × Fin 3 => (e.1,sel e.2)∈E)
def removed {L : Nat} (E : Finset (Fin 3 × Fin L)) (sel : Fin 3 → Fin L) :=
  (E.image Prod.snd) \ (Finset.univ.image sel)

theorem core_card {L : Nat} (E : Finset (Fin 3 × Fin L)) (sel : Fin 3 → Fin L)
    (inj : Function.Injective sel)
    (single : ∀ l,(¬∃ i,sel i=l) → ∀ p q,(p,l)∈E → (q,l)∈E → p=q) :
    E.card=(coreEdges E sel).card+(removed E sel).card := by
  classical
  let S := removed E sel
  let dropped := E.filter (fun e => e.2∈S)
  let kept := E.filter (fun e => e.2∉S)
  have seq (e : Fin 3 × Fin L) (he : e∈E) : e.2∈S ↔ ¬∃ i,sel i=e.2 := by
    have active : e.2∈E.image Prod.snd := Finset.mem_image_of_mem _ he
    simp [S,removed,active]
  have snd_inj : Set.InjOn Prod.snd (↑dropped : Set (Fin 3 × Fin L)) := by
    rintro ⟨p,l⟩ ha ⟨q,j⟩ hb eq
    change l=j at eq
    subst j
    obtain ⟨pe,pl⟩ := Finset.mem_filter.mp ha
    obtain ⟨qe,_⟩ := Finset.mem_filter.mp hb
    exact Prod.ext (single l ((seq _ pe).mp pl) _ _ pe qe) rfl
  have eqS : dropped.image Prod.snd=S := by
    ext l
    constructor
    · intro h
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp he).2
    · intro hl
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hl).1
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨he,hl⟩ : e∈dropped)
  have sizeD := Finset.card_image_of_injOn snd_inj
  rw [eqS] at sizeD
  let pack : Fin 3 × Fin 3 → Fin 3 × Fin L := fun x => (x.1,sel x.2)
  have pi : Function.Injective pack := fun a b eq => Prod.ext (congrArg (fun x : Fin 3 × Fin L => x.1) eq) (inj (congrArg (fun x : Fin 3 × Fin L => x.2) eq))
  have eqK : (coreEdges E sel).image pack=kept := by
    ext e
    constructor
    · intro he
      obtain ⟨⟨p,j⟩,h,rfl⟩ := Finset.mem_image.mp he
      have hp : (p,sel j)∈E := (Finset.mem_filter.mp h).2
      exact Finset.mem_filter.mpr ⟨hp,fun h => (seq _ hp).mp h ⟨j,rfl⟩⟩
    · intro h
      obtain ⟨he,hnot⟩ := Finset.mem_filter.mp h
      obtain ⟨j,hj⟩ := not_not.mp (fun q => hnot ((seq _ he).mpr q))
      refine Finset.mem_image.mpr ⟨(e.1,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,Prod.ext rfl hj⟩
      simpa [hj] using he
  have sizeK := Finset.card_image_of_injective (coreEdges E sel) pi
  rw [eqK] at sizeK
  have both := Finset.card_filter_add_card_filter_not (s:=E) (fun e => e.2∈S)
  change dropped.card+kept.card=E.card at both
  change E.card= _ + S.card
  omega

noncomputable def retract {L} (sel : Fin 3 → Fin L) (l : Fin L) : Fin 3 :=
  if hit : ∃ i,sel i=l then hit.choose else 0
theorem retract_sel {L} {sel : Fin 3 → Fin L} (inj : Function.Injective sel) (i : Fin 3) :
    retract sel (sel i)=i := by
  have ex : ∃ j,sel j=sel i := ⟨_,rfl⟩
  simp only [retract,dite_eq_left ex]
  exact inj ex.choose_spec

theorem compress_selected {L} {E : Finset (Fin 3 × Fin L)} (sel : Fin 3 → Fin L)
    (inj : Function.Injective sel) (D : Circuit) (ao : IsAO2 (3+L) D)
    (works : computes (E.filter fun e => e.2∉removed E sel) D) :
    ∃ Z : Circuit, IsAO2 6 Z ∧ computes (coreEdges E sel) Z ∧ Z.size=D.size := by
  classical
  let σ : Fin (3+L) → Fin 6 := Fin.addCases (Fin.castAdd 3) (fun l => Fin.natAdd 3 (retract sel l))
  refine ⟨renameCircuit (resize σ) D,resize_ao σ D ao,?_,size_rename _ _⟩
  intro z
  rw [resize_eval,works]
  congr 1
  apply propext
  constructor
  · rintro ⟨p,l,h,hp,hl⟩
    obtain ⟨he,kept⟩ := Finset.mem_filter.mp h
    have active : l∈E.image Prod.snd := Finset.mem_image_of_mem Prod.snd he
    have ex : ∃ j,sel j=l := by simpa [removed,active] using kept
    obtain ⟨j,rfl⟩ := ex
    exact ⟨p,j,by simpa [coreEdges] using he,by simpa [σ] using hp,by simpa [σ,retract_sel inj] using hl⟩
  · rintro ⟨p,j,h,hp,hl⟩
    have he : (p,sel j)∈E := (Finset.mem_filter.mp h).2
    refine ⟨p,sel j,Finset.mem_filter.mpr ⟨he,?_⟩,by simpa [σ] using hp,by simpa [σ,retract_sel inj] using hl⟩
    intro rm
    exact (Finset.mem_sdiff.mp rm).2 (Finset.mem_image_of_mem _ (Finset.mem_univ j))

#print axioms core_card
#print axioms compress_selected
end IncidenceCover.Three
