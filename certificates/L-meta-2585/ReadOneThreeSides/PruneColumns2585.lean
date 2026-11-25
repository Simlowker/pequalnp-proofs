import Ref5720
import IncidenceCover2585

namespace IncidenceCover
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def keepColumns {P L} (E : Finset (Fin P × Fin L)) (B : Finset (Fin L)) :=
  E.filter (fun e => e.2∈B)
def incidenceValue {P L} (E : Finset (Fin P × Fin L)) (x : Fin (P+L) → Bool) :=
  decide (∃ p l,(p,l)∈E ∧ x (Fin.castAdd L p)=true ∧ x (Fin.natAdd P l)=true)
theorem cross_ne {P L} (p : Fin P) (l : Fin L) : Fin.castAdd L p ≠ Fin.natAdd P l := by
  intro h
  have eq := congrArg Fin.val h
  simp at eq
  omega

theorem restriction {P L} (E : Finset (Fin P × Fin L)) (l : Fin L) (x : Fin (P+L) → Bool) :
    incidenceValue E (Function.update x (Fin.natAdd P l) false) =
      incidenceValue (E.filter fun e => e.2≠l) x := by
  simp only [incidenceValue,Finset.mem_filter]
  congr 1
  apply propext
  constructor
  · rintro ⟨p,j,edge,hp,hj⟩
    have ne : j≠l := by rintro rfl; simp at hj
    refine ⟨p,j,⟨edge,ne⟩,?_,?_⟩
    · simpa [Function.update_of_ne (cross_ne p l)] using hp
    · have h : Fin.natAdd P j ≠ Fin.natAdd P l := fun eq => ne (Fin.natAdd_injective _ _ eq)
      simpa [Function.update_of_ne h] using hj
  · rintro ⟨p,j,⟨e,ne⟩,hp,hj⟩
    have h : Fin.natAdd P j ≠ Fin.natAdd P l := fun eq => ne (Fin.natAdd_injective _ _ eq)
    exact ⟨p,j,e,by simpa [Function.update_of_ne (cross_ne p l)] using hp,
      by simpa [Function.update_of_ne h] using hj⟩

def pairInput {P L} (p : Fin P) (l : Fin L) (i : Fin (P+L)) :=
  decide (i=Fin.castAdd L p ∨ i=Fin.natAdd P l)

theorem pair_value {P L} (E : Finset (Fin P × Fin L)) (p : Fin P) (l : Fin L) :
    incidenceValue E (pairInput p l)=decide ((p,l)∈E) := by
  simp only [incidenceValue,pairInput,decide_eq_true_eq]
  congr 1
  apply propext
  constructor
  · rintro ⟨a,b,e,ha,hb⟩
    have ap : a=p := Fin.castAdd_injective _ _ (ha.resolve_right (cross_ne a l))
    have bl : b=l := Fin.natAdd_injective _ _ (hb.resolve_left (Ne.symm (cross_ne p b)))
    simpa [ap,bl] using e
  · exact fun h => ⟨p,l,h,Or.inl rfl,Or.inr rfl⟩

theorem delete_column {P L} {E : Finset (Fin P × Fin L)} {C : Circuit} (ao : IsAO2 (P+L) C)
    (works : computes E C) (l : Fin L) (active : ∃ p,(p,l)∈E)
    (remains : (E.filter fun e => e.2≠l).Nonempty) :
    ∃ D : Circuit, IsAO2 (P+L) D ∧ D.size<C.size ∧ computes (E.filter fun e => e.2≠l) D := by
  obtain ⟨p,pl⟩ := active
  obtain ⟨⟨q,m⟩,he⟩ := remains
  let F := E.filter (fun e => e.2≠l)
  have eval (x) : circuitFun (P+L) C x=incidenceValue E x := works x
  have update (x) : circuitFun (P+L) C (Function.update x (Fin.natAdd P l) false)=incidenceValue F x :=
    (eval _).trans (restriction _ _ _)
  obtain ⟨D,da,sz,w⟩ := PEqualNP.Outside.L_meta_5720 (P+L) C (Fin.natAdd P l) ao
    (show ∃ x, circuitFun _ C x ≠ circuitFun _ C (Function.update x (Fin.natAdd P l) false) by
      refine ⟨pairInput p l,?_⟩
      rw [update,eval,pair_value,pair_value]
      simp [pl,F])
    (show ∃ x y, circuitFun _ C (Function.update x (Fin.natAdd P l) false) ≠
      circuitFun _ C (Function.update y (Fin.natAdd P l) false) by
        refine ⟨pairInput q m,fun _ => false,?_⟩
        rw [update,update,pair_value]
        change decide ((q,m)∈F)≠incidenceValue F (fun _ => false)
        simp [incidenceValue,show (q,m)∈F from he])
  exact ⟨D,da,sz,fun x => (w x).trans (update x)⟩

theorem prune_columns {P L} {E : Finset (Fin P × Fin L)} {C : Circuit} (S : Finset (Fin L))
    (ao : IsAO2 (P+L) C) (works : computes E C) (active : ∀ l∈S, ∃ p,(p,l)∈E)
    (keep : (E.filter fun e => e.2∉S).Nonempty) :
    ∃ D : Circuit, IsAO2 (P+L) D ∧ D.size+S.card ≤ C.size ∧ computes (E.filter fun e => e.2∉S) D := by
  classical
  induction S using Finset.induction_on generalizing C E with
  | empty => exact ⟨C,ao,by simp,by simpa using works⟩
  | @insert l S outside ih =>
    let F := E.filter (fun e => e.2≠l)
    have eq : (F.filter fun e => e.2∉S)=E.filter (fun e => e.2∉insert l S) := by
      ext e
      simp [F,not_or,and_assoc]
    have kp : (F.filter fun e => e.2∉S).Nonempty := eq ▸ keep
    have left : F.Nonempty := kp.mono (Finset.filter_subset _ _)
    obtain ⟨D,da,less,dw⟩ := delete_column ao works l (active l (Finset.mem_insert_self _ _)) left
    have act : ∀ j∈S,∃ p,(p,j)∈F := by
      intro j hj
      obtain ⟨p,h⟩ := active j (Finset.mem_insert_of_mem hj)
      exact ⟨p,Finset.mem_filter.mpr ⟨h,fun ej => outside (ej ▸ hj)⟩⟩
    obtain ⟨D',ao',budget,correct⟩ := ih da dw act kp
    exact ⟨D',ao',by rw [Finset.card_insert_of_notMem outside]; omega,eq ▸ correct⟩

#print axioms prune_columns
#print axioms delete_column
end IncidenceCover
