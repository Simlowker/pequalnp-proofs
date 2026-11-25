import Obstruction3722
import Ref7684
import Ref4897

namespace IncidenceCover
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4897 (graph cross)
open IncidenceBudget

def computes {P L : ℕ} (E : Finset (Fin P × Fin L)) (C : Circuit) :=
  ∀ z : Fin (P+L) → Bool, circuitFun (P+L) C z =
    decide (∃ p l, (p,l)∈E ∧ z (Fin.castAdd L p)=true ∧ z (Fin.natAdd P l)=true)

def replacement {P L : ℕ} (E : Finset (Fin P × Fin L)) (C : Circuit) :=
  ∃ D : Circuit, IsAO2 (P+L) D ∧ computes E D ∧ D.size≤C.size ∧ PEqualNP.ReadK.IsReadK (P+L) D 1

theorem from_cover {P L : ℕ} {E : Finset (Fin P × Fin L)} {C : Circuit}
    (A : Finset (Fin P)) (B : Finset (Fin L))
    (hits : ∀ e∈E,e.1∈A ∨ e.2∈B) (budget : E.card+A.card+B.card≤C.size+1) :
    replacement E C := by
  obtain ⟨D,ao,sz,works,read⟩ := PEqualNP.Outside.L_meta_7684 P L E A B hits
  exact ⟨D,ao,works,by omega,read⟩

theorem graph_computes {P L} {E : Finset (Fin P × Fin L)} {C : Circuit}
    (f : computes E C) :
    letI := Classical.decRel (graph E).Adj
    circuitFun (P+L) C=graphFun (graph E) ∅ := by
  classical
  funext z
  rw [f]
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or]
  congr 1
  apply propext
  constructor
  · rintro ⟨a,b,edge,ha,hb⟩
    exact ⟨Fin.castAdd L a,Fin.natAdd P b,by simpa [graph,cross] using edge,ha,hb⟩
  · rintro ⟨a,b,edge,ha,hb⟩
    cases a using Fin.addCases <;> cases b using Fin.addCases <;> simp [graph,cross] at edge
    · exact ⟨_,_,edge,ha,hb⟩
    · exact ⟨_,_,edge,hb,ha⟩

theorem support_count {P L : ℕ} (E : Finset (Fin P × Fin L)) :
    letI := Classical.decRel (graph E).Adj
    (E.image Prod.fst).card+(E.image Prod.snd).card ≤ (used (graph E)).card := by
  classical
  let s := (E.image Prod.fst).disjSum (E.image Prod.snd)
  have h : ∀ i∈s, (finSumFinEquiv i : Fin (P+L)).val ∈ used (graph E) := by
    intro i hi
    apply Finset.mem_image.mpr
    refine ⟨finSumFinEquiv i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
    cases i with
    | inl p =>
      obtain ⟨⟨a,b⟩,he,rfl⟩ := Finset.mem_image.mp (Finset.inl_mem_disjSum.mp hi)
      exact ⟨Fin.natAdd P b,by simpa [graph,cross] using he⟩
    | inr l =>
      obtain ⟨⟨a,b⟩,he,rfl⟩ := Finset.mem_image.mp (Finset.inr_mem_disjSum.mp hi)
      exact ⟨Fin.castAdd L a,by simpa [graph,cross] using he⟩
  have b := Finset.card_le_card_of_injOn (fun i => (finSumFinEquiv i : Fin (P+L)).val) h
    (fun _ _ _ _ eq => finSumFinEquiv.injective (Fin.ext eq))
  simpa [s] using b

theorem support_bound {P L : ℕ} {E : Finset (Fin P × Fin L)} {C : Circuit}
    (ao : IsAO2 (P+L) C) (works : computes E C) :
    (E.image Prod.fst).card+(E.image Prod.snd).card≤C.size+1 := by
  classical
  exact (support_count E).trans (support_lower ao (graph_computes works))

theorem path_bound {P L : ℕ} {E : Finset (Fin P × Fin L)} {C : Circuit}
    (ao : IsAO2 (P+L) C) (works : computes E C) {p q : Fin P} {l m : Fin L}
    (e : (p,l)∈E) (f : (p,m)∈E) (g : (q,l)∈E) (mp : m≠l) (qp : q≠p) (diag : (q,m)∉E) :
    (E.image Prod.fst).card+(E.image Prod.snd).card≤C.size := by
  classical
  apply (support_count E).trans
  apply p4_budget (graph E) C ao (graph_computes works)
    (u:=Fin.castAdd L p) (v:=Fin.natAdd P l) (s:=Fin.natAdd P m) (t:=Fin.castAdd L q)
  all_goals simp_all [graph,cross]

theorem unique_columns {P L : ℕ} {E : Finset (Fin P × Fin L)} {C : Circuit}
    (ao : IsAO2 (P+L) C) (works : computes E C)
    (uniq : Set.InjOn Prod.snd (↑E : Set (Fin P × Fin L))) : replacement E C := by
  apply from_cover (E.image Prod.fst) ∅ (fun e he => Or.inl (Finset.mem_image_of_mem _ he))
  have h := support_bound ao works
  have eq := Finset.card_image_of_injOn uniq
  simp only [Finset.card_empty, Nat.add_zero]
  omega
#print axioms path_bound
#print axioms unique_columns
end IncidenceCover
