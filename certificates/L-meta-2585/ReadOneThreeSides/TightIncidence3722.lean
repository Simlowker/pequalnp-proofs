import TightCompile3722
import Sparse3722
namespace IncidenceBudget
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.ReadK SparseIncidence

def used {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Finset Nat :=
  (Finset.univ.filter fun v : Fin n => ∃ w,G.Adj v w).image Fin.val

theorem computed {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (ao : IsAO2 n C) (works : circuitFun n C=graphFun G ∅) (x : Nat → Bool) :
    ev x (output n C)=graphFun G ∅ (fun i => x i.val) := by
  rw [project_ev n C ao]
  have listEq : rows n x=List.ofFn (fun i : Fin n => x i.val) := by
    apply List.ext_getElem <;> simp [rows]
  rw [listEq]
  exact congrFun works _

def pair (u v j : Nat) := (j==u) || (j==v)
def one (v j : Nat) := j==v

theorem edge_on {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} (edge : G.Adj u v) : graphFun G ∅ (fun i => pair u.val v.val i.val)=true := by
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq]
  exact ⟨u,v,edge,by simp [pair],by simp [pair]⟩

theorem single_off {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : Nat) :
    graphFun G ∅ (fun i => one p i.val)=false := by
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_false_iff_not]
  rintro ⟨a,b,adj,ha,hb⟩
  have eq : a=b := Fin.ext ((beq_iff_eq.mp ha).trans (beq_iff_eq.mp hb).symm)
  subst b
  exact G.irrefl adj

theorem support_contains {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (ao : IsAO2 n C) (works : circuitFun n C=graphFun G ∅) :
    used G ⊆ (sig (output n C)).1 := by
  intro j hj
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hj
  obtain ⟨v,edge⟩ := (Finset.mem_filter.mp hu).2
  by_contra missing
  have eq : ev (pair u.val v.val) (output n C)=ev (one v.val) (output n C) := by
    apply ev_agree
    intro i hi
    have ne : i≠u.val := fun e => missing (e ▸ hi)
    simp [pair,one,ne]
  rw [computed ao works,computed ao works,edge_on edge,single_off] at eq
  contradiction

theorem support_lower {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (ao : IsAO2 n C) (works : circuitFun n C=graphFun G ∅) : (used G).card≤C.size+1 :=
  (Finset.card_le_card (support_contains ao works)).trans (output_budget n C).1

theorem tight_single {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (ao : IsAO2 n C) (works : circuitFun n C=graphFun G ∅) (tight : C.size+1≤(used G).card)
    (m : Nat → Bool) {u v : Fin n} (edge : G.Adj u v) (mu : m u=false) (mv : m v=true) :
    lineSingle C n m u v=true := by
  let e := output n C
  let x := pair u.val v.val
  have treeTight := (output_budget n C).2 (tight.trans (Finset.card_le_card (support_contains ao works)))
  have active (j) (hm : m j=true) (hx : x j=true) : j=v.val := by
    rcases Bool.or_eq_true_iff.mp hx with h|h
    · have eq : j=u := beq_iff_eq.mp h
      rw [eq,mu] at hm; contradiction
    · exact beq_iff_eq.mp h
  have table := linear_when_tight e m x v.val active treeTight
  have mask : (fun j => x j && !m j)=one u.val := by
    funext j
    by_cases hu : j=u.val
    · subst j; simp [x,pair,one,mu]
    · by_cases hv : j=v.val
      · subst j; simp [x,pair,one,mv,hu]
      · simp [x,pair,one,beq_eq_false_iff_ne.mpr hv,beq_eq_false_iff_ne.mpr hu]
  have dead : (lin m x e).1=false := by
    rw [constant_part,mask,computed ao works,single_off]
  have yes : ev x e=true := (computed ao works x).trans (edge_on edge)
  rw [dead,yes,Bool.false_or] at table
  change ((linearParts C m (rows n x)).getD C.output (false,false)).2=true
  rw [←project_lin n C ao m x]
  exact table

theorem tight_incidence {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (G : SimpleGraph (Fin (N+N))) [DecidableRel G.Adj] (ok : compatible N I G) (C : Circuit)
    (ao : IsAO2 (N+N) C) (works : circuitFun (N+N) C=graphFun G ∅) (tight : C.size+1≤(used G).card) :
    doubleReread C (N+N) (fun i => decide (N ≤ i)) (incidences N I)=[] := by
  apply List.filter_eq_nil_iff.mpr
  intro z hz
  obtain ⟨p,_,hp⟩ := List.mem_flatMap.mp hz
  obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hp
  have edge := (ok (Fin.castAdd N p) (Fin.natAdd N l)).mpr
    ⟨p,l,of_decide_eq_true (List.mem_filter.mp hl).2,Or.inl ⟨rfl,rfl⟩⟩
  have hs := tight_single ao works tight (fun i => decide (N ≤ i)) edge
    (by simp [p.isLt]) (by simp)
  change lineSingle C (N+N) (fun i => decide (N ≤ i)) p.val (N+l.val)=true at hs
  simp [hs]

#print axioms support_lower
#print axioms tight_incidence
end IncidenceBudget
