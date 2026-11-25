import PairRows3722
import Port3722
namespace IncidenceBudget
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

theorem graph_hit {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool)
    {a b : Fin n} (e : G.Adj a b) (ha : x a=true) (hb : x b=true) : graphFun G ∅ x=true := by
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq]
  exact ⟨a,b,e,ha,hb⟩

theorem p4_budget {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (works : circuitFun n C=graphFun G ∅)
    {u v s t : Fin n} (uv : G.Adj u v) (us : G.Adj u s) (vt : G.Adj v t)
    (sv : s≠v) (tu : t≠u) (st : ¬ G.Adj s t) : (used G).card≤C.size := by
  by_contra! small
  have tight := (output_budget n C).2 ((show C.size+1≤(used G).card by omega).trans
    (Finset.card_le_card (support_contains ao works)))
  let X := fun (r j : Nat) => (vword u.val v.val s.val t.val j).testBit r
  have vu : v.val≠u.val := fun eq => uv.ne (Fin.ext eq.symm)
  have su : s.val≠u.val := fun eq => us.ne (Fin.ext eq.symm)
  have tv : t.val≠v.val := fun eq => vt.ne (Fin.ext eq.symm)
  have sv' : s.val≠v.val := fun eq => sv (Fin.ext eq)
  have tu' : t.val≠u.val := fun eq => tu (Fin.ext eq)
  let encode (a b c : Bool) : Nat := if a then 21 else if b then 38 else if c then 56 else 0
  have lookup : ∀ a b c : Bool, ¬(a=true ∧ b=true) → ¬(a=true ∧ c=true) → ¬(b=true ∧ c=true) →
      (encode a b c).testBit 0=a ∧ (encode a b c).testBit 1=b ∧
      (encode a b c).testBit 2=(a||b) ∧ (encode a b c).testBit 3=c := by decide +kernel
  have point (j : Nat) : X 0 j=one u.val j ∧ X 1 j=one v.val j ∧
      X 2 j=pair u.val v.val j ∧ X 3 j=pair s.val t.val j := by
    have eq : vword u.val v.val s.val t.val j=encode (j==u.val) (j==v.val) ((j==s.val)||(j==t.val)) := by
      simp only [vword,encode,Bool.or_eq_true_iff,beq_iff_eq]
    unfold X
    rw [eq]
    apply lookup <;> simp only [Bool.or_eq_true_iff,beq_iff_eq] <;> grind
  have rows : X 0=one u.val ∧ X 1=one v.val ∧ X 2=pair u.val v.val ∧ X 3=pair s.val t.val :=
    ⟨funext (fun j => (point j).1),funext (fun j => (point j).2.1),
      funext (fun j => (point j).2.2.1),funext (fun j => (point j).2.2.2)⟩
  let e := output n C
  have a0 : ev (X 0) e=false := by rw [rows.1,computed ao works,single_off]
  have a1 : ev (X 1) e=false := by rw [rows.2.1,computed ao works,single_off]
  have a2 : ev (X 2) e=true := by rw [rows.2.2.1,computed ao works,edge_on uv]
  have a3 : ev (X 3) e=false := by
    rw [rows.2.2.2,computed ao works]
    change graphFun G ∅ (fun j => (j==s) || (j==t))=false
    rw [graph_pair]; exact decide_eq_false st
  have a4 : ev (X 4) e=true := by
    rw [computed ao works]
    apply graph_hit G _ us
    · simp [X,vword] <;> decide +kernel
    · simp [X,vword,su,sv'] <;> decide +kernel
  have a5 : ev (X 5) e=true := by
    rw [computed ao works]
    apply graph_hit G _ vt
    · simp [X,vword,vu] <;> decide +kernel
    · simp [X,vword,tu',tv] <;> decide +kernel
  have w := word_bound u.val v.val s.val t.val vu.symm e tight
  have exactWord : word u.val v.val s.val t.val e=52 := by
    change pack [0,1,2,3,4,5] (fun r => ev (X r) e)=52
    simp only [pack,List.foldr_cons,List.foldr_nil,a0,a1,a2,a3,a4,a5]
    decide +kernel
  rw [exactWord] at w
  have reject : ∀ a b : Bool, 52∉bag a b := by decide +kernel
  exact reject _ _ w

#print axioms p4_budget
end IncidenceBudget
