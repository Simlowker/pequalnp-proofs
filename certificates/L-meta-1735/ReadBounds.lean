import TreeBounds
import TypeBounds
import PEqualNP.MetaComplexity.Helpers.ReadTwoBridge

/-! Compare the project's capped count vectors with accepting trees for
a two-vertex input, at an arbitrary read threshold. -/

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.ReadK
open PEqualNP.Outside.L_meta_1880
namespace Simlowker.Tree1735
namespace RV
open PEqualNP.MetaComplexity.ReadTwoBridge

private abbrev vectors {n : Nat} (C : Circuit) (u v : Fin n) (r w : Nat) :=
  (readVectors C n [u.val,v.val] r).getD w []
private theorem at_input {n : Nat} (C : Circuit) (u v : Fin n) (r w : Nat) (hw : w<n) :
    vectors C u v r w = leafVectors [u.val,v.val] r w := by
  unfold vectors
  rw [rv_eq,foldl_snoc_init _ _ _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD,hw]

private theorem at_gate {n : Nat} (C : Circuit) (u v : Fin n) (r j : Nat) (hj : j<C.gates.length)
    (rb : ∀ i ∈ (gateAt C j).inputs, i<n+j) :
    vectors C u v r (n+j) = rvG [u.val,v.val] r ((gateAt C j).inputs.map (vectors C u v r)) (gateAt C j) := by
  unfold vectors
  rw [PEqualNP.MetaComplexity.ReadTwoBridge.gateAt_eq C j hj] at rb ⊢
  have h := foldl_snoc_gate (rvG [u.val,v.val] r) [] ((List.range n).map (leafVectors [u.val,v.val] r)) C.gates j hj
    (by simpa using rb)
  simp only [List.length_map,List.length_range] at h
  rw [rv_eq,h]

private theorem realize_pair {n : Nat} (C : Circuit) (ao : IsAO2 n C) (u v : Fin n) (uv : u ≠ v) (r w : Nat)
    (z : List Nat) (mem : z ∈ vectors C u v r w) :
    ∃ a b, Tree C (pairInput u v) w (a+b) ∧ z = [min a (r+1), min b (r+1)] := by
  induction w using Nat.strong_induction_on generalizing z with
  | ind w ih =>
    by_cases lo : w<n
    · rw [at_input C u v r w lo] at mem
      simp only [leafVectors] at mem
      split_ifs at mem with h
      · simp only [List.mem_singleton] at mem
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        have neval : u.val ≠ v.val := fun eq => uv (Fin.ext eq)
        rcases h with e|e
        · subst w
          refine ⟨1,0,?_,?_⟩
          · exact Tree.input u (by simp [pairInput])
          · simpa [neval,Ne.symm neval] using mem
        · subst w
          refine ⟨0,1,?_,?_⟩
          · exact Tree.input v (by simp [pairInput])
          · simpa [neval,Ne.symm neval] using mem
      · simp at mem
    obtain ⟨j,rfl⟩ : ∃ j, w=n+j := ⟨w-n,by omega⟩
    by_cases hj : j<C.gates.length
    swap
    · unfold vectors at mem
      rw [rv_eq,foldl_snoc_beyond _ _ _ _ _ (by simp; omega)] at mem
      simp at mem
    obtain ⟨p,q,hins⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hj))
    have pm : p ∈ (gateAt C j).inputs := by simp [hins]
    have qm : q ∈ (gateAt C j).inputs := by simp [hins]
    have hp := ao.2.1 j hj p pm
    have hq := ao.2.1 j hj q qm
    rw [at_gate C u v r j hj (ao.2.1 j hj)] at mem
    rcases ao.1 _ (gateAt_mem hj) with hand|hor
    · simp only [rvG,hand,hins,List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil] at mem
      obtain ⟨left,hl,right,hr,rfl⟩ := (mem_andStep ..).mp mem
      obtain ⟨zero,hzero,z,hz,rfl⟩ := (mem_andStep ..).mp hl
      obtain rfl := List.mem_singleton.mp hzero
      obtain ⟨a,b,ta,rfl⟩ := ih p hp z hz
      obtain ⟨c,d,tb,rfl⟩ := ih q hq right hr
      refine ⟨a+c,b+d,?_,?_⟩
      · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Tree.viaAnd hj hand hins ta tb
      · simp only [capAdd,List.zipWith_cons_cons,List.zipWith_nil_right,
          List.cons.injEq,and_true]
        constructor <;> omega
    · simp only [rvG,hor,hins,List.map_cons,List.map_nil] at mem
      rw [mem_orFold] at mem
      simp only [List.not_mem_nil,false_or,List.mem_cons,or_false,exists_eq_or_imp,exists_eq_left] at mem
      rcases mem with h|h
      · obtain ⟨a,b,t,hz⟩ := ih p hp z h
        exact ⟨a,b,Tree.viaOr hj hor pm t,hz⟩
      · obtain ⟨a,b,t,hz⟩ := ih q hq z h
        exact ⟨a,b,Tree.viaOr hj hor qm t,hz⟩

theorem read_pair_tree {n : Nat} (C : Circuit) (ao : IsAO2 n C) (r : Nat) (u v : Fin n) (uv : u ≠ v)
    (yes : readsAtMost C n [u.val,v.val] r = true) :
    ∃ k ≤ 2*r, Tree C (pairInput u v) C.output k := by
  obtain ⟨z,hz,good⟩ := List.any_eq_true.mp yes
  obtain ⟨a,b,t,rfl⟩ := realize_pair C ao u v uv r C.output z hz
  simp only [List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq] at good
  exact ⟨a+b,by omega,t⟩

end RV

private theorem pair_list {n : Nat} (u v : Fin n) (ne : u ≠ v) :
    setList {u,v} = [u.val,v.val] ∨ setList {u,v} = [v.val,u.val] := by
  have hne : u.val ≠ v.val := fun eq => ne (Fin.ext eq)
  have nd : (setList {u,v}).Nodup := List.Nodup.map Fin.val_injective ((List.nodup_finRange n).filter _)
  have perm : (setList {u,v}).Perm [u.val,v.val] := by
    apply (List.perm_ext_iff_of_nodup nd (by simp [hne])).mpr
    intro z
    simp only [setList,List.mem_map,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq,
      Finset.mem_insert,Finset.mem_singleton,List.mem_cons,List.not_mem_nil,or_false]
    constructor
    · rintro ⟨a,h|h,e⟩
      · exact .inl (e.symm.trans (congrArg Fin.val h))
      · exact .inr (e.symm.trans (congrArg Fin.val h))
    · rintro (rfl|rfl)
      · exact ⟨u,.inl rfl,rfl⟩
      · exact ⟨v,.inr rfl,rfl⟩
  obtain ⟨a,b,eq⟩ := List.length_eq_two.mp perm.length_eq
  rw [eq] at perm nd ⊢
  have ab : a ≠ b := by simpa using nd
  have aIn := perm.mem_iff.mp (List.mem_cons_self : a ∈ [a,b])
  have bIn := perm.mem_iff.mp (by simp : b ∈ [a,b])
  simp only [List.mem_cons,List.not_mem_nil,or_false] at aIn bIn
  rcases aIn with rfl|rfl <;> rcases bIn with rfl|rfl <;> simp_all

private theorem prime_pair {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (compute : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅) (u v : Fin n) (adj : G.Adj u v) :
    IsPrimeImplicant n C {u,v} := by
  constructor
  · have inp : setInput {u,v} = pairInput u v := by funext z; simp [setInput,pairInput]
    rw [compute,inp]
    exact (graphFun_pair G u v).mpr adj
  · intro T hT
    obtain ⟨sub,ne⟩ := Finset.ssubset_iff_subset_ne.mp (Finset.mem_ssubsets.mp hT)
    rw [compute]
    apply Bool.eq_false_iff.mpr
    intro yes
    simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,
      setInput,decide_eq_true_eq] at yes
    obtain ⟨a,b,ab,ha,hb⟩ := yes
    have aa := sub ha
    have bb := sub hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at aa bb
    apply ne (Finset.Subset.antisymm sub ?_)
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases aa with rfl|rfl <;> rcases bb with e|e <;> rcases hz with h|h <;> first
      | exact h.symm ▸ ha
      | exact (h.trans e.symm).symm ▸ hb
      | exact False.elim (ab.ne e.symm)

theorem read_k_bound {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (four : NoFourCycle G) (ao : IsAO2 n C) (compute : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (r : Nat) (read : IsReadK n C r) : G.edgeFinset.card ≤ C.size * factor (2*r) := by
  apply tree_edge_bound G C four ao (fun x hx => (congrFun compute x) ▸ hx)
  intro u v edge
  have adj := G.mem_edgeFinset.mp edge
  have yes := read _ (prime_pair G C compute u v adj)
  rcases pair_list u v adj.ne with ord|ord
  · rw [ord] at yes
    exact RV.read_pair_tree C ao r u v adj.ne yes
  · rw [ord] at yes
    have sw : pairInput v u = pairInput u v := by funext z; simp [pairInput,or_comm]
    exact sw ▸ RV.read_pair_tree C ao r v u adj.ne.symm yes

/-- A dense counterexample would require an edge for which both orders
    of the joint capped-vector test fail at the chosen threshold. -/
theorem hard_edge {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (four : NoFourCycle G) (ao : IsAO2 n C) (compute : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (r : Nat) (dense : C.size * factor (2*r) < G.edgeFinset.card) :
    ∃ u v, G.Adj u v ∧ readsAtMost C n [u.val,v.val] r = false ∧ readsAtMost C n [v.val,u.val] r = false := by
  by_contra! all
  apply (Nat.not_lt_of_ge (tree_edge_bound G C four ao (fun x hx => (congrFun compute x) ▸ hx)
    (2*r) G.edgeFinset ?_)) dense
  intro u v edge
  have adj := G.mem_edgeFinset.mp edge
  by_cases yes : readsAtMost C n [u.val,v.val] r = true
  · exact RV.read_pair_tree C ao r u v adj.ne yes
  · have other := all u v adj (Bool.eq_false_iff.mpr yes)
    have sw : pairInput v u = pairInput u v := by funext z; simp [pairInput,or_comm]
    exact sw ▸ RV.read_pair_tree C ao r v u adj.ne.symm (by simpa using other)

/-- A replacement with bounded read multiplicity may cost a fixed factor.
    Such replacements suffice for the exact desk conclusion of L-meta-1735. -/
theorem replacement_suffices (r overhead : Nat)
    (normalize : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ C : Circuit, IsLeastAO G C → TopForm G C → ∃ D : Circuit, IsAO2 n D ∧
      PEqualNP.MetaComplexity.circuitFun n D = graphFun G ∅ ∧ IsReadK n D r ∧
      D.size ≤ overhead*(C.size+1)) :
    ∃ c : Nat, ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ C : Circuit, IsLeastAO G C → TopForm G C → (Ustar G C).card ≤ c*(C.size+1) := by
  refine ⟨factor (2*r)*overhead,?_⟩
  intro n G _ girth nonempty C least top
  obtain ⟨D,ao,compute,read,size⟩ := normalize n G girth nonempty C least top
  have sub : Ustar G C ⊆ G.edgeFinset := Finset.sdiff_subset
  calc
    _ ≤ G.edgeFinset.card := Finset.card_le_card sub
    _ ≤ D.size * factor (2*r) := read_k_bound G D (Simlowker.Types1735.girth_four G girth) ao compute r read
    _ ≤ (overhead*(C.size+1))*factor (2*r) := Nat.mul_le_mul_right _ size
    _ = _ := by ring

#print axioms replacement_suffices
#print axioms read_k_bound
#print axioms hard_edge
end Simlowker.Tree1735
