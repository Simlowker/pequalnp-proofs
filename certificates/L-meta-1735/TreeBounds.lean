import PEqualNP.Outside.L_meta_1880

/-! Bounds for edge families with small accepting trees. The representative-family
and deleted-edge transfer lemmas are from JLDC's proof of L-meta-1880. Here the
budgets follow the number of leaves of a particular accepting tree. -/

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.Outside.L_meta_1880
namespace Simlowker.Tree1735

/-- An accepting tree. An OR selects one active operand; an AND needs both.
Repeated uses of the same input count as separate leaves. -/
inductive Tree {n : Nat} (C : Circuit) (x : Fin n → Bool) : Nat → Nat → Prop
  | input (i : Fin n) (on : x i = true) : Tree C x i.val 1
  | viaOr {j p k : Nat} (existsGate : j < C.gates.length) (op : (gateAt C j).op = GateOp.or) (mem : p ∈ (gateAt C j).inputs)
      (child : Tree C x p k) : Tree C x (n+j) k
  | viaAnd {j p q a b : Nat} (existsGate : j < C.gates.length) (op : (gateAt C j).op = GateOp.and)
      (ins : (gateAt C j).inputs = [p,q]) (left : Tree C x p a) (right : Tree C x q b) :
      Tree C x (n+j) (a+b)

theorem tree_positive {n C x w k} (t : @Tree n C x w k) : 0 < k := by
  induction t with
  | input => decide
  | viaOr _ _ _ _ h => exact h
  | viaAnd _ _ _ _ _ a b => omega

theorem tree_wire {n C x w k} (t : @Tree n C x w k) : w < n+C.gates.length := by
  cases t with
  | input i => have := i.isLt; omega
  | viaOr h => omega
  | viaAnd h => omega

private theorem tree_input {n C x k} (i : Fin n) (t : Tree C x i.val k) : x i = true := by
  generalize eq : i.val = w at t
  cases t with
  | input z on => exact (Fin.ext eq : i=z) ▸ on
  | viaOr => have := i.isLt; omega
  | viaAnd => have := i.isLt; omega

private theorem tree_or {n C x j p q k} (op : (gateAt C j).op = GateOp.or)
    (ins : (gateAt C j).inputs = [p,q]) (t : @Tree n C x (n+j) k) :
    Tree C x p k ∨ Tree C x q k := by
  generalize eq : n+j = w at t
  cases t with
  | input i => have := i.isLt; omega
  | @viaOr j' a _ _ g mem child =>
    have ej : j=j' := by omega
    subst j'
    rw [ins] at mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    exact mem.elim (fun e => .inl (e ▸ child)) (fun e => .inr (e ▸ child))
  | @viaAnd j' _ _ _ _ _ g _ _ _ =>
    have ej : j=j' := by omega
    subst j'
    rw [op] at g
    contradiction

private theorem tree_and {n C x j p q k} (op : (gateAt C j).op = GateOp.and)
    (ins : (gateAt C j).inputs = [p,q]) (t : @Tree n C x (n+j) k) :
    ∃ a b, a+b=k ∧ Tree C x p a ∧ Tree C x q b := by
  generalize eq : n+j = w at t
  cases t with
  | input i => have := i.isLt; omega
  | @viaOr j' _ _ _ g _ _ =>
    have ej : j=j' := by omega
    subst j'
    rw [op] at g
    contradiction
  | @viaAnd j' l r a b _ g ins' left right =>
    have ej : j=j' := by omega
    subst j'
    rw [ins] at ins'
    simp only [List.cons.injEq,and_true] at ins'
    exact ⟨a,b,rfl,ins'.1.symm ▸ left,ins'.2.symm ▸ right⟩

variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
abbrev Family (n : Nat) := Finset (Finset (Fin n))

def limit (K : Nat) := budget K (2*K)
def span (K : Nat) := 2*((K+1)*(limit K*K))
def factor (K : Nat) := span K * (span K + span K * span K)

def sound (w k : Nat) (R : Family n) := ∀ W ∈ R, W.card ≤ k ∧ Apart G.Adj W W ∧ Forces C w W
def covers (K w k : Nat) (B : Finset (Sym2 (Fin n))) (R : Family n) :=
  ∀ u v, s(u,v) ∉ B → Tree C (pairInput u v) w k → ∀ S : Finset (Fin n),
    S.card + 2*k ≤ 2*K → Apart (away G s(u,v)) {u,v} S → ∃ W ∈ R, Apart (away G s(u,v)) W S
def profile (K w k : Nat) (B : Finset (Sym2 (Fin n))) (R : Family n) :=
  R.card ≤ limit K ∧ sound G C w k R ∧ covers G C K w k B R

omit [DecidableRel G.Adj] in
private theorem monotone_profile {K w k B B' R} (h : profile G C K w k B R) (sub : B ⊆ B') :
    profile G C K w k B' R := ⟨h.1,h.2.1,fun u v he => h.2.2 u v (fun hb => he (sub hb))⟩

private theorem compress_tree (four : NoFourCycle G) {K w k} (bound : k ≤ K)
    {A : Family n} {B : Finset (Sym2 (Fin n))} {D : Finset (Fin n)}
    (inc : ∀ W ∈ A, W ⊆ D) (charged : charge G D ⊆ B)
    (safety : sound G C w k A) (total : covers G C K w k B A) : ∃ R, profile G C K w k B R := by
  obtain ⟨R,rep,size⟩ := representatives G four K (2*K) A (fun W hW => (safety W hW).1.trans bound)
  refine ⟨R,size,fun W hW => safety W (rep.1 hW),?_⟩
  intro u v he t S hs sep
  obtain ⟨W,hw,hS⟩ := total u v he t S hs sep
  exact transfer_rep G (fun hc => he (charged hc)) rep inc (by omega) hw hS

omit [DecidableRel G.Adj] in
private theorem input_profile (K k : Nat) (i : Fin n) (B : Finset (Sym2 (Fin n))) :
    ∃ R, profile G C K i.val k B R := by
  by_cases pos : 0 < k
  · refine ⟨{{i}},?_,?_,?_⟩
    · rw [Finset.card_singleton]
      unfold limit
      generalize 2*K = m
      cases m with
      | zero => simp [budget]
      | succ m => simp [budget]
    · intro W hW
      obtain rfl := Finset.mem_singleton.mp hW
      refine ⟨by rw [Finset.card_singleton]; omega,?_,?_⟩
      · intro a ha b hb
        obtain rfl := Finset.mem_singleton.mp ha
        obtain rfl := Finset.mem_singleton.mp hb
        exact G.irrefl
      · intro x hx
        exact (fires_input ..).mpr (hx _ (by simp))
    · intro u v _ t S _ sep
      obtain h|h := (pairInput_true ..).mp (tree_input i t)
      all_goals exact ⟨{i},by simp,fun a ha => sep a (by simp [Finset.mem_singleton.mp ha,h])⟩
  · refine ⟨∅,by simp,by simp [sound],?_⟩
    intro u v _ t
    exact False.elim (pos (tree_positive t))

private theorem or_profile (four : NoFourCycle G) {K k p q w} {B : Finset (Sym2 (Fin n))}
    {P Q : Family n} {D : Finset (Fin n)} (size : k≤K)
    (ps : profile G C K p k B P) (qs : profile G C K q k B Q)
    (pin : ∀ W ∈ P, W ⊆ D) (qin : ∀ W ∈ Q, W ⊆ D)
    (sem : ∀ x : Fin n → Bool, fires C w x ↔ fires C p x ∨ fires C q x)
    (step : ∀ x : Fin n → Bool, Tree C x w k → Tree C x p k ∨ Tree C x q k) :
    ∃ R, profile G C K w k (B ∪ charge G D) R := by
  apply compress_tree G C four size (A:=P∪Q) (D:=D) _ Finset.subset_union_right
  · intro W hw
    rcases Finset.mem_union.mp hw with a|b
    · obtain ⟨small,ind,force⟩ := ps.2.1 W a
      exact ⟨small,ind,fun x hx => (sem x).mpr (.inl (force x hx))⟩
    · obtain ⟨small,ind,force⟩ := qs.2.1 W b
      exact ⟨small,ind,fun x hx => (sem x).mpr (.inr (force x hx))⟩
  · intro u v e t S hs sep
    have he := fun h => e (Finset.mem_union_left _ h)
    rcases step _ t with a|b
    · obtain ⟨W,hw,se⟩ := ps.2.2 u v he a S hs sep
      exact ⟨W,Finset.mem_union_left _ hw,se⟩
    · obtain ⟨W,hw,se⟩ := qs.2.2 u v he b S hs sep
      exact ⟨W,Finset.mem_union_right _ hw,se⟩
  · intro W hw
    exact (Finset.mem_union.mp hw).elim (pin W) (qin W)

private theorem and_profile (four : NoFourCycle G) {K k p q w} {B : Finset (Sym2 (Fin n))}
    {P Q : Fin (K+1) → Family n} {D : Finset (Fin n)} (size : k ≤ K)
    (ps : ∀ a, profile G C K p a.val B (P a)) (qs : ∀ b, profile G C K q b.val B (Q b))
    (pin : ∀ a W, W ∈ P a → W ⊆ D) (qin : ∀ b W, W ∈ Q b → W ⊆ D)
    (sem : ∀ x : Fin n → Bool, fires C w x ↔ fires C p x ∧ fires C q x)
    (step : ∀ x : Fin n → Bool, Tree C x w k → ∃ a b, a+b=k ∧ Tree C x p a ∧ Tree C x q b) :
    ∃ R, profile G C K w k (B ∪ charge G D) R := by
  classical
  let A : Family n := Finset.univ.filter (fun W =>
    Apart G.Adj W W ∧ ∃ (a b : Fin (K+1)), a.val+b.val=k ∧
      ∃ U ∈ P a, ∃ V ∈ Q b, W = U∪V)
  have mem {W} : W ∈ A ↔ Apart G.Adj W W ∧ ∃ (a b : Fin (K+1)), a.val+b.val=k ∧
      ∃ U ∈ P a, ∃ V ∈ Q b, W = U∪V := by simp [A]
  apply compress_tree G C four size (A:=A) (D:=D) _ Finset.subset_union_right
  · intro W hw
    obtain ⟨ind,a,b,sum,U,hu,V,hv,rfl⟩ := mem.mp hw
    obtain ⟨su,_,fu⟩ := (ps a).2.1 U hu
    obtain ⟨sv,_,fv⟩ := (qs b).2.1 V hv
    refine ⟨(Finset.card_union_le ..).trans (sum ▸ Nat.add_le_add su sv),ind,?_⟩
    intro x hx
    exact (sem x).mpr ⟨fu x (fun z hz => hx z (Finset.mem_union_left _ hz)),
                       fv x (fun z hz => hx z (Finset.mem_union_right _ hz))⟩
  · intro u v he t S hs sep
    obtain ⟨a,b,sum,ta,tb⟩ := step _ t
    have ap := tree_positive ta
    have bp := tree_positive tb
    let i : Fin (K+1) := ⟨a,by omega⟩
    let j : Fin (K+1) := ⟨b,by omega⟩
    have heB := fun h => he (Finset.mem_union_left _ h)
    have heD := fun h => he (Finset.mem_union_right _ h)
    have sa : (S ∪ {u,v}).card + 2*a ≤ 2*K := by
      have h := Finset.card_union_le S {u,v}
      have ss : ({u,v} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
      omega
    obtain ⟨U,hu,awayU⟩ := (ps i).2.2 u v heB ta (S∪{u,v}) sa (apart_union_right.mpr ⟨sep,pair_apart G u v⟩)
    obtain ⟨uS,uPair⟩ := apart_union_right.mp awayU
    have up := apart_symm (away_symm (G:=G) (e:=s(u,v))) uPair
    obtain ⟨su,indU,_⟩ := (ps i).2.1 U hu
    change U.card ≤ a at su
    have sb : (S ∪ U).card + 2*b ≤ 2*K := by
      have h := Finset.card_union_le S U
      omega
    obtain ⟨V,hv,awayV⟩ := (qs j).2.2 u v heB tb (S∪U) sb (apart_union_right.mpr ⟨sep,up⟩)
    obtain ⟨vS,vU⟩ := apart_union_right.mp awayV
    have uV := apart_symm (away_symm (G:=G) (e:=s(u,v))) vU
    have vi := ((qs j).2.1 V hv).2.1
    have apart : Apart (away G s(u,v)) (U∪V) (U∪V) :=
      apart_union_left.mpr ⟨apart_union_right.mpr ⟨apart_weaken indU _,uV⟩,
                             apart_union_right.mpr ⟨vU,apart_weaken vi _⟩⟩
    have sub := Finset.union_subset (pin i U hu) (qin j V hv)
    exact ⟨U∪V,mem.mpr ⟨recover_independent G heD sub apart,i,j,sum,U,hu,V,hv,rfl⟩,
      apart_union_left.mpr ⟨uS,vS⟩⟩
  · intro W hw
    obtain ⟨_,a,b,_,U,hu,V,hv,rfl⟩ := mem.mp hw
    exact Finset.union_subset (pin a U hu) (qin b V hv)

private def pool {K : Nat} (P : Fin (K+1) → Family n) : Finset (Fin n) :=
  Finset.univ.biUnion (fun i => vertices (P i))

private theorem pool_inc {K : Nat} (P : Fin (K+1) → Family n) (i : Fin (K+1)) {W : Finset (Fin n)}
    (h : W ∈ P i) : W ⊆ pool P := fun _ hw =>
  Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,subset_vertices h hw⟩

omit [DecidableRel G.Adj] in
private theorem pool_bound {K p B} {P : Fin (K+1) → Family n}
    (hp : ∀ i, profile G C K p i.val B (P i)) : (pool P).card ≤ (K+1)*(limit K*K) := by
  apply (union_bound Finset.univ (fun i => vertices (P i)) (limit K*K) ?_).trans_eq
  · simp
  · intro i _
    have h := vertices_bound (P i) K (fun W hw => ((hp i).2.1 W hw).1.trans (by omega))
    exact h.trans (Nat.mul_le_mul_right _ (hp i).1)

private theorem all_wires (four : NoFourCycle G) (ao : IsAO2 n C) (K m : Nat) (hm : m ≤ C.gates.length) :
    ∃ B : Finset (Sym2 (Fin n)), B.card ≤ m*factor K ∧ ∀ w < n+m,
      ∀ i : Fin (K+1), ∃ R, profile G C K w i.val B R := by
  classical
  induction m with
  | zero =>
    refine ⟨∅,by simp,?_⟩
    intro w hw i
    exact input_profile G C K i.val ⟨w,by omega⟩ _
  | succ j ih =>
    have hj : j < C.gates.length := by omega
    obtain ⟨B,hB,prev⟩ := ih (by omega)
    have hmem := gateAt_mem hj
    obtain ⟨p,q,ins⟩ := List.length_eq_two.mp (ao.2.2 _ hmem)
    have hp := ao.2.1 j hj p (by simp [ins])
    have hq := ao.2.1 j hj q (by simp [ins])
    choose P hP using prev p hp
    choose Q hQ using prev q hq
    let D := pool P ∪ pool Q
    let B' := B ∪ charge G D
    have pin a W (h : W ∈ P a) : W ⊆ D := (pool_inc P a h).trans Finset.subset_union_left
    have qin b W (h : W ∈ Q b) : W ⊆ D := (pool_inc Q b h).trans Finset.subset_union_right
    have size : D.card ≤ span K := by
      have uni := Finset.card_union_le (pool P) (pool Q)
      have l := pool_bound G C hP
      have r := pool_bound G C hQ
      dsimp [D,span]
      omega
    refine ⟨B',?_,?_⟩
    · rw [Nat.succ_mul]
      exact (Finset.card_union_le ..).trans (Nat.add_le_add hB (charge_bound G four D (span K) size))
    · intro w hw i
      by_cases old : w<n+j
      · obtain ⟨R,hR⟩ := prev w old i
        exact ⟨R,monotone_profile G C hR Finset.subset_union_left⟩
      have eq : w=n+j := by omega
      subst w
      have sem := fires_gate C hj ins hp hq
      rcases ao.1 _ hmem with ha|ho
      · exact and_profile G C four (by omega) hP hQ pin qin (fun x => (sem x).1 ha) (fun _ => tree_and ha ins)
      · exact or_profile G C four (by omega) (hP i) (hQ i) (pin i) (qin i)
          (fun x => (sem x).2 ho) (fun _ => tree_or ho ins)

/-- AND height counts the nested ANDs on the longest path in the chosen tree. -/
inductive Height {n : Nat} (C : Circuit) (x : Fin n → Bool) : Nat → Nat → Prop
  | input (i : Fin n) (on : x i=true) : Height C x i.val 0
  | viaOr {j p d : Nat} (hj : j<C.gates.length) (op : (gateAt C j).op=GateOp.or)
      (mem : p ∈ (gateAt C j).inputs) (sub : Height C x p d) : Height C x (n+j) d
  | viaAnd {j p q a b : Nat} (hj : j<C.gates.length) (op : (gateAt C j).op=GateOp.and)
      (ins : (gateAt C j).inputs=[p,q]) (l : Height C x p a) (r : Height C x q b) :
      Height C x (n+j) (max a b + 1)

theorem height_tree {n C x w d} (h : @Height n C x w d) : ∃ k ≤ 2^d, Tree C x w k := by
  induction h with
  | input i on => exact ⟨1,by simp,Tree.input i on⟩
  | viaOr hj op mem _ ih =>
    obtain ⟨k,cap,t⟩ := ih
    exact ⟨k,cap,Tree.viaOr hj op mem t⟩
  | @viaAnd j p q a b hj op ins _ _ ih₁ ih₂ =>
    obtain ⟨k,cap,t⟩ := ih₁
    obtain ⟨l,cap',t'⟩ := ih₂
    have h₁ := cap.trans (Nat.pow_le_pow_right (by decide : 0<2) (le_max_left a b))
    have h₂ := cap'.trans (Nat.pow_le_pow_right (by decide : 0<2) (le_max_right a b))
    exact ⟨k+l,by rw [pow_succ]; omega,Tree.viaAnd hj op ins t t'⟩

/-- Uniform in the graph, circuit, sharing, and unused paths. The coefficient
depends only on the number of leaves in a shortest accepting tree for each pair. -/
theorem tree_edge_bound (four : NoFourCycle G) (ao : IsAO2 n C)
    (safe : ∀ x : Fin n → Bool, fires C C.output x → graphFun G ∅ x = true)
    (K : Nat) (E : Finset (Sym2 (Fin n)))
    (hit : ∀ u v, s(u,v) ∈ E → ∃ k ≤ K, Tree C (pairInput u v) C.output k) : E.card ≤ C.size * factor K := by
  obtain ⟨B,hB,hAll⟩ := all_wires G C four ao K C.gates.length le_rfl
  apply (Finset.card_le_card (show E ⊆ B from ?_)).trans hB
  intro e
  induction e using Sym2.ind with
  | _ u v =>
    intro he
    by_contra miss
    obtain ⟨k,hk,t⟩ := hit u v he
    let i : Fin (K+1) := ⟨k,by omega⟩
    obtain ⟨R,pr⟩ := hAll C.output (tree_wire t) i
    obtain ⟨W,hW,_⟩ := pr.2.2 u v miss t ∅ (by simp [i]; omega) (by simp [Apart])
    obtain ⟨_,ind,force⟩ := pr.2.1 W hW
    let x := fun z : Fin n => decide (z ∈ W)
    have yes := safe x (force x (by simp [x]))
    simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,
      decide_eq_true_eq,x] at yes
    obtain ⟨a,b,adj,ha,hb⟩ := yes
    exact ind a ha b hb adj

theorem height_edge_bound (four : NoFourCycle G) (ao : IsAO2 n C)
    (safe : ∀ x : Fin n → Bool, fires C C.output x → graphFun G ∅ x = true)
    (D : Nat) (E : Finset (Sym2 (Fin n)))
    (hit : ∀ u v, s(u,v) ∈ E → ∃ d ≤ D, Height C (pairInput u v) C.output d) :
    E.card ≤ C.size * factor (2^D) := by
  apply tree_edge_bound G C four ao safe
  intro u v edge
  obtain ⟨d,hd,h⟩ := hit u v edge
  obtain ⟨k,hk,t⟩ := height_tree h
  exact ⟨k,hk.trans (Nat.pow_le_pow_right (by decide) hd),t⟩

#print axioms tree_edge_bound
#print axioms height_edge_bound

end Simlowker.Tree1735
