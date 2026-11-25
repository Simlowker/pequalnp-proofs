import WideGates
import DegreeBounds

/-! ## Dependence on the input sides of dirty gates -/

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1506
namespace Simlowker.Types1735
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

theorem dirty_leaf (ao : IsAO2 n C) (top : TopForm G C) (j h p : Nat)
    (hj : j < C.gates.length) (jAnd : (gateAt C j).op = GateOp.and)
    (hp : p ∈ (gateAt C j).inputs) (before : p < n+j)
    (hh : h < C.gates.length) (hAnd : (gateAt C h).op = GateOp.and)
    (reached : OrR n C p (n+h)) : h < j ∧ h ∈ junk G C := by
  have A := ao_of n C ao
  have le := orR_le n C A _ _ reached
  have pe : p = n+(p-n) := by omega
  have cone : InCone n C h j := by
    rcases orR_cone n C A h p reached (p-n) pe (by omega) with eq|hc
    · apply inCone_c1 n C A h j hj
      rwa [eq,←pe]
    · apply inCone_c2 n C A h (p-n) j hj hc
      rwa [←pe]
  have outside : ¬ BelowF G C h := fun ok => top h hh j hj hAnd ok jAnd cone
  unfold BelowF at outside
  push Not at outside
  obtain ⟨x,on,off⟩ := outside
  exact ⟨by omega,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh,hAnd,hh,x,on,by simpa using off⟩⟩

def baseOn (j : Nat) (b : Fin 2) (x : Fin n → Bool) := ∃ v ∈ side C j b, x v = true

theorem through_operand (ao : IsAO2 n C) (top : TopForm G C) {j : Nat}
    (hj : j < C.gates.length) (jAnd : (gateAt C j).op = GateOp.and)
    (b : Fin 2) (x : Fin n → Bool) :
    W n C x (opnd C j b) = true ↔ baseOn C j b x ∨
      ∃ k < j, k ∈ junk G C ∧ OrR n C (opnd C j b) (n+k) ∧ gateVal n C k x = true := by
  have A := ao_of n C ao
  obtain ⟨a,d,ins,ha,hd⟩ := (A j hj).2
  have inputMem : opnd C j b ∈ (gateAt C j).inputs := by
    fin_cases b <;> simp [opnd,ins,List.getD]
  have before : opnd C j b < n+j := by
    fin_cases b <;> simp [opnd,ins,List.getD,ha,hd]
  constructor
  · intro on
    obtain ⟨v,reach,leaf,enabled⟩ := orR_leaf_true n C A x _ (by omega) on
    rcases leaf with lo | ⟨k,rfl,hk,op⟩
    · left
      exact ⟨⟨v,lo⟩,(orIn_iff n C A _ _).mpr reach,(W_input n C x v lo) ▸ enabled⟩
    · obtain ⟨sm,dirty⟩ := dirty_leaf G C ao top j k _ hj jAnd inputMem before hk op reach
      exact Or.inr ⟨k,sm,dirty,reach,enabled⟩
  · rintro (⟨v,mem,yes⟩|⟨k,_,_,reach,yes⟩)
    · exact orR_mono n C A x _ v.val ((orIn_iff n C A _ v).mp mem) (by rwa [W_input n C _ _ v.isLt])
    · exact orR_mono n C A x _ (n+k) reach yes

theorem and_on (ao : IsAO2 n C) {j : Nat} (hj : j < C.gates.length) (op : (gateAt C j).op = GateOp.and)
    (x : Fin n → Bool) : gateVal n C j x = true ↔
      W n C x (opnd C j 0) = true ∧ W n C x (opnd C j 1) = true := by
  obtain ⟨a,b,ins,ha,hb⟩ := ((ao_of n C ao) j hj).2
  change W n C x (n+j) = true ↔ _
  rw [W_and n C x j hj op a b ins ha hb,Bool.and_eq_true_iff]
  simp [opnd,ins,List.getD]

theorem dirty_transfer (ao : IsAO2 n C) (top : TopForm G C) (x y : Fin n → Bool)
    (profile : ∀ j ∈ junk G C, ∀ b : Fin 2, baseOn C j b x → baseOn C j b y) :
    ∀ j ∈ junk G C, gateVal n C j x = true → gateVal n C j y = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j prev =>
    intro dirty on
    have mem := Finset.mem_filter.mp dirty
    have hj := Finset.mem_range.mp mem.1
    have andOp := mem.2.1
    have src := (and_on C ao hj andOp x).mp on
    apply (and_on C ao hj andOp y).mpr
    have move (b : Fin 2) (val : W n C x (opnd C j b) = true) : W n C y (opnd C j b) = true := by
      apply (through_operand G C ao top hj andOp b y).mpr
      rcases (through_operand G C ao top hj andOp b x).mp val with base|⟨k,sm,hk,re,yes⟩
      · exact Or.inl (profile j dirty b base)
      · exact Or.inr ⟨k,sm,hk,re,prev k sm hk yes⟩
    exact ⟨move 0 src.1,move 1 src.2⟩

#print axioms dirty_transfer
end Simlowker.Types1735

/-! ## Substitution inside a signature class -/

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1506
namespace Simlowker.Types1735
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

def signature (v : Fin n) (j : {j // j ∈ junk G C}) (b : Fin 2) : Bool :=
  decide (v ∈ side C j.val b)

theorem base_pair (j : Nat) (b : Fin 2) (u v : Fin n) :
    baseOn C j b (pairInput u v) ↔ u ∈ side C j b ∨ v ∈ side C j b := by
  simp only [baseOn,pairInput,decide_eq_true_eq]
  constructor
  · rintro ⟨w,hw,rfl|rfl⟩
    · exact Or.inl hw
    · exact Or.inr hw
  · rintro (h|h)
    · exact ⟨u,h,Or.inl rfl⟩
    · exact ⟨v,h,Or.inr rfl⟩

def marked (j : Nat) (b : Fin 2) (u v : Fin n) : Prop :=
  ∃ k < j, k ∈ junk G C ∧ OrR n C (opnd C j b) (n+k) ∧ gateVal n C k (pairInput u v) = true

theorem move_mark (ao : IsAO2 n C) (top : TopForm G C) {j : Nat} {b : Fin 2} {u v u' v' : Fin n}
    (p : signature G C u = signature G C u') (q : signature G C v = signature G C v')
    (h : marked G C j b u v) : marked G C j b u' v' := by
  obtain ⟨k,lt,hk,reach,on⟩ := h
  refine ⟨k,lt,hk,reach,dirty_transfer G C ao top _ _ ?_ k hk on⟩
  intro i hi a active
  have eq1 := congrFun (congrFun p ⟨i,hi⟩) a
  have eq2 := congrFun (congrFun q ⟨i,hi⟩) a
  simp only [signature,decide_eq_decide] at eq1 eq2
  exact (base_pair C i a u' v').mpr (((base_pair C i a u v).mp active).imp eq1.mp eq2.mp)

theorem edge_top (least : IsLeastAO G C) {u v : Fin n} (adj : G.Adj u v) :
    ∃ j ∈ tops G C, gateVal n C j (pairInput u v) = true := by
  have A := ao_of n C least.1
  have compute (x : Fin n → Bool) : W n C x C.output = graphFun G ∅ x := congrFun least.2.1 x
  have on := (compute (pairInput u v)).trans ((graphFun_pair G u v).mpr adj)
  have valid : C.output < n+C.gates.length := by
    by_contra! h
    simp only [W] at on
    rw [getD_ge_length _ _ (by rw [wires_length]; omega)] at on
    contradiction
  obtain ⟨r,reach,leaf,yes⟩ := orR_leaf_true n C A _ C.output valid on
  rcases leaf with lo | ⟨k,rfl,hk,op⟩
  · let w : Fin n := ⟨r,lo⟩
    have single : W n C (pairInput w w) r = true := by
      rw [W_input n C _ r lo]
      simp [pairInput,w]
    have impossible := orR_mono n C A _ _ _ reach single
    rw [compute,graphFun_diag] at impossible
    contradiction
  · refine ⟨k,?_,yes⟩
    simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range]
    refine ⟨hk,op,?_⟩
    intro x hx
    exact (compute x).symm.trans (orR_mono n C A x _ _ reach hx)

private theorem choose_side {a b c d e f : Prop} (h : (a ∨ b) ∨ c) (i : (d ∨ e) ∨ f)
    (j : ¬(a ∧ e)) (k : ¬(b ∧ d)) : ((a ∨ c) ∧ (d ∨ f)) ∨ ((b ∨ c) ∧ (e ∨ f)) := by tauto

theorem block_edge (least : IsLeastAO G C) (top : TopForm G C) (u v : Fin n)
    (edge : s(u,v) ∈ Ustar G C) :
    (∀ w, signature G C w = signature G C v → G.Adj u w) ∨
    (∀ w, signature G C w = signature G C u → G.Adj w v) := by
  classical
  obtain ⟨mem,outside⟩ := Finset.mem_sdiff.mp edge
  have adj : G.Adj u v := G.mem_edgeFinset.mp mem
  obtain ⟨j,hj,on⟩ := edge_top G C least adj
  have info := hj
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at info
  obtain ⟨lt,op,clean⟩ := info
  have halves (b : Fin 2) (x y : Fin n) :
      W n C (pairInput x y) (opnd C j b) = true ↔
      (x ∈ side C j b ∨ y ∈ side C j b) ∨ marked G C j b x y := by
    rw [through_operand G C least.1 top lt op,base_pair]
    rfl
  have cross (x y : Fin n) (hx : x ∈ side C j 0) (hy : y ∈ side C j 1) :
      s(x,y) ∈ starEdges G C :=
    Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,rfl⟩⟩
  have neg1 : ¬ (u ∈ side C j 0 ∧ v ∈ side C j 1) := fun h => outside (cross _ _ h.1 h.2)
  have neg2 : ¬ (v ∈ side C j 0 ∧ u ∈ side C j 1) := by
    intro h
    exact outside (Sym2.eq_swap ▸ cross _ _ h.1 h.2)
  obtain ⟨h0,h1⟩ := (and_on C least.1 lt op _).mp on
  have a0 := (halves 0 u v).mp h0
  have a1 := (halves 1 u v).mp h1
  have choice : ((u ∈ side C j 0 ∨ marked G C j 0 u v) ∧ (u ∈ side C j 1 ∨ marked G C j 1 u v)) ∨
      ((v ∈ side C j 0 ∨ marked G C j 0 u v) ∧ (v ∈ side C j 1 ∨ marked G C j 1 u v)) := choose_side a0 a1 neg1 neg2
  have finish (x y : Fin n) (h : ∀ b : Fin 2, W n C (pairInput x y) (opnd C j b) = true) :
      G.Adj x y := (graphFun_pair G x y).mp (clean _ ((and_on C least.1 lt op _).mpr ⟨h 0,h 1⟩))
  rcases choice with h|h
  · left
    intro w eq
    apply finish
    intro b
    apply (halves _ _ _).mpr
    have val : u ∈ side C j b ∨ marked G C j b u v := by fin_cases b; exact h.1; exact h.2
    exact val.elim (fun x => Or.inl (Or.inl x)) (fun x => Or.inr (move_mark G C least.1 top rfl eq.symm x))
  · right
    intro w eq
    apply finish
    intro b
    apply (halves _ _ _).mpr
    have val : v ∈ side C j b ∨ marked G C j b u v := by fin_cases b; exact h.1; exact h.2
    exact val.elim (fun x => Or.inl (Or.inr x)) (fun x => Or.inr (move_mark G C least.1 top eq.symm rfl x))

#print axioms block_edge
end Simlowker.Types1735

/-! ## Counting the stars -/

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover
namespace Simlowker.Types1735
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

abbrev Color := {j // j ∈ junk G C} → Fin 2 → Bool

def fiber (S : Finset (Fin n)) (c : Color G C) := S.filter fun w => signature G C w = c

def centers (S Y : Finset (Fin n)) := S.filter fun x => ∀ y ∈ Y, G.Adj x y

def starBlock (S Y : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  ((centers G S Y) ×ˢ Y).image fun p => s(p.1,p.2)

theorem starBlock_bound (four : NoFourCycle G) {S Y : Finset (Fin n)} (ys : Y ⊆ S) :
    (starBlock G S Y).card ≤ S.card := by
  have bic : ∀ x ∈ centers G S Y, ∀ y ∈ Y, G.Adj x y := fun _ h => (Finset.mem_filter.mp h).2
  have h := Simlowker.Witness1735.biclique_small G four (centers G S Y) Y bic
  apply Finset.card_image_le.trans
  rw [Finset.card_product]
  rcases h with h|h
  · exact (Nat.mul_le_mul_right _ h).trans (by simpa using Finset.card_le_card ys)
  · exact (Nat.mul_le_mul_left _ h).trans (by simpa [centers] using Finset.card_le_card (Finset.filter_subset (fun x => ∀ y ∈ Y, G.Adj x y) S))

theorem residual_cover (least : IsLeastAO G C) (top : TopForm G C) :
    let S := G.support.toFinset
    Ustar G C ⊆ (S.image (signature G C)).biUnion (fun c => starBlock G S (fiber G C S c)) := by
  classical
  dsimp only
  let S := G.support.toFinset
  have add (x y : Fin n) (hx : x ∈ S) (hy : y ∈ S)
      (univ : ∀ w, signature G C w = signature G C y → G.Adj x w) :
      s(x,y) ∈ (S.image (signature G C)).biUnion (fun c => starBlock G S (fiber G C S c)) := by
    refine Finset.mem_biUnion.mpr ⟨_,Finset.mem_image_of_mem _ hy,Finset.mem_image.mpr ⟨(x,y),?_,rfl⟩⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hx,fun w hw => univ w (Finset.mem_filter.mp hw).2⟩,
      Finset.mem_filter.mpr ⟨hy,rfl⟩⟩
  intro e
  induction e using Sym2.inductionOn with
  | _ u v =>
    intro edge
    have adj : G.Adj u v := G.mem_edgeFinset.mp (Finset.mem_sdiff.mp edge).1
    have hu : u ∈ S := Set.mem_toFinset.mpr ⟨v,adj⟩
    have hv : v ∈ S := Set.mem_toFinset.mpr ⟨u,adj.symm⟩
    rcases block_edge G C least top u v edge with h|h
    · exact add u v hu hv h
    · rw [Sym2.eq_swap]
      exact add v u hv hu (fun w hw => (h w hw).symm)

theorem bound_by_types (four : NoFourCycle G) (least : IsLeastAO G C) (top : TopForm G C) :
    (Ustar G C).card ≤ (G.support.toFinset.image (signature G C)).card * G.support.ncard := by
  classical
  let S := G.support.toFinset
  let K := S.image (signature G C)
  have size : S.card = G.support.ncard := by simp [S,Set.ncard_eq_toFinset_card']
  calc
    _ ≤ _ := Finset.card_le_card (residual_cover G C least top)
    _ ≤ ∑ c ∈ K, (starBlock G S (fiber G C S c)).card := Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ K, S.card := Finset.sum_le_sum fun c _ => starBlock_bound G four (Finset.filter_subset _ S)
    _ = _ := by simp only [Finset.sum_const,Nat.nsmul_eq_mul,size]; rfl

theorem fixed_junk (four : NoFourCycle G) (least : IsLeastAO G C) (top : TopForm G C) :
    (Ustar G C).card ≤ 4 ^ (junk G C).card * (C.size + 1) := by
  classical
  have color_count : Fintype.card (Color G C) = 4 ^ (junk G C).card := by
    simp [Color]
  exact (bound_by_types G C four least top).trans
    (Nat.mul_le_mul ((Finset.card_le_univ _).trans_eq color_count) (PEqualNP.Outside.L_meta_2074 n G C least))

#print axioms fixed_junk
end Simlowker.Types1735

/-! ## An additive bound from singleton classes -/

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
namespace Simlowker.Types1735
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

def shared (x : Fin n) (p : Fin n × Fin n) := p.1 ≠ p.2 ∧ G.Adj x p.1 ∧ G.Adj x p.2

theorem incidence_bound (four : NoFourCycle G) (S Z : Finset (Fin n)) :
    (∑ x ∈ S, (Z.filter (G.Adj x)).card) ≤ S.card + Z.card ^ 2 := by
  classical
  let P := Z ×ˢ Z
  have row (x : Fin n) :
      (Z.filter (G.Adj x)).card ≤ 1 + ∑ p ∈ P, if shared G x p then 1 else 0 := by
    let D := Z.filter (G.Adj x)
    change D.card ≤ _
    by_cases empty : D = ∅
    · simp [empty]
    obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    let f := fun b : Fin n => (a,b)
    have inc : (D.erase a).image f ⊆ P.filter (shared G x) := by
      intro p hp
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨ba,bd⟩ := Finset.mem_erase.mp hb
      obtain ⟨az,xa⟩ := Finset.mem_filter.mp ha
      obtain ⟨bz,xb⟩ := Finset.mem_filter.mp bd
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨az,bz⟩,Ne.symm ba,xa,xb⟩
    have bound := Finset.card_le_card inc
    rw [Finset.card_image_of_injective _ (fun _ _ eq => congrArg Prod.snd eq),Finset.card_erase_of_mem ha] at bound
    calc
      D.card ≤ 1 + (P.filter (shared G x)).card := by omega
      _ = _ := by rw [Finset.card_filter]
  have col (p : Fin n × Fin n) : (∑ x ∈ S, if shared G x p then 1 else 0) ≤ 1 := by
    rw [← Finset.card_filter]
    by_cases diff : p.1 ≠ p.2
    · apply (Finset.card_le_card ?_).trans (four _ _ diff)
      intro x hx
      obtain ⟨_,_,a,b⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.symm,b.symm⟩
    · simp [shared,diff]
  calc
    _ ≤ ∑ x ∈ S, (1 + ∑ p ∈ P, if shared G x p then 1 else 0) := Finset.sum_le_sum fun x _ => row x
    _ = S.card + ∑ p ∈ P, ∑ x ∈ S, if shared G x p then 1 else 0 := by
      rw [Finset.sum_add_distrib,Finset.sum_comm (s := S) (t := P)]; simp
    _ ≤ S.card + ∑ _p ∈ P, 1 := Nat.add_le_add_left (Finset.sum_le_sum (fun p _ => col p)) _
    _ = _ := by simp [P,pow_two]

variable (C : Circuit)

def lone (S : Finset (Fin n)) := S.filter fun v => (fiber G C S (signature G C v)).card = 1

theorem additive_bound (four : NoFourCycle G) (least : IsLeastAO G C) (top : TopForm G C) :
    (Ustar G C).card ≤ 2 * G.support.ncard + (lone G C G.support.toFinset).card ^ 2 := by
  classical
  let S := G.support.toFinset
  let K := S.image (signature G C)
  let Y := fiber G C S
  let Z := lone G C S
  let A := K.filter fun c => (Y c).card ≠ 1
  let B := fun x => (Z.filter (G.Adj x)).image fun y => s(x,y)
  have cover : Ustar G C ⊆ (A.biUnion fun c => starBlock G S (Y c)) ∪ S.biUnion B := by
    intro e he
    obtain ⟨c,hc,ec⟩ := Finset.mem_biUnion.mp (residual_cover G C least top he)
    by_cases small : (Y c).card = 1
    · obtain ⟨⟨x,y⟩,xy,rfl⟩ := Finset.mem_image.mp ec
      obtain ⟨center,fy⟩ := Finset.mem_product.mp xy
      obtain ⟨_,adj⟩ := Finset.mem_filter.mp center
      obtain ⟨sy,sig⟩ := Finset.mem_filter.mp fy
      have yz : y ∈ Z := Finset.mem_filter.mpr ⟨sy,by change (Y (signature G C y)).card = 1; rw [sig]; exact small⟩
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨x,(Finset.mem_filter.mp center).1,
        Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨yz,adj y fy⟩,rfl⟩⟩))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr ⟨c,Finset.mem_filter.mpr ⟨hc,small⟩,ec⟩))
  have multi (c) (hc : c ∈ A) : (starBlock G S (Y c)).card ≤ (Y c).card := by
    apply Finset.card_image_le.trans
    rw [Finset.card_product]
    obtain small|small := Simlowker.Witness1735.biclique_small G four (centers G S (Y c)) (Y c)
      (fun _ h => (Finset.mem_filter.mp h).2)
    · simpa using Nat.mul_le_mul_right (Y c).card small
    · have ne := (Finset.mem_filter.mp hc).2
      have zero : (Y c).card = 0 := by omega
      simp [zero]
  have sumA : (A.biUnion fun c => starBlock G S (Y c)).card ≤ S.card := by
    calc
      _ ≤ ∑ c ∈ A, (starBlock G S (Y c)).card := Finset.card_biUnion_le
      _ ≤ ∑ c ∈ A, (Y c).card := Finset.sum_le_sum multi
      _ = (S.filter fun v => signature G C v ∈ A).card := Finset.sum_card_fiberwise_eq_card_filter _ _ _
      _ ≤ _ := Finset.card_le_card (Finset.filter_subset _ _)
  have sumB : (S.biUnion B).card ≤ S.card + Z.card^2 := by
    calc
      _ ≤ ∑ x ∈ S, (B x).card := Finset.card_biUnion_le
      _ ≤ ∑ x ∈ S, (Z.filter (G.Adj x)).card := Finset.sum_le_sum fun x _ => Finset.card_image_le
      _ ≤ _ := incidence_bound G four S Z
  have h := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  have size : S.card = G.support.ncard := by simp [S,Set.ncard_eq_toFinset_card']
  change (Ustar G C).card ≤ 2 * G.support.ncard + Z.card^2
  omega

#print axioms additive_bound
end Simlowker.Types1735

/-! ## Bounds in terms of the circuit size -/

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
namespace Simlowker.Types1735
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

theorem girth_four (hg : ∀ a : Fin n, ∀ p : G.Walk a a, p.IsCycle → 5 ≤ p.length) : NoFourCycle G := by
  have h := (Simlowker.Residual1735.girth_local G hg).2
  intro u v uv
  apply Finset.card_le_one_iff.mpr
  intro a b ha hb
  obtain ⟨_,ua,va⟩ := Finset.mem_filter.mp ha
  obtain ⟨_,ub,vb⟩ := Finset.mem_filter.mp hb
  exact h _ _ _ _ uv ua va ub vb

theorem lone_card (S : Finset (Fin n)) : (lone G C S).card ≤ 4 ^ (junk G C).card := by
  classical
  have inj : Set.InjOn (signature G C) (lone G C S : Set (Fin n)) := by
    intro u hu v hv eq
    obtain ⟨us,one⟩ := Finset.mem_filter.mp hu
    obtain ⟨vs,_⟩ := Finset.mem_filter.mp hv
    apply Finset.card_le_one_iff.mp (show (fiber G C S (signature G C u)).card ≤ 1 by omega)
    · exact Finset.mem_filter.mpr ⟨us,rfl⟩
    · exact Finset.mem_filter.mpr ⟨vs,eq.symm⟩
  have card := Finset.card_image_of_injOn inj
  have all := Finset.card_le_univ ((lone G C S).image (signature G C))
  rw [card] at all
  exact all.trans_eq (show Fintype.card (Color G C) = _ by simp [Color])

theorem girth_bounds (hg : ∀ a : Fin n, ∀ p : G.Walk a a, p.IsCycle → 5 ≤ p.length)
    (least : IsLeastAO G C) (top : TopForm G C) :
    (Ustar G C).card ≤ 4 ^ (junk G C).card * (C.size + 1) ∧
    (Ustar G C).card ≤ 2 * (C.size+1) + (lone G C G.support.toFinset).card ^ 2 ∧
    (Ustar G C).card ≤ 2 * (C.size+1) + 16 ^ (junk G C).card := by
  have four := girth_four G hg
  have add := additive_bound G C four least top
  have s := PEqualNP.Outside.L_meta_2074 n G C least
  have main := add.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 s) _)
  refine ⟨fixed_junk G C four least top, main, main.trans (Nat.add_le_add_left ?_ _)⟩
  have sq := Nat.pow_le_pow_left (lone_card G C G.support.toFinset) 2
  rw [← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul] at sq
  exact sq

#print axioms girth_bounds
end Simlowker.Types1735
