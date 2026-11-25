import PEqualNP.Outside.L_meta_1506

/-! ## Independent witnesses -/

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
namespace Simlowker.Witness1735
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : Nat)

def input (X : Finset (Fin n)) (v : Fin n) : Bool := decide (v ∈ X)
def bad (X : Finset (Fin n)) : Prop :=
  gateVal n C g (input X) = true ∧ ∀ u ∈ X, ∀ v ∈ X, ¬ G.Adj u v

theorem hits (ao : IsAO2 n C) (hg : g < C.gates.length) {X : Finset (Fin n)} (hx : bad G C g X)
    {w : Fin n} (hw : w ∈ wmax G C g) : ∃ v ∈ X, G.Adj v w := by
  let Y := insert w X
  have grows (v : Fin n) : input X v = true → input Y v = true := by
    simp only [input,decide_eq_true_eq]
    exact Finset.mem_insert_of_mem
  have val : gateVal n C g (input Y) = true :=
    PEqualNP.Outside.L_meta_1506.W_mono n C (PEqualNP.Outside.L_meta_1506.ao_of n C ao)
      (input X) (input Y) grows (n+g) (by omega) hx.1
  have cert := (Finset.mem_filter.mp hw).2 (input Y) val (by simp [input,Y])
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,
    decide_eq_true_eq,input] at cert
  obtain ⟨a,b,ab,ha,hb⟩ := cert
  rcases Finset.mem_insert.mp ha with ha|ha <;> rcases Finset.mem_insert.mp hb with hb|hb
  · exact False.elim (ab.ne (ha.trans hb.symm))
  · exact ⟨b,hb,ha ▸ ab.symm⟩
  · exact ⟨a,ha,hb ▸ ab⟩
  · exact False.elim (hx.2 a ha b hb ab)

theorem two_covers (four : NoFourCycle G) (W X Y : Finset (Fin n)) (dis : Disjoint X Y)
    (hx : ∀ w ∈ W, ∃ v ∈ X, G.Adj v w) (hy : ∀ w ∈ W, ∃ v ∈ Y, G.Adj v w) :
    W.card ≤ X.card * Y.card := by
  let common (p : Fin n × Fin n) := Finset.univ.filter fun w => G.Adj p.1 w ∧ G.Adj p.2 w
  have sub : W ⊆ (X ×ˢ Y).biUnion common := by
    intro w hw
    obtain ⟨x,xx,xw⟩ := hx w hw
    obtain ⟨y,yy,yw⟩ := hy w hw
    exact Finset.mem_biUnion.mpr ⟨(x,y),Finset.mem_product.mpr ⟨xx,yy⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,xw,yw⟩⟩
  calc W.card ≤ _ := Finset.card_le_card sub
       _ ≤ ∑ p ∈ X ×ˢ Y, (common p).card := Finset.card_biUnion_le
       _ ≤ ∑ _p ∈ X ×ˢ Y, 1 := by
         apply Finset.sum_le_sum
         rintro ⟨x,y⟩ hp
         obtain ⟨xx,yy⟩ := Finset.mem_product.mp hp
         exact four x y (fun eq => Finset.disjoint_left.mp dis xx (eq ▸ yy))
       _ = _ := by simp

theorem disjoint_bound (ao : IsAO2 n C) (hg : g < C.gates.length) (four : NoFourCycle G)
    {X Y : Finset (Fin n)} (hx : bad G C g X) (hy : bad G C g Y) (dis : Disjoint X Y) :
    (wmax G C g).card ≤ X.card * Y.card :=
  two_covers G four _ X Y dis (fun _ hw => hits G C g ao hg hx hw) (fun _ hw => hits G C g ao hg hy hw)

#print axioms disjoint_bound
end Simlowker.Witness1735

/-! ## Small witnesses share a vertex -/

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
namespace Simlowker.Witness1735
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : Nat)

theorem triangle_covers (four : NoFourCycle G) (W : Finset (Fin n)) {a b c : Fin n}
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (hits : ∀ w ∈ W, (G.Adj a w ∨ G.Adj b w) ∧ (G.Adj a w ∨ G.Adj c w) ∧
      (G.Adj b w ∨ G.Adj c w)) : W.card ≤ 3 := by
  let M (x y : Fin n) := Finset.univ.filter fun w => G.Adj x w ∧ G.Adj y w
  have sub : W ⊆ (M a b ∪ M a c) ∪ M b c := by
    intro w hw
    obtain ⟨hab,hac,hbc⟩ := hits w hw
    simp only [M,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
    tauto
  have c1 : (M a b).card ≤ 1 := four a b ab
  have c2 : (M a c).card ≤ 1 := four a c ac
  have c3 : (M b c).card ≤ 1 := four b c bc
  have u1 := Finset.card_union_le (M a b) (M a c)
  have u2 := Finset.card_union_le (M a b ∪ M a c) (M b c)
  have u3 := Finset.card_le_card sub
  omega

theorem small_witness_star (ao : IsAO2 n C) (hg : g < C.gates.length) (four : NoFourCycle G)
    (wide : 4 < (wmax G C g).card)
    (nonempty : ∃ X : Finset (Fin n), X.card ≤ 2 ∧ bad G C g X) :
    ∃ a : Fin n, ∀ X : Finset (Fin n), X.card ≤ 2 → bad G C g X → a ∈ X := by
  classical
  have cross {X Y : Finset (Fin n)} (sx : X.card ≤ 2) (sy : Y.card ≤ 2)
      (bx : bad G C g X) (byy : bad G C g Y) : ∃ v, v ∈ X ∧ v ∈ Y := by
    by_contra! no
    have dis : Disjoint X Y := Finset.disjoint_left.mpr no
    have cap := disjoint_bound G C g ao hg four bx byy dis
    have p := Nat.mul_le_mul sx sy
    omega
  have pair {v w : Fin n} {X : Finset (Fin n)} (vw : v ≠ w) (vx : v ∈ X) (wx : w ∈ X)
      (size : X.card ≤ 2) : X = {v,w} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro t ht
      simp only [Finset.mem_insert,Finset.mem_singleton] at ht
      rcases ht with rfl|rfl <;> assumption
    · simpa [vw] using size
  obtain ⟨X,sx,bx⟩ := nonempty
  by_cases small : X.card ≤ 1
  · obtain ⟨v,hv,_⟩ := cross sx sx bx bx
    refine ⟨v,?_⟩
    intro Y sy byy
    obtain ⟨w,wx,wy⟩ := cross sx sy bx byy
    exact (Finset.card_le_one_iff.mp small wx hv) ▸ wy
  · obtain ⟨a,b,ab,rfl⟩ := Finset.card_eq_two.mp (show X.card=2 by omega)
    by_contra! no
    obtain ⟨Y,sy,byy,na⟩ := no a
    obtain ⟨Z,sz,bz,nb⟩ := no b
    obtain ⟨d,hd,dy⟩ := cross sx sy bx byy
    obtain ⟨e,he,ez⟩ := cross sx sz bx bz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hd he
    have bin : b ∈ Y := by rcases hd with h|h <;> subst d <;> tauto
    have ain : a ∈ Z := by rcases he with h|h <;> subst e <;> tauto
    obtain ⟨c,cy,cz⟩ := cross sy sz byy bz
    have ac : a ≠ c := fun eq => na (eq ▸ cy)
    have bc : b ≠ c := fun eq => nb (eq ▸ cz)
    obtain rfl := pair bc bin cy sy
    obtain rfl := pair ac ain cz sz
    have cover {u v : Fin n} (badpair : bad G C g {u,v}) (w : Fin n) (hw : w ∈ wmax G C g) :
        G.Adj u w ∨ G.Adj v w := by
      obtain ⟨x,hx,h⟩ := hits G C g ao hg badpair hw
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl <;> tauto
    have narrow := triangle_covers G four (wmax G C g) ab ac bc
      (fun w hw => ⟨cover bx w hw,cover bz w hw,cover byy w hw⟩)
    omega

#print axioms small_witness_star
end Simlowker.Witness1735

/-! ## The two input sides of a wide gate -/

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
namespace Simlowker.Witness1735
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : Nat)

theorem pair_bad {u v : Fin n} (off : ¬ G.Adj u v) (on : gateVal n C g (pairInput u v) = true) :
    bad G C g {u,v} := by
  constructor
  · have eq : input ({u,v} : Finset (Fin n)) = pairInput u v := by
      funext w
      simp [input,pairInput]
    rwa [eq]
  · intro a ha b hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> first | exact G.loopless.irrefl _ | exact off | exact fun h => off h.symm

theorem clean_off_vertex (ao : IsAO2 n C) (hg : g < C.gates.length) (four : NoFourCycle G)
    (wide : 4 < (wmax G C g).card) :
    ∃ a : Fin n, ∀ u v : Fin n, u ≠ a → v ≠ a → gateVal n C g (pairInput u v) = true → G.Adj u v := by
  classical
  by_cases small : ∃ X : Finset (Fin n), X.card ≤ 2 ∧ bad G C g X
  · obtain ⟨a,star⟩ := small_witness_star G C g ao hg four wide small
    refine ⟨a,?_⟩
    intro u v ua va on
    by_contra no
    have e := star {u,v} (Finset.card_le_two) (pair_bad G C g no on)
    simp [Ne.symm ua,Ne.symm va] at e
  · obtain ⟨a,_⟩ := Finset.card_pos.mp (show 0 < (wmax G C g).card by omega)
    refine ⟨a,?_⟩
    intro u v _ _ on
    by_contra no
    exact small ⟨{u,v},Finset.card_le_two,pair_bad G C g no on⟩

open PEqualNP.Outside.L_meta_1506 in
theorem cross_enabled (ao : IsAO2 n C) (hg : g < C.gates.length) (op : (gateAt C g).op = GateOp.and)
    {u v : Fin n} (hu : u ∈ side C g 0) (hv : v ∈ side C g 1) :
    gateVal n C g (pairInput u v) = true := by
  have A := ao_of n C ao
  obtain ⟨a,b,ins,ha,hb⟩ := (A g hg).2
  change u ∈ orIn n C (opnd C g 0) at hu
  change v ∈ orIn n C (opnd C g 1) at hv
  have ea : opnd C g 0 = a := by simp [opnd,ins,List.getD]
  have eb : opnd C g 1 = b := by simp [opnd,ins,List.getD]
  rw [ea] at hu
  rw [eb] at hv
  have left := orR_mono n C A (pairInput u v) a u.val ((orIn_iff n C A a u).mp hu)
    (by rw [W_input n C _ _ u.isLt]; simp [pairInput])
  have right := orR_mono n C A (pairInput u v) b v.val ((orIn_iff n C A b v).mp hv)
    (by rw [W_input n C _ _ v.isLt]; simp [pairInput])
  change W n C _ (n+g) = _
  rw [W_and n C _ g hg op a b ins ha hb,left,right]
  rfl

theorem biclique_small (four : NoFourCycle G) (X Y : Finset (Fin n))
    (bic : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y) : X.card ≤ 1 ∨ Y.card ≤ 1 := by
  by_cases h : X.card ≤ 1
  · exact Or.inl h
  · right
    obtain ⟨u,hu,v,hv,uv⟩ := Finset.one_lt_card.mp (by omega : 1 < X.card)
    exact (Finset.card_le_card (show Y ⊆ Finset.univ.filter (fun w => G.Adj u w ∧ G.Adj v w) by
      intro w hw; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,bic u hu w hw,bic v hv w hw⟩)).trans (four u v uv)

theorem wide_side_structure (ao : IsAO2 n C) (hg : g < C.gates.length) (op : (gateAt C g).op = GateOp.and)
    (four : NoFourCycle G) (wide : 4 < (wmax G C g).card) :
    ∃ a : Fin n,
      (∀ u ∈ (side C g 0).erase a, ∀ v ∈ (side C g 1).erase a, G.Adj u v) ∧
      (((side C g 0).erase a).card ≤ 1 ∨ ((side C g 1).erase a).card ≤ 1) := by
  obtain ⟨a,h⟩ := clean_off_vertex G C g ao hg four wide
  refine ⟨a,?_,?_⟩
  · intro u hu v hv
    obtain ⟨ua,uu⟩ := Finset.mem_erase.mp hu
    obtain ⟨va,vv⟩ := Finset.mem_erase.mp hv
    exact h u v ua va (cross_enabled C g ao hg op uu vv)
  · apply biclique_small G four
    intro u hu v hv
    obtain ⟨ua,uu⟩ := Finset.mem_erase.mp hu
    obtain ⟨va,vv⟩ := Finset.mem_erase.mp hv
    exact h u v ua va (cross_enabled C g ao hg op uu vv)

#print axioms wide_side_structure
end Simlowker.Witness1735

/-! ## Routing true pairs to an earlier AND -/

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover
namespace Simlowker.Witness1735
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : Nat)

/-- A true pair can be followed through OR gates to this earlier AND. -/
def routed (q : Nat) (u v : Fin n) :=
  ∃ k < g, (gateAt C k).op = GateOp.and ∧ OrReaches n C q k ∧ gateVal n C k (pairInput u v) = true

open PEqualNP.Outside.L_meta_1506 in
theorem route_operand (ao : IsAO2 n C) (hg : g < C.gates.length) (q : Nat) (hq : q < n+g)
    (u v : Fin n) (on : W n C (pairInput u v) q = true) :
    (u ∈ orIn n C q ∨ v ∈ orIn n C q) ∨ routed C g q u v := by
  have A := ao_of n C ao
  obtain ⟨r,reach,leaf,h⟩ := orR_leaf_true n C A _ q (by omega) on
  rcases leaf with hi | ⟨k,rfl,hk,andOp⟩
  · rw [W_input n C _ r hi] at h
    obtain hu|hv := of_decide_eq_true h
    · exact Or.inl (Or.inl ((orIn_iff n C A q u).mpr (by simpa [←hu] using reach)))
    · exact Or.inl (Or.inr ((orIn_iff n C A q v).mpr (by simpa [←hv] using reach)))
  · right
    have le := orR_le n C A _ _ reach
    exact ⟨k,by omega,andOp,(orReaches_iff n C A q k).mpr ⟨by omega,hk,reach⟩,h⟩

open PEqualNP.Outside.L_meta_1506 in
theorem both_routes (ao : IsAO2 n C) (hg : g < C.gates.length) (op : (gateAt C g).op = GateOp.and)
    (u v : Fin n) (enabled : gateVal n C g (pairInput u v) = true) :
    ∀ b : Fin 2, (u ∈ side C g b ∨ v ∈ side C g b) ∨ routed C g (opnd C g b) u v := by
  have A := ao_of n C ao
  obtain ⟨a,b,ins,ha,hb⟩ := (A g hg).2
  change W n C (pairInput u v) (n+g) = true at enabled
  rw [W_and n C _ g hg op a b ins ha hb,Bool.and_eq_true_iff] at enabled
  intro i
  fin_cases i
  · simpa [side,opnd,ins,List.getD] using route_operand C g ao hg a ha u v enabled.1
  · simpa [side,opnd,ins,List.getD] using route_operand C g ao hg b hb u v enabled.2

theorem wide_routing (ao : IsAO2 n C) (hg : g < C.gates.length) (op : (gateAt C g).op = GateOp.and)
    (four : NoFourCycle G) (wide : 4 < (wmax G C g).card) :
    ∃ T : Finset (Fin n), T.card ≤ 2 ∧ ∀ u v : Fin n, gateVal n C g (pairInput u v) = true →
      u ∈ T ∨ v ∈ T ∨ ∃ b : Fin 2, routed C g (opnd C g b) u v := by
  classical
  obtain ⟨a,_,small⟩ := wide_side_structure G C g ao hg op four wide
  have sideChoice : ∃ b : Fin 2, ((side C g b).erase a).card ≤ 1 := by
    rcases small with h|h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
  obtain ⟨b,hb⟩ := sideChoice
  let T := insert a ((side C g b).erase a)
  have sub : side C g b ⊆ T := by
    intro t ht
    by_cases h : t=a
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨h,ht⟩))
  have bound := Finset.card_insert_le a ((side C g b).erase a)
  refine ⟨T,by dsimp [T]; omega,?_⟩
  intro u v on
  rcases both_routes C g ao hg op u v on b with (hu|hv)|rec
  · exact Or.inl (sub hu)
  · exact Or.inr (Or.inl (sub hv))
  · exact Or.inr (Or.inr ⟨b,rec⟩)

#print axioms wide_routing
end Simlowker.Witness1735
