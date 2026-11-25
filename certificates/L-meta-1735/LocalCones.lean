import MatchingBounds

/-! ## Independent representatives of large sets -/

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
namespace Simlowker.Transversal1735
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

def independent (I : Finset (Fin n)) := ∀ x ∈ I, ∀ y ∈ I, ¬G.Adj x y

theorem at_most_one_center (four : NoFourCycle G) (A B : Finset (Fin n)) (L : Nat)
    (large : 2*L ≤ B.card) :
    (A.filter fun x => (B.filter fun y => ¬G.Adj x y).card < L).card ≤ 1 := by
  classical
  apply Finset.card_le_one_iff.mpr
  intro x y hx hy
  by_contra diff
  let X := B.filter fun w => ¬G.Adj x w
  let Y := B.filter fun w => ¬G.Adj y w
  let N := Finset.univ.filter fun w => G.Adj x w ∧ G.Adj y w
  have bound : B ⊆ (X ∪ Y) ∪ N := by
    intro z hz
    by_cases a : G.Adj x z
    · by_cases b : G.Adj y z
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,b⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz,b⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz,a⟩))
  have h := (Finset.card_le_card bound).trans (Finset.card_union_le _ _)
  have xy := Finset.card_union_le X Y
  have xn : X.card < L := (Finset.mem_filter.mp hx).2
  have yn : Y.card < L := (Finset.mem_filter.mp hy).2
  have cn : N.card ≤ 1 := four x y diff
  omega

theorem sharp_transversal (four : NoFourCycle G) (k : Nat) (F : Fin k → Finset (Fin n))
    (S : Finset (Fin n)) (big : ∀ i, 2^(k-1) ≤ ((F i) ∩ S).card) :
    ∃ I ⊆ S, independent G I ∧ ∀ i, ∃ v ∈ I, v ∈ F i := by
  classical
  induction k generalizing S with
  | zero => exact ⟨∅,Finset.empty_subset _,by simp [independent],fun i => Fin.elim0 i⟩
  | succ k ih =>
    let L := 2^(k-1)
    let A := F 0 ∩ S
    let B (i : Fin k) := F i.succ ∩ S
    let bad (i : Fin k) := A.filter fun x => ((B i).filter fun y => ¬G.Adj x y).card < L
    have large (i : Fin k) : 2*L ≤ (B i).card := by
      have ki := i.isLt
      have eq : (k-1).succ = k := by omega
      have h := big i.succ
      change 2^(k+1-1) ≤ _ at h
      simpa only [L,B,←Nat.pow_succ',eq,Nat.add_sub_cancel] using h
    have count : (Finset.univ.biUnion bad).card ≤ k := by
      calc
        _ ≤ ∑ i : Fin k, (bad i).card := Finset.card_biUnion_le
        _ ≤ ∑ _i : Fin k, 1 := Finset.sum_le_sum fun i _ => at_most_one_center G four A (B i) L (large i)
        _ = _ := by simp
    have enough : k < A.card := by
      have h := big 0
      have p : k < 2^k := Nat.lt_two_pow_self
      simpa only [Nat.add_sub_cancel] using p.trans_le (show 2^k ≤ A.card by simpa [A] using h)
    have existsX : ∃ x ∈ A, x ∉ Finset.univ.biUnion bad := by
      by_contra! no
      exact (Nat.not_le_of_gt enough) ((Finset.card_le_card no).trans count)
    obtain ⟨x,hx,good⟩ := existsX
    let T := S.filter fun y => ¬G.Adj x y
    have next (i : Fin k) : L ≤ ((F i.succ) ∩ T).card := by
      have absent : x ∉ bad i := fun h => good (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,h⟩)
      have le : L ≤ ((B i).filter fun y => ¬G.Adj x y).card := by
        by_contra! small
        exact absent (Finset.mem_filter.mpr ⟨hx,small⟩)
      have eq : (B i).filter (fun y => ¬G.Adj x y) = F i.succ ∩ T := by ext w; simp [B,T,and_assoc]
      rwa [←eq]
    obtain ⟨I,sub,ind,hit⟩ := ih (fun i => F i.succ) T next
    refine ⟨insert x I,Finset.insert_subset (Finset.mem_inter.mp hx).2 (sub.trans (Finset.filter_subset _ _)),?_,?_⟩
    · intro a ha b hb
      rcases Finset.mem_insert.mp ha with ax|ai <;> rcases Finset.mem_insert.mp hb with bx|bi
      · rw [ax,bx]; exact G.loopless.irrefl _
      · rw [ax]; exact (Finset.mem_filter.mp (sub bi)).2
      · rw [bx]; exact fun h => (Finset.mem_filter.mp (sub ai)).2 h.symm
      · exact ind a ai b bi
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨x,Finset.mem_insert_self _ _,(Finset.mem_inter.mp hx).1⟩
      · obtain ⟨v,hv,vf⟩ := hit j
        exact ⟨v,Finset.mem_insert_of_mem hv,vf⟩

theorem transversal (four : NoFourCycle G) (k : Nat) (F : Fin k → Finset (Fin n))
    (S : Finset (Fin n)) (big : ∀ i, 2^(k+1) ≤ ((F i) ∩ S).card) :
    ∃ I ⊆ S, independent G I ∧ ∀ i, ∃ v ∈ I, v ∈ F i := by
  apply sharp_transversal G four
  intro i
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) (show k-1 ≤ k+1 by omega)).trans (big i)

#print axioms transversal
end Simlowker.Transversal1735

/-! ## Counting edges covered by a large OR wire -/

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_1506
namespace Simlowker.Transversal1735
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

def front (L : Nat) (u v : Fin n) := ∃ h < C.gates.length, ∃ b : Fin 2,
  2*L ≤ (orIn n C (n+h)).card ∧ ((orIn n C (n+h)).filter (fun y => ¬G.Adj u y)).card < L ∧
  v ∈ side C h b ∧ (side (n:=n) C h b).card < 2*L

theorem wire_frontier (ao : IsAO2 n C) {L : Nat} (pos : 0 < L) (u v : Fin n) (q : Nat)
    (wide : 2*L ≤ (orIn n C q).card) (near : ((orIn n C q).filter fun y => ¬G.Adj u y).card < L)
    (visible : v ∈ orIn n C q) : front G C L u v := by
  have A := ao_of n C ao
  have inSmall (w : Fin n) : orIn n C w.val = {w} := by
    ext x
    rw [orIn_iff n C A,Finset.mem_singleton]
    constructor
    · intro p
      rcases Relation.ReflTransGen.cases_head p with eq | ⟨z,⟨k,bad,_,_,_⟩,_⟩
      · exact Fin.ext eq.symm
      · have := w.isLt
        omega
    · rintro rfl
      exact .refl
  induction q using Nat.strong_induction_on with
  | ind q ih =>
    rcases Relation.ReflTransGen.cases_head ((orIn_iff n C A q v).mp visible) with eq|⟨z,step,path⟩
    · rw [eq,inSmall,Finset.card_singleton] at wide
      omega
    · have smaller := orStep_lt n C A _ _ step
      have inc : orIn n C z ⊆ orIn n C q := fun x hx =>
        (orIn_iff n C A _ _).mpr (Relation.ReflTransGen.head step ((orIn_iff n C A _ _).mp hx))
      have vz := (orIn_iff n C A z v).mpr path
      by_cases wz : 2*L ≤ (orIn n C z).card
      · exact ih z smaller wz ((Finset.card_le_card (Finset.filter_subset_filter _ inc)).trans_lt near) vz
      · obtain ⟨h,rfl,hlt,_,zin⟩ := step
        obtain ⟨a,d,ins,_,_⟩ := (A h hlt).2
        rw [ins] at zin
        simp only [List.mem_cons,List.not_mem_nil,or_false] at zin
        have operand : ∃ b : Fin 2, opnd C h b = z := by
          rcases zin with rfl|rfl
          · exact ⟨0,by simp [opnd,ins,List.getD]⟩
          · exact ⟨1,by simp [opnd,ins,List.getD]⟩
        obtain ⟨b,eb⟩ := operand
        exact ⟨h,hlt,b,wide,near,by simpa [side,eb] using vz,by simpa [side,eb] using Nat.lt_of_not_ge wz⟩

def wideCenters (L h : Nat) : Finset (Fin n) :=
  let P := orIn n C (n+h)
  if 2*L ≤ P.card then Finset.univ.filter (fun u => (P.filter (fun y => ¬G.Adj u y)).card < L) else ∅

def tips (L h : Nat) (b : Fin 2) : Finset (Fin n) :=
  let S := side (n:=n) C h b
  if S.card < 2*L then S else ∅

def frontEdges (L : Nat) : Finset (Sym2 (Fin n)) :=
  ((Finset.range C.gates.length) ×ˢ (Finset.univ : Finset (Fin 2))).biUnion fun p =>
    (wideCenters G C L p.1 ×ˢ tips (n:=n) C L p.1 p.2).image (fun q => s(q.1,q.2))

theorem front_in {L : Nat} {u v : Fin n} (h : front G C L u v) : s(u,v) ∈ frontEdges G C L := by
  obtain ⟨a,ha,b,wide,near,vb,narrow⟩ := h
  exact Finset.mem_biUnion.mpr ⟨(a,b),Finset.mem_product.mpr ⟨Finset.mem_range.mpr ha,Finset.mem_univ _⟩,
    Finset.mem_image.mpr ⟨(u,v),Finset.mem_product.mpr
      ⟨by simpa [wideCenters,wide] using near,by simpa [tips,narrow] using vb⟩,rfl⟩⟩

theorem front_count (four : NoFourCycle G) (L : Nat) :
    (frontEdges G C L).card ≤ (4*L)*C.size := by
  classical
  let U := (Finset.range C.gates.length) ×ˢ (Finset.univ : Finset (Fin 2))
  have centers (h) : (wideCenters G C L h).card ≤ 1 := by
    by_cases big : 2*L ≤ (orIn n C (n+h)).card
    · simpa [wideCenters,big] using at_most_one_center G four Finset.univ _ L big
    · simp [wideCenters,big]
  have leaves (h b) : (tips (n:=n) C L h b).card ≤ 2*L := by
    by_cases sm : (side (n:=n) C h b).card < 2*L
    · simpa [tips,sm] using sm.le
    · simp [tips,sm]
  calc
    _ ≤ ∑ p ∈ U, ((wideCenters G C L p.1 ×ˢ tips (n:=n) C L p.1 p.2).image (fun q => s(q.1,q.2))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ U, 2*L := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.card_image_le.trans
      rw [Finset.card_product]
      simpa only [one_mul] using Nat.mul_le_mul (centers p.1) (leaves p.1 p.2)
    _ = _ := by simp [U,Circuit.size]; ring

#print axioms wire_frontier
#print axioms front_count
end Simlowker.Transversal1735

/-! ## The input wires relevant to one clean top -/

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1506 Simlowker.Types1735
namespace Simlowker.Transversal1735
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

noncomputable def relevant (j : Nat) : Finset Nat := by
  classical
  exact insert j ((junk G C).filter (fun k => ancestor G C k j))

noncomputable def ports (j : Nat) : Finset Nat :=
  (relevant G C j ×ˢ (Finset.univ : Finset (Fin 2))).image (fun p => opnd C p.1 p.2)

theorem port_mem {j k : Nat} (p : k=j ∨ ancestor G C k j) (b : Fin 2) : opnd C k b ∈ ports G C j := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨(k,b),Finset.mem_product.mpr ⟨?_,Finset.mem_univ _⟩,rfl⟩
  exact Finset.mem_insert.mpr (p.imp_right (fun a => Finset.mem_filter.mpr ⟨ancestor_dirty G C a,a⟩))

theorem port_transfer (ao : IsAO2 n C) (top : TopForm G C) {j : Nat} (hj : j ∈ tops G C)
    {u v : Fin n} (on : gateVal n C j (pairInput u v) = true) (y : Fin n → Bool)
    (enough : ∀ q ∈ ports G C j, (u ∈ orIn n C q ∨ v ∈ orIn n C q) →
      ∃ w ∈ orIn n C q, y w = true) : graphFun G ∅ y = true := by
  have info := hj
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at info
  obtain ⟨lt,op,clean⟩ := info
  have profile (k : Nat) (p : k=j ∨ ancestor G C k j) (b : Fin 2) :
      baseOn C k b (pairInput u v) → baseOn C k b y := by
    intro src
    exact enough _ (port_mem G C p b) ((base_pair C k b u v).mp src)
  have operand (b : Fin 2) (orig : W n C (pairInput u v) (opnd C j b) = true) :
      W n C y (opnd C j b) = true := by
    apply (through_operand G C ao top lt op b y).mpr
    rcases (through_operand G C ao top lt op b _).mp orig with lit|⟨k,sm,dirty,reach,active⟩
    · exact Or.inl (profile j (Or.inl rfl) b lit)
    · exact Or.inr ⟨k,sm,dirty,reach,local_transfer G C ao top j _ _
        (fun i p a => profile i (Or.inr p) a) k (.single ⟨sm,dirty,b,reach⟩) dirty active⟩
  obtain ⟨h0,h1⟩ := (and_on C ao lt op _).mp on
  exact clean _ ((and_on C ao lt op y).mpr ⟨operand 0 h0,operand 1 h1⟩)

def missing (R : Finset Nat) (u v : Fin n) := R.filter (fun q => v ∈ orIn n C q ∧ u ∉ orIn n C q)

theorem missing_near (four : NoFourCycle G) (R : Finset Nat) {u v : Fin n}
    (guard : ∀ y : Fin n → Bool, (∀ q ∈ R, (u ∈ orIn n C q ∨ v ∈ orIn n C q) →
      ∃ w ∈ orIn n C q, y w = true) → graphFun G ∅ y = true) :
    ∃ q ∈ missing C R u v,
      ((orIn n C q).filter fun y => ¬G.Adj u y).card < 2^((missing C R u v).card-1) := by
  classical
  by_contra! all
  let S := Finset.univ.filter (fun w => ¬G.Adj u w)
  let need := missing C R u v
  let e : Fin need.card ≃ {q // q ∈ need} := (Fintype.equivFinOfCardEq (Fintype.card_coe need)).symm
  have adj (q) : orIn n C q ∩ S = ((orIn n C q).filter fun y => ¬G.Adj u y) := by
    ext w; simp [S]
  have bound (i : Fin need.card) : 2^(need.card-1) ≤ (orIn n C (e i).val ∩ S).card := by
    rw [adj]
    exact all _ (e i).property
  obtain ⟨I,isub,ind,hits⟩ := sharp_transversal G four need.card (fun i => orIn n C (e i).val) S bound
  let A := insert u I
  let y := fun x : Fin n => decide (x ∈ A)
  have yes := guard y (by
    intro q port seen
    by_cases uq : u ∈ orIn n C q
    · exact ⟨u,uq,by simp [y,A]⟩
    · have vq := seen.resolve_left uq
      let w : {q // q ∈ need} := ⟨q,Finset.mem_filter.mpr ⟨port,vq,uq⟩⟩
      obtain ⟨z,zi,zq⟩ := hits (e.symm w)
      rw [e.apply_symm_apply] at zq
      exact ⟨z,zq,decide_eq_true (Finset.mem_insert_of_mem zi)⟩)
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq,y] at yes
  obtain ⟨a,b,ab,ha,hb⟩ := yes
  rcases Finset.mem_insert.mp ha with au|ai <;> rcases Finset.mem_insert.mp hb with bu|bi
  · exact ab.ne (au.trans bu.symm)
  · exact (Finset.mem_filter.mp (isub bi)).2 (au ▸ ab)
  · exact (Finset.mem_filter.mp (isub ai)).2 (bu ▸ ab.symm)
  · exact ind a ai b bi ab

theorem family_near (four : NoFourCycle G) (R : Finset Nat) {u v : Fin n}
    (guard : ∀ y : Fin n → Bool, (∀ q ∈ R, (u ∈ orIn n C q ∨ v ∈ orIn n C q) →
      ∃ w ∈ orIn n C q, y w = true) → graphFun G ∅ y = true) :
    ∃ q ∈ R, v ∈ orIn n C q ∧
      ((orIn n C q).filter fun y => ¬G.Adj u y).card < 2^(R.card+1) := by
  obtain ⟨q,hq,near⟩ := missing_near G C four R guard
  have sub : (missing C R u v).card ≤ R.card := Finset.card_le_card (Finset.filter_subset _ _)
  have info := Finset.mem_filter.mp hq
  exact ⟨q,info.1,info.2.1,near.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))⟩

theorem almost_neighbors (four : NoFourCycle G) (ao : IsAO2 n C) (top : TopForm G C)
    {j : Nat} (hj : j ∈ tops G C) {u v : Fin n} (on : gateVal n C j (pairInput u v) = true) :
    ∃ q ∈ ports G C j, v ∈ orIn n C q ∧
    ((orIn n C q).filter fun y => ¬G.Adj u y).card < 2^((ports G C j).card+1) :=
  family_near G C four _ (port_transfer G C ao top hj on)

#print axioms almost_neighbors
end Simlowker.Transversal1735

/-! ## A linear bound with bounded local cones -/

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open Simlowker.Types1735
namespace Simlowker.Transversal1735
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

noncomputable def shortInputs (L j : Nat) : Finset (Fin n) :=
  ((ports G C j).filter fun q => (orIn n C q).card < 2*L).biUnion (orIn n C)

theorem short_count (L j : Nat) : (shortInputs G C L j).card ≤ (ports G C j).card*(2*L) := by
  classical
  let A := (ports G C j).filter fun q => (orIn n C q).card < 2*L
  calc
    _ ≤ ∑ q ∈ A, (orIn n C q).card := Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ A, 2*L := Finset.sum_le_sum (fun q h => (Finset.mem_filter.mp h).2.le)
    _ = A.card*(2*L) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.filter_subset _ _))

theorem dichotomy (four : NoFourCycle G) (ao : IsAO2 n C) (top : TopForm G C) {j K : Nat}
    (hj : j ∈ tops G C) (width : (ports G C j).card ≤ K) {u v : Fin n}
    (on : gateVal n C j (pairInput u v) = true) :
    let L := 2^(K+1)
    s(u,v) ∈ frontEdges G C L ∨ v ∈ shortInputs G C L j := by
  let L := 2^(K+1)
  have pos : 0 < L := Nat.pow_pos (by decide)
  obtain ⟨q,hq,vq,near⟩ := almost_neighbors G C four ao top hj on
  have closer : ((orIn n C q).filter fun y => ¬G.Adj u y).card < L := near.trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.add_le_add_right width 1))
  by_cases big : 2*L ≤ (orIn n C q).card
  · exact Or.inl (front_in G C (wire_frontier G C ao pos u v q big closer vq))
  · exact Or.inr (Finset.mem_biUnion.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,Nat.lt_of_not_ge big⟩,vq⟩)

theorem covered_edges (four : NoFourCycle G) (ao : IsAO2 n C) (top : TopForm G C)
    (E : Finset (Sym2 (Fin n))) (K : Nat)
    (hit : ∀ u v, s(u,v) ∈ E → ∃ j ∈ tops G C, (ports G C j).card ≤ K ∧ gateVal n C j (pairInput u v) = true) :
    let L := 2^(K+1)
    E.card ≤ (4*L+(K*(2*L))^2)*C.size := by
  classical
  let L := 2^(K+1)
  let A := (tops G C).filter fun j => (ports G C j).card ≤ K
  let D := fun j => ((shortInputs G C L j) ×ˢ (shortInputs G C L j)).image fun p => s(p.1,p.2)
  have inc : E ⊆ frontEdges G C L ∪ A.biUnion D := by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
      intro he
      obtain ⟨j,hj,width,on⟩ := hit u v he
      have swap : pairInput v u = pairInput u v := by funext w; simp [pairInput,or_comm]
      have on' : gateVal n C j (pairInput v u) = true := by rwa [swap]
      rcases dichotomy G C four ao top hj width on with done|hv
      · exact Finset.mem_union_left _ done
      rcases dichotomy G C four ao top hj width on' with done|hu
      · exact Finset.mem_union_left _ (Sym2.eq_swap ▸ done)
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,Finset.mem_filter.mpr ⟨hj,width⟩,
        Finset.mem_image.mpr ⟨(u,v),Finset.mem_product.mpr ⟨hu,hv⟩,rfl⟩⟩)
  have cost (j) (hj : j ∈ A) : (D j).card ≤ (K*(2*L))^2 := by
    have w := (Finset.mem_filter.mp hj).2
    have t := (short_count G C L j).trans (Nat.mul_le_mul_right _ w)
    apply Finset.card_image_le.trans
    rw [Finset.card_product,pow_two]
    exact Nat.mul_le_mul t t
  have amount : A.card ≤ C.size := by
    have sub : A ⊆ Finset.range C.gates.length := by
      intro i hi
      have ht := (Finset.mem_filter.mp hi).1
      simp only [tops,gatesWhere,Finset.mem_filter] at ht
      exact ht.1
    exact (Finset.card_le_card sub).trans_eq (Finset.card_range _)
  have allD : (A.biUnion D).card ≤ C.size * (K*(2*L))^2 := by
    calc
      _ ≤ ∑ j ∈ A, (D j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ A, (K*(2*L))^2 := Finset.sum_le_sum cost
      _ = _ := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ amount
  have wide := front_count G C four L
  have upper := (Finset.card_le_card inc).trans (Finset.card_union_le _ _)
  exact upper.trans ((Nat.add_le_add wide allD).trans_eq (by ring))

theorem bounded_local_gates (hg : ∀ a : Fin n, ∀ p : G.Walk a a, p.IsCycle → 5 ≤ p.length)
    (least : IsLeastAO G C) (top : TopForm G C) (d : Nat)
    (width : ∀ j ∈ tops G C, (relevant G C j).card ≤ d+1) :
    let K := 2*(d+1)
    let L := 2^(K+1)
    G.edgeFinset.card ≤ (4*L+(K*(2*L))^2)*C.size := by
  apply covered_edges G C (girth_four G hg) least.1 top
  intro u v edge
  obtain ⟨j,hj,on⟩ := edge_top G C least (G.mem_edgeFinset.mp edge)
  refine ⟨j,hj,?_,on⟩
  apply Finset.card_image_le.trans
  rw [Finset.card_product,Finset.card_univ,Fintype.card_fin]
  simpa only [Nat.mul_comm 2] using Nat.mul_le_mul_right 2 (width j hj)

#print axioms bounded_local_gates
end Simlowker.Transversal1735
