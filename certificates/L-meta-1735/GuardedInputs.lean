import FlatCircuits

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open Simlowker.Transversal1735
namespace Simlowker.Guarded1735
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
abbrev Guard (n : Nat) := Option (Finset (Fin n))

def ready (x : Fin n) (B : Guard n) (y : Fin n → Bool) :=
  y x = true ∧ ∀ F ∈ B.toFinset, ∃ z ∈ F, y z = true

def valid (x : Fin n) (B : Guard n) :=
  ∀ F ∈ B.toFinset, 4 ≤ (F.filter fun z => ¬ G.Adj x z).card

def exceptions (x : Fin n) (B : Guard n) : Finset (Fin n) := match B with
  | none => ∅
  | some F => Finset.univ.filter fun y => ((F.filter fun t => ¬G.Adj x t).filter fun t => ¬G.Adj y t).card < 2

theorem exceptions_card (four : NoFourCycle G) {x : Fin n} {B : Guard n} (validB : valid G x B) :
    (exceptions G x B).card ≤ 1 := by
  cases B with
  | none => simp [exceptions]
  | some F => exact at_most_one_center G four Finset.univ _ 2 (validB F (by simp))

theorem own_exception {x : Fin n} {B : Guard n} (ok : valid G x B) : x ∉ exceptions G x B := by
  cases B with
  | none => simp [exceptions]
  | some F =>
    have large := ok F (by simp)
    intro bad
    have h := (Finset.mem_filter.mp bad).2
    have eq : ((F.filter fun z => ¬G.Adj x z).filter fun z => ¬G.Adj x z) = F.filter (fun z => ¬G.Adj x z) := by ext w; simp
    rw [eq] at h
    omega

theorem not_joint (four : NoFourCycle G) (x y : Fin n) (P Q : Guard n)
    (off : ¬G.Adj x y) (allowX : y ∉ exceptions G x P) (allowY : x ∉ exceptions G y Q) :
    ∃ z, graphFun G ∅ z = false ∧ ready x P z ∧ ready y Q z := by
  classical
  let R := P.toFinset ∪ Q.toFinset
  let S := Finset.univ.filter fun w => ¬G.Adj x w ∧ ¬G.Adj y w
  have nonadj {a b : Fin n} {B : Guard n} (allowed : b ∉ exceptions G a B) {F : Finset (Fin n)} (h : F ∈ B.toFinset) :
      2 ≤ ((F.filter fun z => ¬G.Adj a z).filter fun z => ¬G.Adj b z).card := by
    cases B with
    | none => simp at h
    | some T =>
      have eq : F=T := by simpa using h
      subst T
      by_contra! fail
      exact allowed (Finset.mem_filter.mpr ⟨Finset.mem_univ _,fail⟩)
  have bound (F : Finset (Fin n)) (h : F ∈ R) : 2 ≤ (F ∩ S).card := by
    rcases Finset.mem_union.mp h with l|r
    · have eq : (F.filter (fun z => ¬G.Adj x z)).filter (fun z => ¬G.Adj y z) = F ∩ S := by
        ext z; simp [S,and_assoc]
      rw [←eq]; exact nonadj allowX l
    · have eq : (F.filter (fun z => ¬G.Adj y z)).filter (fun z => ¬G.Adj x z) = F ∩ S := by
        ext z; simp [S,and_comm,and_left_comm]
      rw [←eq]; exact nonadj allowY r
  have small (B : Guard n) : B.toFinset.card ≤ 1 := by cases B <;> simp
  have boundR : R.card ≤ 2 := (Finset.card_union_le _ _).trans (by have := small P; have := small Q; omega)
  let e : Fin R.card ≃ {F // F ∈ R} := (Fintype.equivFinOfCardEq (Fintype.card_coe R)).symm
  obtain ⟨I,sub,ind,hit⟩ := sharp_transversal G four R.card (fun i => (e i).val) S (by
    intro i
    exact (Nat.pow_le_pow_right (by decide : 0<2) (show R.card-1 ≤ 1 by omega)).trans (bound _ (e i).property))
  let T := insert x (insert y I)
  let z := fun w : Fin n => decide (w ∈ T)
  have get (F : Finset (Fin n)) (h : F ∈ R) : ∃ w ∈ F, z w = true := by
    let t : {F // F ∈ R} := ⟨F,h⟩
    obtain ⟨w,wi,wf⟩ := hit (e.symm t)
    rw [e.apply_symm_apply] at wf
    exact ⟨w,wf,decide_eq_true (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem wi))⟩
  refine ⟨z,?_,⟨by simp [z,T],fun F h => get F (Finset.mem_union_left _ h)⟩,
    ⟨by simp [z,T],fun F h => get F (Finset.mem_union_right _ h)⟩⟩
  by_contra! no
  have yes : graphFun G ∅ z = true := by simpa using no
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq,z,T,
    Finset.mem_insert] at yes
  obtain ⟨a,b,ab,ha,hb⟩ := yes
  have away (w) (hw : w ∈ I) := (Finset.mem_filter.mp (sub hw)).2
  rcases ha with ax|ay|ai <;> rcases hb with bx|by'|bi
  · exact ab.ne (ax.trans bx.symm)
  · exact off (ax ▸ by' ▸ ab)
  · exact (away b bi).1 (ax ▸ ab)
  · exact off (ay ▸ bx ▸ ab.symm)
  · exact ab.ne (ay.trans by'.symm)
  · exact (away b bi).2 (ay ▸ ab)
  · exact (away a ai).1 (bx ▸ ab.symm)
  · exact (away a ai).2 (by' ▸ ab.symm)
  · exact ind a ai b bi ab

/-- The exceptions on each side of a graph-compatible collection are singletons. -/
def fits (P : Finset (Fin n)) (exc : Fin n → Finset (Fin n)) (x : Fin n) :=
  ∃ E : Finset (Fin n), E.card ≤ 1 ∧ ∀ y ∈ P, G.Adj x y ∨ y ∈ E ∨ x ∈ exc y

theorem few_centers (four : NoFourCycle G) (P : Finset (Fin n)) (exc : Fin n → Finset (Fin n))
    (sparse : ∀ y ∈ P, (exc y).card ≤ 1) (big : 7 ≤ P.card) (X : Finset (Fin n))
    (all : ∀ x ∈ X, fits G P exc x) : X.card ≤ 2 := by
  classical
  by_contra! wide
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0<X.card by omega)
  have erased := Finset.card_erase_of_mem ha
  obtain ⟨b,hb,c,hc,bc⟩ := Finset.one_lt_card.mp (show 1<(X.erase a).card by omega)
  obtain ⟨ba,bx⟩ := Finset.mem_erase.mp hb
  obtain ⟨ca,cx⟩ := Finset.mem_erase.mp hc
  obtain ⟨A,ac,ar⟩ := all a ha
  obtain ⟨B,bd,br⟩ := all b bx
  obtain ⟨C,cd,cr⟩ := all c cx
  let M := fun (u v : Fin n) => Finset.univ.filter fun y => G.Adj u y ∧ G.Adj v y
  let T := ((A ∪ B) ∪ C) ∪ ((M a b ∪ M a c) ∪ M b c)
  have sub : P ⊆ T := by
    intro y hy
    have h1 := ar y hy
    have h2 := br y hy
    have h3 := cr y hy
    have one {i j : Fin n} (hi : i ∈ exc y) (hj : j ∈ exc y) : i=j := Finset.card_le_one_iff.mp (sparse y hy) hi hj
    have nab : ¬(a ∈ exc y ∧ b ∈ exc y) := fun h => ba (one h.2 h.1)
    have nac : ¬(a ∈ exc y ∧ c ∈ exc y) := fun h => ca (one h.2 h.1)
    have nbc : ¬(b ∈ exc y ∧ c ∈ exc y) := fun h => bc (one h.1 h.2)
    simp only [T,M,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
    clear * - h1 h2 h3 nab nac nbc
    tauto
  have h := Finset.card_le_card sub
  have u1 := Finset.card_union_le A B
  have u2 := Finset.card_union_le (A ∪ B) C
  have u3 := Finset.card_union_le (M a b) (M a c)
  have u4 := Finset.card_union_le (M a b ∪ M a c) (M b c)
  have u5 := Finset.card_union_le ((A ∪ B) ∪ C) ((M a b ∪ M a c) ∪ M b c)
  have m1 : (M a b).card ≤ 1 := four _ _ ba.symm
  have m2 : (M a c).card ≤ 1 := four _ _ ca.symm
  have m3 : (M b c).card ≤ 1 := four _ _ bc
  dsimp only [T] at h
  omega

#print axioms not_joint
#print axioms few_centers
end Simlowker.Guarded1735

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1506 Simlowker.Types1735 Simlowker.Transversal1735
namespace Simlowker.Guarded1735
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

def axes (k : Nat) : Finset (Fin n) × Finset (Fin n) :=
  if (side (n:=n) C k 0).card < 16 then (side C k 0,side C k 1) else (side C k 1,side C k 0)
def lit (S : Finset (Fin n)) (y : Fin n → Bool) := ∃ w ∈ S, y w = true

theorem axes_on {k : Nat} (ao : IsAO2 n C) (top : TopForm G C) (hk : k ∈ junk G C) (y : Fin n → Bool)
    (maj : lit (axes (n:=n) C k).2 y) (minor : lit (axes (n:=n) C k).1 y) : gateVal n C k y = true := by
  have info := Finset.mem_filter.mp hk
  have lt := Finset.mem_range.mp info.1
  have op := info.2.1
  have fromBase (i : Fin 2) (h : lit (side C k i) y) : W n C y (opnd C k i) = true :=
    (through_operand G C ao top lt op i y).mpr (Or.inl h)
  apply (and_on C ao lt op y).mpr
  by_cases sel : (side (n:=n) C k 0).card < 16
  · simp only [axes,sel,ite_true] at maj minor
    exact ⟨fromBase 0 minor,fromBase 1 maj⟩
  · simp only [axes,sel,ite_false] at maj minor
    exact ⟨fromBase 0 maj,fromBase 1 minor⟩

/-- Labels available at an input or a dirty AND with a small side. -/
def seed (w : Nat) (x : Fin n) (B : Guard n) :=
  (w=x.val ∧ B=none) ∨ ∃ k ∈ junk G C, w=n+k ∧
    (axes (n:=n) C k).1.card < 16 ∧ x ∈ (axes C k).1 ∧
    ((B=none ∧ x ∈ (axes C k).2) ∨
     (B=some (axes C k).2 ∧ 16 ≤ (axes (n:=n) C k).2.card ∧ valid G x B))

def tag (w : Nat) (x : Fin n) (B : Guard n) := ∃ s, OrR n C w s ∧ seed G C s x B

noncomputable def names (q : Nat) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun x => ∃ B, tag G C q x B

theorem name_iff {q : Nat} {x : Fin n} : x ∈ names G C q ↔ ∃ B, tag G C q x B := by
  classical
  simp [names]

theorem tag_valid {w : Nat} {x : Fin n} {B : Guard n} (t : tag G C w x B) : valid G x B := by
  obtain ⟨_,_,raw|⟨_,_,_,_,_,h|h⟩⟩ := t
  · simp [raw.2,valid]
  · simp [h.1,valid]
  · exact h.2.2

theorem tag_up {q p : Nat} (path : OrR n C q p) {x : Fin n} {B : Guard n} (t : tag G C p x B) : tag G C q x B := by
  obtain ⟨s,r,h⟩ := t
  exact ⟨s,path.trans r,h⟩

theorem tag_on (ao : IsAO2 n C) (top : TopForm G C) {w : Nat} {x : Fin n} {B : Guard n}
    (t : tag G C w x B) (y : Fin n → Bool) (r : ready x B y) : W n C y w = true := by
  obtain ⟨s,path,sd⟩ := t
  apply orR_mono n C (ao_of n C ao) y w s path
  rcases sd with ⟨rfl,rfl⟩|⟨k,hk,rfl,_,minor,h|h⟩
  · exact (W_input n C y x x.isLt).trans r.1
  · exact axes_on G C ao top hk y ⟨x,h.2,r.1⟩ ⟨x,minor,r.1⟩
  · exact axes_on G C ao top hk y (r.2 _ (by simp [h.1])) ⟨x,minor,r.1⟩

theorem seed_small {s : Nat} {x : Fin n} {B : Guard n} (src : seed G C s x B) : (names G C s).card ≤ 15 := by
  classical
  have terminal (r : Nat) (h : OrR n C s r) : s=r := by
    rcases Relation.ReflTransGen.cases_head h with eq|⟨_,⟨i,wire,_,orOp,_⟩,_⟩
    · exact eq
    · rcases src with ⟨raw,_⟩|⟨k,hk,eq,_,_,_⟩
      · have := x.isLt
        omega
      · have ki : k=i := by omega
        subst i
        rw [(Finset.mem_filter.mp hk).2.1] at orOp
        contradiction
  have self (v) (h : v ∈ names G C s) : ∃ T, seed G C s v T := by
    obtain ⟨T,r,p,sd⟩ := (name_iff G C).mp h
    exact ⟨T,terminal r p ▸ sd⟩
  rcases src with ⟨eq,_⟩|⟨k,hk,eq,small,_,_⟩
  · have sub : names G C s ⊆ {x} := by
      intro v hv
      obtain ⟨_,⟨raw,_⟩|⟨k,_,gate,_⟩⟩ := self v hv
      · exact Finset.mem_singleton.mpr (Fin.ext (raw.symm.trans eq))
      · have := x.isLt
        omega
    exact (Finset.card_le_card sub).trans (by simp)
  · have sub : names G C s ⊆ (axes C k).1 := by
      intro v hv
      obtain ⟨_,⟨raw,_⟩|⟨i,_,gate,_,mem,_⟩⟩ := self v hv
      · have := v.isLt
        omega
      · have ki : k=i := by omega
        exact ki ▸ mem
    exact (Finset.card_le_card sub).trans (by omega)

def compatible (q : Nat) (x : Fin n) := ∃ E : Finset (Fin n), E.card ≤ 1 ∧
  ∀ y B, tag G C q y B → G.Adj x y ∨ y ∈ E ∨ x ∈ exceptions G y B

theorem compatible_down {q p : Nat} (path : OrR n C q p) {x : Fin n} (h : compatible G C q x) :
    compatible G C p x := by
  obtain ⟨E,size,all⟩ := h
  exact ⟨E,size,fun _ _ t => all _ _ (tag_up G C path t)⟩

theorem compatible_count (four : NoFourCycle G) (q : Nat) (big : 7 ≤ (names G C q).card) :
    (Finset.univ.filter fun x => by classical exact decide (compatible G C q x) = true).card ≤ 2 := by
  classical
  let P := names G C q
  let exc (y : Fin n) := if h : y ∈ P then exceptions G y (Classical.choose ((name_iff G C).mp h)) else ∅
  apply few_centers G four P exc ?_ big
  · intro x hx
    obtain ⟨E,sz,all⟩ := of_decide_eq_true (Finset.mem_filter.mp hx).2
    refine ⟨E,sz,?_⟩
    intro y hy
    have t := Classical.choose_spec ((name_iff G C).mp hy)
    simpa [exc,hy] using all _ _ t
  · intro y hy
    have t := Classical.choose_spec ((name_iff G C).mp hy)
    simpa [exc,hy] using exceptions_card G four (tag_valid G C t)

#print axioms seed_small
#print axioms compatible_count
end Simlowker.Guarded1735

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1506 Simlowker.Types1735 Simlowker.Transversal1735
namespace Simlowker.Guarded1735
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

theorem pair_rule (four : NoFourCycle G) (ao : IsAO2 n C) (top : TopForm G C) {p q : Nat}
    (clean : ∀ z, W n C z p = true → W n C z q = true → graphFun G ∅ z = true)
    {x y : Fin n} {P Q : Guard n} (tx : tag G C p x P) (ty : tag G C q y Q) :
    G.Adj x y ∨ y ∈ exceptions G x P ∨ x ∈ exceptions G y Q := by
  by_contra! no
  obtain ⟨z,falseAt,r,s⟩ := not_joint G four x y P Q no.1 no.2.1 no.2.2
  have yes := clean z (tag_on G C ao top tx z r) (tag_on G C ao top ty z s)
  rw [falseAt] at yes
  contradiction

theorem tag_comp (four : NoFourCycle G) (ao : IsAO2 n C) (top : TopForm G C) {p q : Nat}
    (clean : ∀ z, W n C z p = true → W n C z q = true → graphFun G ∅ z = true)
    {x : Fin n} {P : Guard n} (tx : tag G C p x P) : compatible G C q x :=
  ⟨exceptions G x P,exceptions_card G four (tag_valid G C tx),
   fun _ _ ty => pair_rule G C four ao top clean tx ty⟩

noncomputable def centers (q : Nat) : Finset (Fin n) := by
  classical
  exact if 16 ≤ (names G C q).card then Finset.univ.filter (compatible G C q) else ∅

noncomputable def smallNames (q : Nat) : Finset (Fin n) := by
  classical
  exact if (names G C q).card < 16 then names G C q else ∅

noncomputable def charges : Finset (Sym2 (Fin n)) :=
  ((Finset.range C.gates.length) ×ˢ (Finset.univ : Finset (Fin 2))).biUnion fun p =>
    (centers G C (n+p.1) ×ˢ smallNames G C (opnd C p.1 p.2)).image fun z => s(z.1,z.2)

theorem charges_count (four : NoFourCycle G) : (charges G C).card ≤ 60*C.size := by
  classical
  let R := (Finset.range C.gates.length) ×ˢ (Finset.univ : Finset (Fin 2))
  have cap (q : Nat) : (centers G C q).card ≤ 2 := by
    by_cases big : 16 ≤ (names G C q).card
    · simpa [centers,big] using compatible_count G C four q (by omega)
    · simp [centers,big]
  have sm (q : Nat) : (smallNames G C q).card ≤ 15 := by
    by_cases h : (names G C q).card < 16
    · simpa [smallNames,h] using (show (names G C q).card ≤ 15 by omega)
    · simp [smallNames,h]
  calc
    _ ≤ ∑ p ∈ R, ((centers G C (n+p.1) ×ˢ smallNames G C (opnd C p.1 p.2)).image (fun z => s(z.1,z.2))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ R, 30 := by
      apply Finset.sum_le_sum
      intro p _
      exact Finset.card_image_le.trans ((Finset.card_product _ _).le.trans (Nat.mul_le_mul (cap _) (sm _)))
    _ = _ := by simp [R,Circuit.size]; ring

theorem charge_large (ao : IsAO2 n C) (x y : Fin n) (w : Nat)
    (fits : compatible G C w x) (big : 16 ≤ (names G C w).card) (vy : y ∈ names G C w) :
    s(x,y) ∈ charges G C := by
  classical
  have A := ao_of n C ao
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    obtain ⟨B,s,path,sd⟩ := (name_iff G C).mp vy
    rcases Relation.ReflTransGen.cases_head path with eq|⟨z,step,rest⟩
    · subst s
      have sm := seed_small G C sd
      omega
    · have zy : y ∈ names G C z := (name_iff G C).mpr ⟨B,s,rest,sd⟩
      by_cases large : 16 ≤ (names G C z).card
      · exact ih z (orStep_lt n C A _ _ step) (compatible_down G C (.single step) fits) large zy
      · obtain ⟨h,rfl,lt,_,zin⟩ := step
        obtain ⟨a,d,ins,_,_⟩ := (A h lt).2
        rw [ins] at zin
        simp only [List.mem_cons,List.not_mem_nil,or_false] at zin
        have operand : ∃ b : Fin 2, opnd C h b = z := by
          rcases zin with rfl|rfl
          · exact ⟨0,by simp [opnd,ins,List.getD]⟩
          · exact ⟨1,by simp [opnd,ins,List.getD]⟩
        obtain ⟨b,eq⟩ := operand
        exact Finset.mem_biUnion.mpr ⟨(h,b),Finset.mem_product.mpr ⟨Finset.mem_range.mpr lt,Finset.mem_univ _⟩,
          Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr
          ⟨by simpa [centers,big] using fits,by simpa [smallNames,eq,Nat.lt_of_not_ge large] using zy⟩,rfl⟩⟩

noncomputable def littleCross (F : Nat → Fin 2 → Finset (Fin n)) : Finset (Sym2 (Fin n)) := by
  classical
  exact (Finset.range C.gates.length).biUnion fun j =>
    if (F j 0).card < 16 ∧ (F j 1).card < 16 then (F j 0 ×ˢ F j 1).image (fun z => s(z.1,z.2)) else ∅

theorem little_count (F : Nat → Fin 2 → Finset (Fin n)) : (littleCross C F).card ≤ 225*C.size := by
  classical
  unfold littleCross
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _j ∈ Finset.range C.gates.length, 225 := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs with h
      · apply Finset.card_image_le.trans
        rw [Finset.card_product]
        exact Nat.mul_le_mul (show (F j 0).card ≤ 15 by omega) (show (F j 1).card ≤ 15 by omega)
      · simp
    _ = _ := by simp [Circuit.size]; ring

theorem little_in (F : Nat → Fin 2 → Finset (Fin n)) {j : Nat} (hj : j < C.gates.length) {u v : Fin n}
    (h0 : (F j 0).card < 16) (h1 : (F j 1).card < 16) (a : u ∈ F j 0) (b : v ∈ F j 1) :
    s(u,v) ∈ littleCross C F := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨j,Finset.mem_range.mpr hj,?_⟩
  simp only [h0,h1,and_self,ite_true]
  exact Finset.mem_image.mpr ⟨(u,v),Finset.mem_product.mpr ⟨a,b⟩,rfl⟩

#print axioms charges_count
#print axioms charge_large
end Simlowker.Guarded1735
