import GuardedInputs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1506 Simlowker.Types1735 Simlowker.Transversal1735
namespace Simlowker.Guarded1735
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

def allLarge (R : Finset Nat) := ∀ p ∈ R, 16 ≤ (orIn n C p).card
def largeOption (w : Nat) (u v : Fin n) := ∃ R : Finset Nat, R.card ≤ 2 ∧ allLarge (n:=n) C R ∧
  hitsAll C R (pairInput u v) ∧ ∀ y, hitsAll C R y → W n C y w = true
def tagOption (w : Nat) (u v : Fin n) := ∃ x B, (x=u ∨ x=v) ∧ tag G C w x B ∧
  (B=none ∨ ∃ p, B=some (orIn n C p) ∧ 16 ≤ (orIn n C p).card ∧ hitsWire C p (pairInput u v))

theorem edge_eq {x z u v : Fin n} (hx : x=u ∨ x=v) (hz : z=u ∨ z=v) (diff : x≠z) :
    s(x,z)=s(u,v) := by
  rcases hx with h|h <;> rcases hz with k|k
  · exact False.elim (diff (h.trans k.symm))
  · rw [h,k]
  · rw [h,k,Sym2.eq_swap]
  · exact False.elim (diff (h.trans k.symm))

theorem axes_wires (k : Nat) : ∃ a b : Fin 2, (axes (n:=n) C k).1 = orIn n C (opnd C k a) ∧
    (axes (n:=n) C k).2 = orIn n C (opnd C k b) := by
  by_cases choose : (side (n:=n) C k 0).card < 16
  · exact ⟨0,1,by simp only [axes,ite_eq_left choose]; rfl,by simp only [axes,ite_eq_left choose]; rfl⟩
  · exact ⟨1,0,by simp only [axes,ite_eq_right choose]; rfl,by simp only [axes,ite_eq_right choose]; rfl⟩

theorem axes_little {k : Nat} (len : k<C.gates.length) {x y : Fin n}
    (_sm : (axes (n:=n) C k).1.card <16) (sm' : (axes (n:=n) C k).2.card <16)
    (xm : x ∈ (axes C k).1) (ym : y ∈ (axes C k).2) : s(x,y) ∈ littleCross C (side (n:=n) C) := by
  by_cases choose : (side (n:=n) C k 0).card <16
  · simp only [axes,choose,ite_true] at sm' xm ym
    exact little_in C _ len choose sm' xm ym
  · have impossible : (side (n:=n) C k 0).card < 16 := by simpa only [axes, ite_eq_right choose] using sm'
    exact False.elim (choose impossible)

theorem flat_axes_true (ao : IsAO2 n C) (top : TopForm G C)
    (flat : ∀ i ∈ junk G C, ∀ j ∈ junk G C, ¬InCone n C i j)
    {k : Nat} (hk : k ∈ junk G C) {y : Fin n → Bool} (on : gateVal n C k y = true) :
    lit (axes (n:=n) C k).1 y ∧ lit (axes C k).2 y := by
  have inf := Finset.mem_filter.mp hk
  have lt := Finset.mem_range.mp inf.1
  have op := inf.2.1
  have both := (and_on C ao lt op y).mp on
  have leaf (b : Fin 2) (h : W n C y (opnd C k b) = true) : lit (side C k b) y := by
    rcases (through_operand G C ao top lt op b y).mp h with yes|⟨i,sm,hi,path,_⟩
    · exact yes
    · exact False.elim (flat i hi k hk (feeds_cone G C ao lt ⟨sm,hi,b,path⟩))
  by_cases select : (side (n:=n) C k 0).card <16
  · simpa only [axes,select,ite_true] using And.intro (leaf 0 both.1) (leaf 1 both.2)
  · simpa only [axes,select,ite_false] using And.intro (leaf 1 both.2) (leaf 0 both.1)

/-- The input satisfies an operand using only OR wires and at most one dirty AND per path. -/
def shallowPort (w : Nat) (y : Fin n → Bool) : Prop :=
  hitsWire C w y ∨ ∃ k ∈ junk G C, OrR n C w (n+k) ∧ lit (axes C k).1 y ∧ lit (axes C k).2 y

theorem flat_port (ao : IsAO2 n C) (top : TopForm G C)
    (flat : ∀ i ∈ junk G C, ∀ j ∈ junk G C, ¬InCone n C i j)
    {j : Nat} (hj : j ∈ tops G C) (b : Fin 2) (y : Fin n → Bool)
    (on : W n C y (opnd C j b) = true) : shallowPort G C (opnd C j b) y := by
  have info := hj
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at info
  rcases (through_operand G C ao top info.1 info.2.1 b y).mp on with literal|⟨k,_,hk,path,active⟩
  · exact Or.inl literal
  · exact Or.inr ⟨k,hk,path,flat_axes_true G C ao top flat hk active⟩

theorem classify (ao : IsAO2 n C) (top : TopForm G C) {j : Nat} (b : Fin 2) (u v : Fin n)
    (litSmall : s(u,v) ∉ littleCross C (side (n:=n) C)) (noFront : s(u,v) ∉ frontEdges G C 8)
    (on : shallowPort G C (opnd C j b) (pairInput u v)) :
    tagOption G C (opnd C j b) u v ∨ largeOption C (opnd C j b) u v := by
  classical
  rcases on with literal|⟨k,hk,path,la,lb⟩
  · obtain ⟨x,seen,one⟩ := literal
    exact Or.inl ⟨x,none,of_decide_eq_true one,
      ⟨x,(orIn_iff n C (ao_of n C ao) _ _).mp seen,Or.inl ⟨rfl,rfl⟩⟩,Or.inl rfl⟩
  let A := (axes (n:=n) C k).1
  let B := (axes (n:=n) C k).2
  obtain ⟨i,l,ae,be⟩ := axes_wires (n:=n) C k
  change A = _ at ae
  change B = _ at be
  by_cases small : A.card <16
  · left
    obtain ⟨x,xa,xuv⟩ := la
    have ex : x=u ∨ x=v := of_decide_eq_true xuv
    by_cases xb : x ∈ B
    · exact ⟨x,none,ex,⟨n+k,path,Or.inr ⟨k,hk,rfl,small,xa,Or.inl ⟨rfl,xb⟩⟩⟩,Or.inl rfl⟩
    obtain ⟨z,zb,zuv⟩ := lb
    have ez : z=u ∨ z=v := of_decide_eq_true zuv
    have eq := edge_eq ex ez (fun e => xb (e ▸ zb))
    have kb := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    have big : 16 ≤ B.card := by
      by_contra! other
      exact litSmall (eq ▸ axes_little C kb small other xa zb)
    have many : 4 ≤ (B.filter (fun t => ¬G.Adj x t)).card := by
      by_contra! few
      have far : ((orIn n C (opnd C k l)).filter (fun t => ¬G.Adj x t)).card < 8 := by rw [←be]; omega
      have w := wire_frontier G C ao (by decide : 0<8) x z (opnd C k l) (by rw [←be]; exact big) far (be ▸ zb)
      exact noFront (eq ▸ front_in G C w)
    have ok : valid G x (some B) := by
      intro F hf
      have e : F = B := by simpa using hf
      exact e ▸ many
    exact ⟨x,some B,ex,⟨n+k,path,Or.inr ⟨k,hk,rfl,small,xa,Or.inr ⟨rfl,big,ok⟩⟩⟩,
      Or.inr ⟨opnd C k l,congrArg some be,be ▸ big,⟨z,be ▸ zb,zuv⟩⟩⟩
  · right
    have otherBig : 16 ≤ B.card := by
      by_cases sel : (side (n:=n) C k 0).card <16
      · exact False.elim (small (by simp [A,axes,sel]))
      · simpa [B,axes,sel] using Nat.le_of_not_gt sel
    let R : Finset Nat := {opnd C k i,opnd C k l}
    refine ⟨R,Finset.card_le_two,?_,?_,?_⟩
    · intro q hq
      rcases Finset.mem_insert.mp hq with e|e
      · rw [e,←ae]; exact Nat.le_of_not_gt small
      · rw [Finset.mem_singleton.mp e,←be]; exact otherBig
    · intro q hq
      rcases Finset.mem_insert.mp hq with e|e
      · rw [e]; change lit (orIn n C _) _; rwa [←ae]
      · rw [Finset.mem_singleton.mp e]; change lit (orIn n C _) _; rwa [←be]
    · intro y all
      have ay := all (opnd C k i) (by simp [R])
      have by' := all (opnd C k l) (by simp [R])
      apply orR_mono n C (ao_of n C ao) y _ _ path
      exact axes_on G C ao top hk y (by change lit B y; rw [be]; exact by') (by change lit A y; rw [ae]; exact ay)

#print axioms classify
end Simlowker.Guarded1735

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1506 Simlowker.Types1735 Simlowker.Transversal1735
namespace Simlowker.Guarded1735
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

private theorem raw_name (ao : IsAO2 n C) (w : Fin n) : orIn n C w.val = {w} := by
  ext x
  rw [orIn_iff n C (ao_of n C ao),Finset.mem_singleton]
  constructor
  · intro p
    rcases Relation.ReflTransGen.cases_head p with eq | ⟨z,⟨k,bad,_,_,_⟩,_⟩
    · exact Fin.ext eq.symm
    · have := w.isLt
      omega
  · rintro rfl
    exact .refl

private theorem marked (ao : IsAO2 n C) (top : TopForm G C) {w : Nat} {u v : Fin n}
    (tagged : tagOption G C w u v) :
    ∃ x R, (x=u ∨ x=v) ∧ R.card ≤ 1 ∧ allLarge (n:=n) C R ∧ hitsAll C R (pairInput u v) ∧
      ∀ y, y x = true → hitsAll C R y → W n C y w = true := by
  obtain ⟨x,B,ex,t,guard⟩ := tagged
  rcases guard with rfl|⟨p,rfl,big,active⟩
  · refine ⟨x,∅,ex,by simp,by simp [allLarge],by simp [hitsAll],?_⟩
    intro y yes _
    exact tag_on G C ao top t y ⟨yes,by simp⟩
  · refine ⟨x,{p},ex,by simp,by simpa [allLarge] using big,by simpa [hitsAll] using active,?_⟩
    intro y yes all
    apply tag_on G C ao top t y
    refine ⟨yes,?_⟩
    intro F hf
    have eq : F=orIn n C p := by simpa using hf
    exact eq.symm ▸ all p (by simp)

private theorem one_front (four : NoFourCycle G) (ao : IsAO2 n C) (R : Finset Nat) {u v : Fin n}
    (size : R.card ≤ 4) (active : hitsAll C R (pairInput u v))
    (safe : ∀ y, hitsAll C R y → graphFun G ∅ y = true)
    (wide : ∀ p ∈ R, u ∉ orIn n C p → 16 ≤ (orIn n C p).card) : s(u,v) ∈ frontEdges G C 8 := by
  obtain ⟨q,hq,near⟩ := trace_near G C four R active safe
  obtain ⟨qr,vq,uq⟩ := Finset.mem_filter.mp hq
  have count : (missing C R u v).card ≤ 4 := (Finset.card_le_card (Finset.filter_subset _ _)).trans size
  have pow : 2 ^ ((missing C R u v).card-1) ≤ 2^3 := Nat.pow_le_pow_right (by decide) (by omega)
  exact front_in G C (wire_frontier G C ao (by decide : 0<8) u v q (wide q qr uq) (near.trans_le pow) vq)

private theorem front_at (four : NoFourCycle G) (ao : IsAO2 n C) (R : Finset Nat) {u v x : Fin n}
    (endp : x=u ∨ x=v) (size : R.card ≤ 4) (active : hitsAll C R (pairInput u v))
    (safe : ∀ y, hitsAll C R y → graphFun G ∅ y = true)
    (wide : ∀ p ∈ R, x ∉ orIn n C p → 16 ≤ (orIn n C p).card) : s(u,v) ∈ frontEdges G C 8 := by
  rcases endp with rfl|rfl
  · exact one_front G C four ao R size active safe wide
  · have sw : pairInput u x = pairInput x u := by funext z; simp [pairInput,or_comm]
    rw [Sym2.eq_swap]
    exact one_front G C four ao R size (sw ▸ active) safe wide

private theorem mixed (four : NoFourCycle G) (ao : IsAO2 n C) (top : TopForm G C) {p q : Nat}
    (clean : ∀ z, W n C z p = true → W n C z q = true → graphFun G ∅ z = true) {u v : Fin n}
    (a : tagOption G C p u v) (b : largeOption C q u v) : s(u,v) ∈ frontEdges G C 8 := by
  obtain ⟨x,S,ex,sc,sl,sa,ss⟩ := marked G C ao top a
  obtain ⟨T,tc,tl,ta,ts⟩ := b
  let R := insert x.val (S ∪ T)
  have uni := Finset.card_union_le S T
  have sz := Finset.card_insert_le x.val (S ∪ T)
  have xy : pairInput u v x = true := decide_eq_true ex
  have raw (y : Fin n → Bool) : hitsWire C x.val y ↔ y x=true := by simp [hitsWire,raw_name C ao]
  apply front_at G C four ao R ex (by dsimp [R]; omega)
  · intro r hr
    rcases Finset.mem_insert.mp hr with rfl|h
    · exact (raw _).mpr xy
    · exact (Finset.mem_union.mp h).elim (sa r) (ta r)
  · intro y all
    apply clean y (ss y ((raw _).mp (all x.val (by simp [R]))) (fun r hr => all r (by simp [R,hr])))
      (ts y (fun r hr => all r (by simp [R,hr])))
  · intro r hr missed
    rcases Finset.mem_insert.mp hr with rfl|h
    · exact False.elim (missed (by simp [raw_name C ao]))
    · exact (Finset.mem_union.mp h).elim (sl r) (tl r)

private theorem broad (four : NoFourCycle G) (ao : IsAO2 n C) {p q : Nat}
    (clean : ∀ z, W n C z p = true → W n C z q = true → graphFun G ∅ z = true) {u v : Fin n}
    (a : largeOption C p u v) (b : largeOption C q u v) : s(u,v) ∈ frontEdges G C 8 := by
  obtain ⟨S,sc,sl,sa,ss⟩ := a
  obtain ⟨T,tc,tl,ta,ts⟩ := b
  have uni := Finset.card_union_le S T
  apply one_front G C four ao (S∪T) (by omega)
  · intro r h
    exact (Finset.mem_union.mp h).elim (sa r) (ta r)
  · intro y all
    exact clean y (ss y (fun r hr => all r (Finset.mem_union_left T hr)))
      (ts y (fun r hr => all r (Finset.mem_union_right S hr)))
  · intro r h _
    exact (Finset.mem_union.mp h).elim (sl r) (tl r)

private theorem both_tags (four : NoFourCycle G) (ao : IsAO2 n C) (top : TopForm G C) {j : Nat}
    (hj : j < C.gates.length)
    (clean : ∀ z, W n C z (opnd C j 0) = true → W n C z (opnd C j 1) = true → graphFun G ∅ z = true) {u v : Fin n}
    (a : tagOption G C (opnd C j 0) u v) (b : tagOption G C (opnd C j 1) u v) :
    s(u,v) ∈ charges G C ∪ littleCross C (fun k i => names G C (opnd C k i)) := by
  obtain ⟨x,P,ex,tx,_⟩ := a
  obtain ⟨y,Q,ey,ty,_⟩ := b
  have diff : x ≠ y := by
    rintro rfl
    rcases pair_rule G C four ao top clean tx ty with bad|bad|bad
    · exact G.irrefl bad
    · exact own_exception G (tag_valid G C tx) bad
    · exact own_exception G (tag_valid G C ty) bad
  rw [←edge_eq ex ey diff]
  have nx := (name_iff G C).mpr ⟨P,tx⟩
  have ny := (name_iff G C).mpr ⟨Q,ty⟩
  by_cases bq : 16 ≤ (names G C (opnd C j 1)).card
  · exact Finset.mem_union_left _ (charge_large G C ao x y _ (tag_comp G C four ao top clean tx) bq ny)
  by_cases bp : 16 ≤ (names G C (opnd C j 0)).card
  · rw [Sym2.eq_swap]
    exact Finset.mem_union_left _ (charge_large G C ao y x _ (tag_comp G C four ao top (fun z a b => clean z b a) ty) bp nx)
  · exact Finset.mem_union_right _ (little_in C (fun k i => names G C (opnd C k i)) hj (by omega) (by omega) nx ny)

/-- Counts any family of pairs with a shallow accepting witness. Other paths can have arbitrary AND depth. -/
theorem shallow_pairs_bound (four : NoFourCycle G) (ao : IsAO2 n C) (top : TopForm G C)
    (E : Finset (Sym2 (Fin n)))
    (witness : ∀ u v, s(u,v) ∈ E → ∃ j ∈ tops G C, ∀ b : Fin 2, shallowPort G C (opnd C j b) (pairInput u v)) :
    E.card ≤ 542*C.size := by
  classical
  let L := littleCross C (side (n:=n) C)
  let N := littleCross C (fun k i => names G C (opnd C k i))
  let F := frontEdges G C 8
  let H := charges G C
  have cover : E ⊆ (F ∪ L) ∪ (H ∪ N) := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      obtain ⟨j,hj,on⟩ := witness u v he
      have info := hj
      simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at info
      have clean (z) (a : W n C z (opnd C j 0)=true) (b : W n C z (opnd C j 1)=true) :=
        info.2.2 z ((and_on C ao info.1 info.2.1 z).mpr ⟨a,b⟩)
      by_cases hf : s(u,v) ∈ F
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hf)
      by_cases hl : s(u,v) ∈ L
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hl)
      rcases classify G C ao top 0 u v hl hf (on 0) with a|a <;>
        rcases classify G C ao top 1 u v hl hf (on 1) with b|b
      · exact Finset.mem_union_right _ (both_tags G C four ao top info.1 clean a b)
      · exact False.elim (hf (mixed G C four ao top clean a b))
      · exact False.elim (hf (mixed G C four ao top (fun z l r => clean z r l) b a))
      · exact False.elim (hf (broad G C four ao clean a b))
  have cov := Finset.card_le_card cover
  have c1 := Finset.card_union_le (F∪L) (H∪N)
  have c2 := Finset.card_union_le F L
  have c3 := Finset.card_union_le H N
  have f : F.card ≤ 32*C.size := front_count G C four 8
  have l : L.card ≤ 225*C.size := little_count C _
  have h : H.card ≤ 60*C.size := charges_count G C four
  have a : N.card ≤ 225*C.size := little_count C _
  omega

/-- Both intermediate ANDs fire on the pair. The upper one has an operand
    whose literal inputs all miss the pair, so an earlier AND must supply it. -/
def nestedWitness (y : Fin n → Bool) : Prop :=
  ∃ j ∈ tops G C, gateVal n C j y = true ∧ ∃ b : Fin 2, ∃ k ∈ junk G C, OrR n C (opnd C j b) (n+k) ∧
    gateVal n C k y = true ∧ ∃ c : Fin 2, ¬hitsWire C (opnd C k c) y ∧
      ∃ i < k, i ∈ junk G C ∧ OrR n C (opnd C k c) (n+i) ∧ gateVal n C i y = true

private theorem trace_deep (ao : IsAO2 n C) (top : TopForm G C) {j : Nat} (hj : j ∈ tops G C)
    (b : Fin 2) (y : Fin n → Bool) (accepts : gateVal n C j y = true) (on : W n C y (opnd C j b) = true)
    (deep : ¬shallowPort G C (opnd C j b) y) : nestedWitness G C y := by
  have info := hj
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at info
  rcases (through_operand G C ao top info.1 info.2.1 b y).mp on with litJ|⟨k,_,hk,path,active⟩
  · exact False.elim (deep (.inl litJ))
  have ki := Finset.mem_filter.mp hk
  have kl := Finset.mem_range.mp ki.1
  obtain ⟨left,right⟩ := (and_on C ao kl ki.2.1 y).mp active
  have missingSide : ∃ c : Fin 2, ¬hitsWire C (opnd C k c) y := by
    by_contra! all
    apply deep
    obtain ⟨c,d,ac,ad⟩ := axes_wires (n:=n) C k
    refine Or.inr ⟨k,hk,path,?_,?_⟩
    · rw [ac]; exact all c
    · rw [ad]; exact all d
  obtain ⟨c,miss⟩ := missingSide
  have val : W n C y (opnd C k c) = true := by fin_cases c <;> assumption
  rcases (through_operand G C ao top kl ki.2.1 c y).mp val with seen|earlier
  · exact False.elim (miss seen)
  · exact ⟨j,hj,accepts,b,k,hk,path,active,c,miss,earlier⟩

/-- In an unrestricted circuit, only pairs with a live chain of dirty gates
    can contribute beyond the explicit linear allowance. -/
theorem nested_remainder (four : NoFourCycle G) (least : IsLeastAO G C) (top : TopForm G C)
    (D : Finset (Sym2 (Fin n)))
    (capture : ∀ u v, G.Adj u v → nestedWitness G C (pairInput u v) → s(u,v) ∈ D) :
    G.edgeFinset.card ≤ 542*C.size + D.card := by
  classical
  have small : (G.edgeFinset \ D).card ≤ 542*C.size := by
    apply shallow_pairs_bound G C four least.1 top
    intro u v he
    obtain ⟨edge,miss⟩ := Finset.mem_sdiff.mp he
    have adj := G.mem_edgeFinset.mp edge
    obtain ⟨j,hj,on⟩ := edge_top G C least adj
    have info := hj
    simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at info
    obtain ⟨left,right⟩ := (and_on C least.1 info.1 info.2.1 _).mp on
    refine ⟨j,hj,?_⟩
    intro b
    by_contra deep
    apply miss (capture u v adj (trace_deep G C least.1 top hj b _ on ?_ deep))
    fin_cases b <;> assumption
  have sub : G.edgeFinset ⊆ (G.edgeFinset \ D) ∪ D := by
    intro e he
    by_cases hd : e ∈ D
    · exact Finset.mem_union_right _ hd
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he,hd⟩)
  exact (Finset.card_le_card sub).trans ((Finset.card_union_le ..).trans (Nat.add_le_add_right small _))

theorem flat_edge_bound (four : NoFourCycle G) (least : IsLeastAO G C) (top : TopForm G C)
    (flat : ∀ i ∈ junk G C, ∀ j ∈ junk G C, ¬InCone n C i j) : G.edgeFinset.card ≤ 542*C.size := by
  apply shallow_pairs_bound G C four least.1 top
  intro u v he
  obtain ⟨j,hj,on⟩ := edge_top G C least (G.mem_edgeFinset.mp he)
  have info := hj
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at info
  have both := (and_on C least.1 info.1 info.2.1 _).mp on
  refine ⟨j,hj,?_⟩
  intro b
  apply flat_port G C least.1 top flat hj b _
  fin_cases b
  · exact both.1
  · exact both.2

theorem flat_step : ∃ k2 : Nat, ∀ (m : Nat) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj],
    (∀ (v : Fin m) (p : H.Walk v v), p.IsCycle → 5 ≤ p.length) → H.edgeFinset.Nonempty →
    ∀ D : Circuit, IsLeastAO H D → TopForm H D → 2 ≤ (junk H D).card →
    (∀ i ∈ junk H D, ∀ j ∈ junk H D, ¬InCone m D i j) → (Ustar H D).card ≤ k2 * (D.size+1) := by
  refine ⟨542,?_⟩
  intro m H _ girth _ D least top _ flat
  have b := flat_edge_bound H D (girth_four H girth) least top flat
  have ss : Ustar H D ⊆ H.edgeFinset := Finset.sdiff_subset
  have := Finset.card_le_card ss
  omega

#print axioms nested_remainder
#print axioms shallow_pairs_bound
#print axioms flat_edge_bound
#print axioms flat_step
end Simlowker.Guarded1735
