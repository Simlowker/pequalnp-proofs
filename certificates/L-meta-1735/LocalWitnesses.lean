import TypeBounds

/-! ## Dirty predecessors of an accepting top -/

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1506
namespace Simlowker.Types1735
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

/-- A dirty gate reaches an operand of the given gate using only OR wires. -/
def feeds (k j : Nat) : Prop :=
  k < j ∧ k ∈ junk G C ∧ ∃ b : Fin 2, OrR n C (opnd C j b) (n+k)

/-- The dirty predecessors relevant to the chosen top. -/
abbrev ancestor := Relation.TransGen (feeds G C)

/-- A replacement for v, with x fixed, only needs the bits absent at x. -/
def substitute (j : Nat) (x v w : Fin n) : Prop :=
  ∀ k, ancestor G C k j → ∀ b : Fin 2, v ∈ side C k b → x ∈ side C k b ∨ w ∈ side C k b

theorem local_transfer (ao : IsAO2 n C) (top : TopForm G C) (root : Nat) (x y : Fin n → Bool)
    (hxy : ∀ k, ancestor G C k root → ∀ b : Fin 2, baseOn C k b x → baseOn C k b y) :
    ∀ k, ancestor G C k root → k ∈ junk G C → gateVal n C k x = true → gateVal n C k y = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro path dirty on
    have info := Finset.mem_filter.mp dirty
    have lt := Finset.mem_range.mp info.1
    have op := info.2.1
    have both := (and_on C ao lt op x).mp on
    have move (b : Fin 2) (h : W n C x (opnd C k b) = true) :
        W n C y (opnd C k b) = true := by
      apply (through_operand G C ao top lt op b y).mpr
      rcases (through_operand G C ao top lt op b x).mp h with literal|⟨i,ik,dirtyI,reaches,hi⟩
      · exact Or.inl (hxy k path b literal)
      · have next : feeds G C i k := ⟨ik,dirtyI,b,reaches⟩
        exact Or.inr ⟨i,ik,dirtyI,reaches,ih i ik (Relation.TransGen.head next path) dirtyI hi⟩
    exact (and_on C ao lt op y).mpr ⟨move 0 both.1,move 1 both.2⟩

theorem local_mark (ao : IsAO2 n C) (top : TopForm G C) {j : Nat} {b : Fin 2}
    {u v u' v' : Fin n} (cover : ∀ k, ancestor G C k j → ∀ a : Fin 2,
      (u ∈ side C k a ∨ v ∈ side C k a) → u' ∈ side C k a ∨ v' ∈ side C k a)
    (h : marked G C j b u v) : marked G C j b u' v' := by
  obtain ⟨k,lt,dirty,reaches,on⟩ := h
  refine ⟨k,lt,dirty,reaches,local_transfer G C ao top j _ _ ?_ k (.single ⟨lt,dirty,b,reaches⟩) dirty on⟩
  intro i path a h
  exact (base_pair C i a _ _).mpr (cover i path a ((base_pair C i a _ _).mp h))

private theorem choose_local {a b c d e f : Prop} (h : (a ∨ b) ∨ c) (i : (d ∨ e) ∨ f)
    (j : ¬(a ∧ e)) (k : ¬(b ∧ d)) : ((a ∨ c) ∧ (d ∨ f)) ∨ ((b ∨ c) ∧ (e ∨ f)) := by tauto

theorem local_edge (ao : IsAO2 n C) (top : TopForm G C) {j : Nat} (hj : j ∈ tops G C) {u v : Fin n}
    (outside : s(u,v) ∉ starEdges G C) (on : gateVal n C j (pairInput u v) = true) :
    (∀ w, substitute G C j u v w → G.Adj u w) ∨
    (∀ w, substitute G C j v u w → G.Adj w v) := by
  have info := hj
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at info
  obtain ⟨lt,op,clean⟩ := info
  have halves (b : Fin 2) (x y : Fin n) :
      W n C (pairInput x y) (opnd C j b) = true ↔
      (x ∈ side C j b ∨ y ∈ side C j b) ∨ marked G C j b x y := by
    rw [through_operand G C ao top lt op,base_pair]
    rfl
  have cross (x y : Fin n) (hx : x ∈ side C j 0) (hy : y ∈ side C j 1) :
      s(x,y) ∈ starEdges G C :=
    Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,rfl⟩⟩
  have neg1 : ¬ (u ∈ side C j 0 ∧ v ∈ side C j 1) := fun h => outside (cross _ _ h.1 h.2)
  have neg2 : ¬ (v ∈ side C j 0 ∧ u ∈ side C j 1) := by
    intro h
    exact outside (Sym2.eq_swap ▸ cross _ _ h.1 h.2)
  obtain ⟨h0,h1⟩ := (and_on C ao lt op _).mp on
  have choice := choose_local ((halves 0 u v).mp h0) ((halves 1 u v).mp h1) neg1 neg2
  have finish (x y : Fin n) (h : ∀ b : Fin 2, W n C (pairInput x y) (opnd C j b) = true) :
      G.Adj x y := (graphFun_pair G x y).mp (clean _ ((and_on C ao lt op _).mpr ⟨h 0,h 1⟩))
  rcases choice with h|h
  · left
    intro w sub
    apply finish
    intro b
    apply (halves _ _ _).mpr
    have val : u ∈ side C j b ∨ marked G C j b u v := by fin_cases b; exact h.1; exact h.2
    rcases val with literal|mark
    · exact Or.inl (Or.inl literal)
    · exact Or.inr (local_mark G C ao top (fun k p a active => active.elim Or.inl (sub k p a)) mark)
  · right
    intro w sub
    apply finish
    intro b
    apply (halves _ _ _).mpr
    have val : v ∈ side C j b ∨ marked G C j b u v := by fin_cases b; exact h.1; exact h.2
    rcases val with literal|mark
    · exact Or.inl (Or.inr literal)
    · exact Or.inr (local_mark G C ao top (fun k p a active =>
        active.elim (fun z => (sub k p a z).symm) Or.inr) mark)

#print axioms local_edge
end Simlowker.Types1735

/-! ## Substitution by an arbitrary independent assignment -/

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1506
namespace Simlowker.Types1735
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

theorem ancestor_dirty {i j : Nat} (p : ancestor G C i j) : i ∈ junk G C := by
  induction p with
  | single h => exact h.2.1
  | tail _ _ prev => exact prev

/-- An independent assignment containing the held endpoint must miss a dirty side
    containing the other endpoint. The dirty gate is in the accepting top's cone. -/
def separates (j : Nat) (u v : Fin n) := ∀ y : Fin n → Bool,
  graphFun G ∅ y = false → y u = true →
  ∃ k, ancestor G C k j ∧ ∃ b : Fin 2, v ∈ side C k b ∧ ¬baseOn C k b y

theorem separator (ao : IsAO2 n C) (top : TopForm G C) {j : Nat} (hj : j ∈ tops G C)
    {u v : Fin n} (outside : s(u,v) ∉ starEdges G C) (on : gateVal n C j (pairInput u v) = true) :
    separates G C j u v ∨ separates G C j v u := by
  classical
  have info := hj
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at info
  obtain ⟨lt,op,clean⟩ := info
  let M := fun b : Fin 2 => marked G C j b u v
  have halves (b : Fin 2) (h : W n C (pairInput u v) (opnd C j b) = true) :
      (u ∈ side C j b ∨ v ∈ side C j b) ∨ M b := by
    rwa [through_operand G C ao top lt op,base_pair] at h
  have cross (x y : Fin n) (hx : x ∈ side C j 0) (hy : y ∈ side C j 1) :
      s(x,y) ∈ starEdges G C :=
    Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,rfl⟩⟩
  have neg1 : ¬ (u ∈ side C j 0 ∧ v ∈ side C j 1) := fun h => outside (cross _ _ h.1 h.2)
  have neg2 : ¬ (v ∈ side C j 0 ∧ u ∈ side C j 1) := fun h => outside (Sym2.eq_swap ▸ cross _ _ h.1 h.2)
  obtain ⟨h0,h1⟩ := (and_on C ao lt op _).mp on
  have a0 := halves 0 h0
  have a1 := halves 1 h1
  have logic {a b c d e f : Prop} (h : (a ∨ b) ∨ c) (i : (d ∨ e) ∨ f)
      (z : ¬(a ∧ e)) (k : ¬(b ∧ d)) : ((a ∨ c) ∧ (d ∨ f)) ∨ ((b ∨ c) ∧ (e ∨ f)) := by
    clear * - h i z k
    tauto
  have choice := logic a0 a1 neg1 neg2
  have dir (x z : Fin n) (sym : (x=u ∧ z=v) ∨ (x=v ∧ z=u))
      (good : ∀ b : Fin 2, x ∈ side C j b ∨ M b) : separates G C j x z := by
    intro y independent xy
    by_contra! missing
    have profile (k : Nat) (anc : ancestor G C k j) (b : Fin 2) :
        baseOn C k b (pairInput u v) → baseOn C k b y := by
      intro h
      have h1 := (base_pair C k b u v).mp h
      have either : x ∈ side C k b ∨ z ∈ side C k b := by
        rcases sym with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact h1
        · exact h1.symm
      exact either.elim (fun h => ⟨x,h,xy⟩) (missing k anc b)
    have both (b : Fin 2) : W n C y (opnd C j b) = true := by
      apply (through_operand G C ao top lt op b y).mpr
      obtain literal|⟨k,sm,dirty,reach,mark⟩ := good b
      · exact Or.inl ⟨x,literal,xy⟩
      · exact Or.inr ⟨k,sm,dirty,reach,local_transfer G C ao top j _ y profile k
          (.single ⟨sm,dirty,b,reach⟩) dirty mark⟩
    have contradiction := clean y ((and_on C ao lt op y).mpr ⟨both 0,both 1⟩)
    rw [independent] at contradiction
    contradiction
  rcases choice with h|h
  · exact Or.inl (dir u v (Or.inl ⟨rfl,rfl⟩) (by intro b; fin_cases b; exact h.1; exact h.2))
  · exact Or.inr (dir v u (Or.inr ⟨rfl,rfl⟩) (by intro b; fin_cases b; exact h.1; exact h.2))

#print axioms separator
end Simlowker.Types1735

/-! ## Distinct dirty operands for an induced matching -/

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover
namespace Simlowker.Types1735
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

/-- The dirty operand slots available to a family of accepting tops constrain
    the size of any induced matching of residual edges accepted by the family. -/
theorem matching_slots {m : Nat} (ao : IsAO2 n C) (top : TopForm G C)
    (u v : Fin m → Fin n) (root : Fin m → Nat)
    (clean : ∀ i, root i ∈ tops G C)
    (on : ∀ i, gateVal n C (root i) (pairInput (u i) (v i)) = true)
    (outside : ∀ i, s(u i,v i) ∉ starEdges G C)
    (induced : ∀ i l : Fin m, i ≠ l → ∀ a b : Fin n, (a=u i ∨ a=v i) →
      (b=u l ∨ b=v l) → ¬G.Adj a b)
    (D : Finset Nat) (contains : ∀ i k, ancestor G C k (root i) → k ∈ D) :
    m ≤ 2 * D.card := by
  classical
  have orient (i : Fin m) : ∃ a b : Fin n, (a=u i ∨ a=v i) ∧ (b=u i ∨ b=v i) ∧
      separates G C (root i) a b := by
    rcases separator G C ao top (clean i) (outside i) (on i) with h|h
    · exact ⟨u i,v i,Or.inl rfl,Or.inr rfl,h⟩
    · exact ⟨v i,u i,Or.inr rfl,Or.inl rfl,h⟩
  choose a b ea eb sep using orient
  let y (i : Fin m) (z : Fin n) := decide (z = a i ∨ ∃ l : Fin m, l ≠ i ∧ z = b l)
  have active (i : Fin m) {z : Fin n} (h : y i z = true) : ∃ l : Fin m,
      (z=u l ∨ z=v l) ∧ z = (if l=i then a i else b l) := by
    rcases of_decide_eq_true h with eq|⟨l,neq,eq⟩
    · exact ⟨i,eq ▸ ea i,by simpa using eq⟩
    · exact ⟨l,eq ▸ eb l,by simpa [neq] using eq⟩
  have independent (i : Fin m) : graphFun G ∅ (y i) = false := by
    by_contra! no
    have yes : graphFun G ∅ (y i) = true := by simpa using no
    simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq] at yes
    obtain ⟨x,z,adj,xon,zon⟩ := yes
    obtain ⟨p,hp,xp⟩ := active i xon
    obtain ⟨q,hq,zq⟩ := active i zon
    by_cases eq : p=q
    · subst q
      exact adj.ne (xp.trans zq.symm)
    · exact induced p q eq x z hp hq adj
  have privateSide (i : Fin m) : ∃ k ∈ D, ∃ d : Fin 2, b i ∈ side C k d ∧
      ∀ l : Fin m, l ≠ i → b l ∉ side C k d := by
    obtain ⟨k,anc,d,own,miss⟩ := sep i (y i) (independent i) (by simp [y])
    refine ⟨k,contains i k anc,d,own,?_⟩
    intro l diff h
    exact miss ⟨b l,h,decide_eq_true (Or.inr ⟨l,diff,rfl⟩)⟩
  choose k kd d own miss using privateSide
  let slot (i : Fin m) : {k // k ∈ D} × Fin 2 := (⟨k i,kd i⟩,d i)
  have uniq : Function.Injective slot := by
    intro i l h
    by_contra diff
    have ek : k i = k l := congrArg (fun p : {k // k ∈ D} × Fin 2 => p.1.val) h
    have ed : d i = d l := congrArg Prod.snd h
    exact miss i l (Ne.symm diff) (by rw [ek,ed]; exact own l)
  simpa [Nat.mul_comm] using Fintype.card_le_of_injective slot uniq

theorem matching_junk {m : Nat} (least : IsLeastAO G C) (top : TopForm G C)
    (u v : Fin m → Fin n) (edge : ∀ i, s(u i,v i) ∈ Ustar G C)
    (induced : ∀ i l : Fin m, i ≠ l → ∀ a b : Fin n, (a=u i ∨ a=v i) →
      (b=u l ∨ b=v l) → ¬G.Adj a b) : m ≤ 2 * (junk G C).card := by
  have hit (i) := edge_top G C least (u := u i) (v := v i) (G.mem_edgeFinset.mp (Finset.mem_sdiff.mp (edge i)).1)
  choose j hj hon using hit
  exact matching_slots G C least.1 top u v j hj hon (fun i => (Finset.mem_sdiff.mp (edge i)).2)
    induced (junk G C) (fun _ _ p => ancestor_dirty G C p)

#print axioms matching_junk
end Simlowker.Types1735
