import TightBudget3722
namespace IncidenceBudget

inductive Tree where
  | dead
  | var (i : Nat)
  | node (isAnd : Bool) (a b : Tree)

def sig : Tree → Sig
  | .dead => (∅,0)
  | .var i => ({i},1)
  | .node _ a b => join (sig a) (sig b)

def op (d a b : Bool) := if d then a && b else a || b
def linop (d : Bool) (a b : Bool × Bool) : Bool × Bool :=
  if d then (a.1 && b.1,(a.1 && b.2) || (a.2 && b.1)) else (a.1 || b.1,a.2 || b.2)

def ev (x : Nat → Bool) : Tree → Bool
  | .dead => false
  | .var i => x i
  | .node d a b => op d (ev x a) (ev x b)

def lin (mark x : Nat → Bool) : Tree → Bool × Bool
  | .dead => (false,false)
  | .var i => if mark i then (false,x i) else (x i,false)
  | .node d a b => linop d (lin mark x a) (lin mark x b)

theorem card_le (e : Tree) : (sig e).1.card≤(sig e).2 := by
  induction e with
  | dead => rfl
  | var i => simp [sig]
  | node d a b ia ib => exact (Finset.card_union_le ..).trans (Nat.add_le_add ia ib)

theorem ev_agree (e : Tree) {x y : Nat → Bool} (h : ∀ i∈(sig e).1,x i=y i) : ev x e=ev y e := by
  induction e with
  | dead => rfl
  | var i => exact h i (Finset.mem_singleton_self _)
  | node d a b ia ib =>
    exact congrArg₂ (op d) (ia fun i hi => h i (Finset.mem_union_left _ hi))
      (ib fun i hi => h i (Finset.mem_union_right _ hi))

theorem constant_part (e : Tree) (m x : Nat → Bool) :
    (lin m x e).1=ev (fun i => x i && !m i) e := by
  induction e with
  | dead => rfl
  | var i => cases h : m i <;> simp [lin,ev,h]
  | node d a b ia ib => cases d <;> simp [lin,ev,linop,op,ia,ib]

theorem constant_when {e : Tree} {m x : Nat → Bool} {i : Nat}
    (active : ∀ j, m j=true → x j=true → j=i) (out : i∉(sig e).1) :
    (lin m x e).1=ev x e := by
  rw [constant_part]
  apply ev_agree
  intro j hj
  cases hm : m j <;> cases hx : x j <;> simp
  exact False.elim (out ((active j hm hx) ▸ hj))

theorem linear_when_tight (e : Tree) (m x : Nat → Bool) (i : Nat)
    (active : ∀ j, m j=true → x j=true → j=i) (tight : (sig e).2≤(sig e).1.card) :
    ((lin m x e).1 || (lin m x e).2) = ev x e := by
  induction e with
  | dead => rfl
  | var j => cases h : m j <;> simp [lin,ev,h]
  | node d a b ia ib =>
    have ha := card_le a
    have hb := card_le b
    change (sig a).2+(sig b).2 ≤ ((sig a).1 ∪ (sig b).1).card at tight
    have hu := Finset.card_union_le (sig a).1 (sig b).1
    have dis := Finset.card_union_eq_card_add_card.mp (show ((sig a).1∪(sig b).1).card =
        (sig a).1.card+(sig b).1.card by omega)
    have aa := ia (by omega)
    have bb := ib (by omega)
    have alone : i∉(sig a).1 ∨ i∉(sig b).1 := by
      by_cases h : i∈(sig a).1
      · exact Or.inr (fun h' => Finset.disjoint_left.mp dis h h')
      · exact Or.inl h
    have clean : (lin m x a).1=ev x a ∨ (lin m x b).1=ev x b :=
      alone.imp (constant_when active) (constant_when active)
    have law : ∀ (d : Bool) (a b : Bool × Bool), (a.1=(a.1||a.2) ∨ b.1=(b.1||b.2)) →
        ((linop d a b).1 || (linop d a b).2) = op d (a.1||a.2) (b.1||b.2) := by decide +kernel
    rw [←aa,←bb] at clean
    exact (law d _ _ clean).trans (congrArg₂ (op d) aa bb)

#print axioms linear_when_tight
end IncidenceBudget
