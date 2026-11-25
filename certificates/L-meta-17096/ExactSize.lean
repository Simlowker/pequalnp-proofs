import PEqualNP.Outside.L_meta_17095

namespace Simlowker.ThreeSun
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_17095

/-- Wires 0–5 are inputs. Each subsequent index is the output of one gate. -/
def witness : List Gate :=
  [⟨.or, [0, 1]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [1, 4]⟩,
   ⟨.or, [7, 8]⟩, ⟨.and, [7, 8]⟩, ⟨.and, [2, 9]⟩,
   ⟨.or, [5, 10]⟩, ⟨.and, [6, 12]⟩, ⟨.or, [11, 13]⟩]

theorem witness_shape : Monotone2 ⟨witness, 14⟩ := by
  intro g hg
  change g ∈ witness at hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem witness_eval : ∀ x, Circuit.eval ⟨witness,14⟩ (List.ofFn x) = posted x := by
  decide +kernel

theorem witness_legal : ∀ g ∈ witness,
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨hop, arity⟩ := witness_shape g hg
  refine ⟨?_, arity⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
  exact hop.elim Or.inl (fun h => Or.inr (Or.inl h))

/-- Counting AND and OR gates only gives the same optimum, with arbitrary NOT gates allowed. -/
theorem free_negation_circuit_optimum (k : ℕ) :
    (∃ (gs : List Gate) (o : Nat),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2) ∧
      gs.countP (fun g => !PEqualNP.Outside.L_meta_17095.Model.isNot g) ≤ k ∧
      ∀ x, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = posted x) ↔ 9 ≤ k := by
  constructor
  · rintro ⟨gs, o, legal, bound, ok⟩
    exact (binaryLower (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb) gs o legal ok).trans bound
  · intro h
    exact ⟨witness, 14, witness_legal, h, witness_eval⟩

#print axioms free_negation_circuit_optimum
theorem exact_size (s : ℕ) : HasCircuitSize 6 posted s ↔ 9 ≤ s := by
  constructor
  · rintro ⟨⟨gs, o⟩, legal, size_le, correct⟩
    have h := binaryLower (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb) gs o legal correct
    change gs.length ≤ s at size_le
    exact h.trans (List.countP_le_length.trans size_le)
  · intro hs
    exact ⟨⟨witness,14⟩, witness_legal, hs, witness_eval⟩

theorem monotone_replacement (s : ℕ) (h : HasCircuitSize 6 posted s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x) = posted x :=
  ⟨⟨witness,14⟩, witness_shape, (exact_size s).mp h, witness_eval⟩

/-- A circuit of optimum total size cannot spend a gate on negation. -/
theorem optimal_no_not (gs : List Gate) (o : ℕ)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (ok : ∀ x, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = posted x)
    (small : gs.length ≤ 9) : ∀ g ∈ gs, g.op ≠ GateOp.not := by
  have lower := binaryLower (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb) gs o legal ok
  have all := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length (small.trans lower))
  intro g hg h
  have := all g hg
  simp [PEqualNP.Outside.L_meta_17095.Model.isNot, h] at this

#print axioms optimal_no_not
#print axioms exact_size
#print axioms monotone_replacement
end Simlowker.ThreeSun

namespace Simlowker.ThreeSun.FormulaBound
open PEqualNP.Outside.L_meta_17095

/-- Rectangle weights for the signed formula game on this truth table. -/
abbrev Matrix := Nat → Nat → Int

def col (w : Matrix) (rows : List Nat) (j : Nat) :=
  (rows.map (fun i => w i j)).sum

def rect (w : Matrix) (rows cols : List Nat) :=
  (cols.map (col w rows)).sum

def upper (w : Matrix) (rows cols : List Nat) :=
  (cols.map (fun j => max 0 (col w rows j))).sum

theorem upper_nonneg (w : Matrix) (a b) : 0 ≤ upper w a b := by
  induction b with
  | nil => rfl
  | cons j js ih =>
    simp only [upper,List.map_cons,List.sum_cons] at *
    omega

theorem rect_le_upper (w : Matrix) (a : List Nat) {b c : List Nat} (h : b.Sublist c) :
    rect w a b ≤ upper w a c := by
  induction h with
  | slnil => rfl
  | cons x _ ih =>
    simp only [upper,List.map_cons,List.sum_cons] at *
    omega
  | cons_cons x _ ih =>
    simp only [upper,rect,List.map_cons,List.sum_cons] at *
    omega

theorem split (xs : List Nat) (f : Nat → Int) (p : Nat → Bool) :
    (xs.map f).sum = ((xs.filter p).map f).sum + ((xs.filter (fun i => !p i)).map f).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : p x <;> simp [h] <;> omega

theorem split_cols (w : Matrix) (a b : List Nat) (p : Nat → Bool) :
    rect w a b = rect w a (b.filter p) + rect w a (b.filter (fun i => !p i)) :=
  split b (col w a) p

theorem split_rows (w : Matrix) (a b : List Nat) (p : Nat → Bool) :
    rect w a b = rect w (a.filter p) b + rect w (a.filter (fun i => !p i)) b := by
  induction b with
  | nil => rfl
  | cons j js ih =>
    have h : col w a j = col w (a.filter p) j + col w (a.filter (fun i => !p i)) j :=
      split a (fun i => w i j) p
    simp only [rect, List.map_cons, List.sum_cons] at *
    omega

inductive Formula where
  | var (i : Fin 14)
  | disj (l r : Formula)
  | conj (l r : Formula)

def Formula.eval (v : Fin 14 → Bool) : Formula → Bool
  | .var i => v i
  | .disj l r => l.eval v || r.eval v
  | .conj l r => l.eval v && r.eval v

def Formula.cost (c : Fin 14 → Int) : Formula → Int
  | .var i => c i
  | .disj l r | .conj l r => l.cost c + r.cost c

theorem variable_filter {xs ys : List Nat} (h : xs.Sublist ys) (p : Nat → Bool)
    (yes : ∀ i ∈ xs, p i = true) : xs.Sublist (ys.filter p) := by
  have hh := h.filter p
  rwa [List.filter_eq_self.mpr yes] at hh

theorem formula_bound (w : Matrix) (rows cols : List Nat) (yes no : Nat → Fin 14 → Bool)
    (cost : Fin 14 → Int)
    (cert : ∀ v a b, a.Sublist (rows.filter fun i => yes i v) →
      b.Sublist (cols.filter fun j => !no j v) → rect w a b ≤ cost v)
    (f : Formula) {a b : List Nat} (ha : a.Sublist rows) (hb : b.Sublist cols)
    (hy : ∀ i ∈ a, f.eval (yes i) = true) (hn : ∀ j ∈ b, f.eval (no j) = false) :
    rect w a b ≤ f.cost cost := by
  induction f generalizing a b with
  | var v =>
    exact cert v a b (variable_filter ha _ hy)
      (variable_filter hb _ (fun j hj => by have h : no j v=false := hn j hj; simp [h]))
  | conj l r il ir =>
    let p := fun j => !(l.eval (no j))
    have hl := il ha ((List.filter_sublist (p := p)).trans hb)
      (fun i hi => (Bool.and_eq_true_iff.mp (hy i hi)).1) (by
        intro j hj
        simpa [p] using (List.mem_filter.mp hj).2)
    have hr := ir ha ((List.filter_sublist (p := fun j => !p j)).trans hb)
      (fun i hi => (Bool.and_eq_true_iff.mp (hy i hi)).2) (by
        intro j hj
        have hp : l.eval (no j) = true := by simpa [p] using (List.mem_filter.mp hj).2
        simpa [Formula.eval,hp] using hn j (List.mem_filter.mp hj).1)
    change rect w a b ≤ l.cost cost + r.cost cost
    rw [split_cols w a b p]
    exact add_le_add hl hr
  | disj l r il ir =>
    let p := fun i => l.eval (yes i)
    have hl := il ((List.filter_sublist (p := p)).trans ha) hb
      (fun i hi => (List.mem_filter.mp hi).2)
      (fun j hj => (Bool.or_eq_false_iff.mp (hn j hj)).1)
    have hr := ir ((List.filter_sublist (p := fun i => !p i)).trans ha) hb (by
        intro i hi
        have hp : l.eval (yes i) = false := by simpa [p] using (List.mem_filter.mp hi).2
        simpa [Formula.eval,hp] using hy i (List.mem_filter.mp hi).1)
      (fun j hj => (Bool.or_eq_false_iff.mp (hn j hj)).2)
    change rect w a b ≤ l.cost cost + r.cost cost
    rw [split_rows w a b p]
    exact add_le_add hl hr


def tr (w : Matrix) : Matrix := fun a b => w b a

theorem rect_cons_row (w : Matrix) (i : Nat) (a b : List Nat) :
    rect w (i::a) b = col (tr w) b i + rect w a b := by
  induction b with
  | nil => simp [rect,col]
  | cons j js ih =>
    change col w (i::a) j + rect w (i::a) js = _ + (col w a j + rect w a js)
    rw [ih]
    simp [col,tr]
    omega

theorem transpose (w : Matrix) (a b : List Nat) : rect w a b=rect (tr w) b a := by
  induction a with
  | nil => induction b <;> simp_all [rect,col]
  | cons i is ih => rw [rect_cons_row,ih]; rfl

def rowInput : List Nat := [3, 5, 6, 10, 12, 17, 20, 25, 26, 33, 34, 41, 44, 50, 52]
def colInput : List Nat := [1, 2, 4, 9, 18, 24, 36, 40, 48]
def rows := List.range rowInput.length
def cols := List.range colInput.length
def weights : List (List Int) := [[0, 0, 0, 1, 1, -1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1, -1, 0], [0, 0, 0, 0, 1, 0, 1, 0, -1], [0, 1, 0, 1, 0, 1, -1, 0, 0], [0, 0, 1, 1, -1, 0, 0, 1, 0], [1, 0, 0, 0, 1, 1, -1, 0, 0], [0, 0, 1, -1, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, -1, 0, 1, 1, 0], [0, 1, 0, -1, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0]]
def wmat : Matrix := fun i j => (weights.getD i []).getD j 0
def price : Int := 2
def sample (r : Nat) (v : Fin 6) : Bool := r.testBit v.val
/-- Six positive variables, their six negations, then the constants false and true. -/
def vector (x : Fin 6 → Bool) (v : Fin 14) : Bool :=
  if h : v.val < 6 then x ⟨v.val,h⟩
  else if k : v.val < 12 then !x ⟨v.val-6, by omega⟩
  else decide (v.val=13)
def literal (r : Nat) := vector (sample r)
def positive (r : Nat) := literal (rowInput.getD r 0)
def negative (r : Nat) := literal (colInput.getD r 0)

def cap (v : Fin 14) : Bool :=
  let rs := rows.filter fun i => positive i v
  let cs := cols.filter fun j => !negative j v
  if rs.isEmpty || cs.isEmpty then true else
  if rs.length ≤ cs.length then rs.sublists.all fun a => decide (upper wmat a cs ≤ price)
  else cs.sublists.all fun b => decide (upper (tr wmat) b rs ≤ price)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caps : ∀ v : Fin 14, cap v = true := by decide +kernel

theorem literal_bound (v : Fin 14) (a b : List Nat)
    (ha : a.Sublist (rows.filter fun i => positive i v))
    (hb : b.Sublist (cols.filter fun j => !negative j v)) : rect wmat a b ≤ price := by
  have hc := caps v
  dsimp only [cap] at hc
  split at hc
  · rename_i h
    rcases Bool.or_eq_true_iff.mp h with h|h
    · rw [List.isEmpty_iff.mp h] at ha
      have e : a=[] := List.sublist_nil.mp ha
      rw [e,transpose];simp [rect,price]
    · rw [List.isEmpty_iff.mp h] at hb
      have e : b=[] := List.sublist_nil.mp hb
      rw [e];simp [rect,price]
  · split at hc
    · exact (rect_le_upper _ _ hb).trans (decide_eq_true_iff.mp (List.all_eq_true.mp hc _ (List.mem_sublists.mpr ha)))
    · rw [transpose]
      exact (rect_le_upper _ _ ha).trans (decide_eq_true_iff.mp (List.all_eq_true.mp hc _ (List.mem_sublists.mpr hb)))

theorem total : rect wmat rows cols = 21 := by decide +kernel

def Formula.leaves : Formula → Nat
  | .var _ => 1
  | .conj a b | .disj a b => a.leaves+b.leaves

theorem cost_eq (e : Formula) : e.cost (fun _ => price) = price*(e.leaves:Int) := by
  induction e with
  | var _ => simp [Formula.cost,Formula.leaves]
  | conj a b ih jh | disj a b ih jh => simp [Formula.cost,Formula.leaves,ih,jh,mul_add]

theorem trueRows : ∀ r ∈ rowInput, posted (sample r)=true := by decide +kernel
theorem falseCols : ∀ r ∈ colInput, posted (sample r)=false := by decide +kernel

theorem getD_in {xs : List Nat} {i : Nat} (hi : i < xs.length) : xs.getD i 0 ∈ xs := by
  simp [List.getD_eq_getElem?_getD,hi]

theorem lower (e : Formula) (ok : ∀ r, e.eval (literal r)=posted (sample r)) :
    11 ≤ e.leaves := by
  have h := formula_bound wmat rows cols positive negative (fun _ => price) literal_bound e
    (List.Sublist.refl _) (List.Sublist.refl _)
    (fun i hi => (ok _).trans (trueRows _ (getD_in (List.mem_range.mp hi))))
    (fun j hj => (ok _).trans (falseCols _ (getD_in (List.mem_range.mp hj))))
  rw [total,cost_eq] at h
  unfold price at h
  omega
def tree : Formula := (.disj (.disj (.conj (.disj (.var 1) (.var 0)) (.disj (.var 5) (.var 2))) (.conj (.disj (.var 2) (.var 0)) (.disj (.var 4) (.var 1)))) (.conj (.disj (.var 2) (.var 1)) (.var 3)))
theorem tree_leaves : tree.leaves = 11 := rfl
theorem tree_compute : ∀ x : Fin 6 → Bool, tree.eval (vector x) = posted x := by decide +kernel

def Formula.gates : Formula → Nat
  | .var _ => 0
  | .conj l r | .disj l r => l.gates + r.gates + 1

theorem gate_count (e : Formula) : e.gates + 1 = e.leaves := by
  induction e with
  | var _ => rfl
  | conj a b ha hb | disj a b ha hb =>
    simp only [Formula.gates, Formula.leaves]
    omega

theorem formula_optimum (k : ℕ) :
    (∃ e : Formula, e.gates ≤ k ∧ ∀ x, e.eval (vector x) = posted x) ↔ 10 ≤ k := by
  constructor
  · rintro ⟨e, size_le, ok⟩
    have leaves := lower e (fun r => ok (sample r))
    have := gate_count e
    omega
  · intro h
    exact ⟨tree, h, tree_compute⟩

#print axioms formula_optimum
end Simlowker.ThreeSun.FormulaBound

namespace Simlowker.ThreeSun.FormulaBound
open PEqualNP.Outside.L_meta_17095

def flipLiteral (v : Fin 14) : Fin 14 :=
  if a : v.val < 6 then ⟨v.val + 6, by omega⟩
  else if b : v.val < 12 then ⟨v.val - 6, by omega⟩
  else if v.val = 12 then 13 else 12

theorem flip_value : ∀ (v : Fin 14) (x : Fin 6 → Bool),
    vector x (flipLiteral v) = !(vector x v) := by decide +kernel

def Formula.dual : Formula → Formula
  | .var v => .var (flipLiteral v)
  | .conj l r => .disj l.dual r.dual
  | .disj l r => .conj l.dual r.dual

theorem dual_cost (e : Formula) : e.dual.gates = e.gates := by
  induction e <;> simp [Formula.dual, Formula.gates, *]

theorem dual_eval (e : Formula) (x : Fin 6 → Bool) :
    e.dual.eval (vector x) = !(e.eval (vector x)) := by
  induction e <;> simp [Formula.dual, Formula.eval, flip_value, *]

/-- Arbitrary negations in a formula have zero cost in this model. -/
inductive BoolTree where
  | atom (v : Fin 14)
  | neg (e : BoolTree)
  | conj (l r : BoolTree)
  | disj (l r : BoolTree)

def BoolTree.eval (x : Fin 6 → Bool) : BoolTree → Bool
  | .atom v => vector x v
  | .neg e => !(e.eval x)
  | .conj l r => l.eval x && r.eval x
  | .disj l r => l.eval x || r.eval x

def BoolTree.binaryGates : BoolTree → Nat
  | .atom _ => 0
  | .neg e => e.binaryGates
  | .conj l r | .disj l r => l.binaryGates + r.binaryGates + 1

def BoolTree.normalize : BoolTree → Formula
  | .atom v => .var v
  | .neg e => e.normalize.dual
  | .conj l r => .conj l.normalize r.normalize
  | .disj l r => .disj l.normalize r.normalize

theorem normalization_eval (e : BoolTree) (x : Fin 6 → Bool) :
    e.normalize.eval (vector x) = e.eval x := by
  induction e <;> simp [BoolTree.normalize, BoolTree.eval, Formula.eval, dual_eval, *]

theorem normalization_gates (e : BoolTree) : e.normalize.gates = e.binaryGates := by
  induction e <;> simp [BoolTree.normalize, BoolTree.binaryGates, Formula.gates, dual_cost, *]

def Formula.asTree : Formula → BoolTree
  | .var v => .atom v
  | .disj l r => .disj l.asTree r.asTree
  | .conj l r => .conj l.asTree r.asTree

theorem asTree_left (e : Formula) : e.asTree.normalize = e := by
  induction e <;> simp [Formula.asTree, BoolTree.normalize, *]

theorem free_negation_tree_optimum (k : ℕ) :
    (∃ e : BoolTree, e.binaryGates ≤ k ∧ ∀ x, e.eval x = posted x) ↔ 10 ≤ k := by
  constructor
  · rintro ⟨e, size_le, ok⟩
    exact (formula_optimum k).mp ⟨e.normalize, (normalization_gates e).trans_le size_le,
      fun x => (normalization_eval e x).trans (ok x)⟩
  · intro h
    obtain ⟨e, size_le, ok⟩ := (formula_optimum k).mpr h
    refine ⟨e.asTree, ?_, ?_⟩
    · simpa only [← normalization_gates, asTree_left] using size_le
    · intro x
      simpa only [← normalization_eval, asTree_left] using ok x

#print axioms free_negation_tree_optimum
end Simlowker.ThreeSun.FormulaBound

-- Circuit unfolding adapted from the earlier Simlowker certificate for L-meta-12982.
namespace Simlowker.ThreeSun.Depth
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_17095 Simlowker.ThreeSun.FormulaBound
inductive Expr where
  | var (i : Fin 6)
  | constant (c : Bool)
  | neg (t : Expr)
  | branch (andGate : Bool) (a b : Expr)
  deriving Repr

def Expr.dep : Expr → Nat
  | .var _ | .constant _ => 0
  | .neg t => t.dep
  | .branch _ a b => max a.dep b.dep + 1
def Expr.eval (x : Fin 6 → Bool) : Expr → Bool
  | .var i => x i
  | .constant c => c
  | .neg a => !a.eval x
  | .branch c a b => if c then a.eval x && b.eval x else a.eval x || b.eval x


def Expr.asTree : Expr → BoolTree
  | .var i => .atom ⟨i.val, by omega⟩
  | .constant c => .atom (if c then 13 else 12)
  | .neg t => .neg t.asTree
  | .branch a l r => if a then .conj l.asTree r.asTree else .disj l.asTree r.asTree

theorem asTree_eval (t : Expr) (x : Fin 6 → Bool) : t.asTree.eval x = t.eval x := by
  induction t with
  | var i => simp [Expr.asTree, BoolTree.eval, Expr.eval, vector, i.isLt]
  | constant c => cases c <;> rfl
  | neg t h => simp [Expr.asTree, BoolTree.eval, Expr.eval, h]
  | branch c l r h j => cases c <;> simp [Expr.asTree, BoolTree.eval, Expr.eval, h, j]

theorem tree_capacity (t : Expr) : t.asTree.binaryGates + 1 ≤ 2^t.dep := by
  induction t with
  | var _ => rfl
  | constant c => cases c <;> rfl
  | neg t h => exact h
  | branch c l r hl hr =>
    have lb : 2^l.dep ≤ (2:Nat)^(max l.dep r.dep) := Nat.pow_le_pow_right (by decide) (le_max_left _ _)
    have rb : 2^r.dep ≤ (2:Nat)^(max l.dep r.dep) := Nat.pow_le_pow_right (by decide) (le_max_right _ _)
    cases c <;> simp only [Expr.asTree, Bool.false_eq_true, ↓reduceIte, BoolTree.binaryGates, Expr.dep, pow_succ] <;> omega

theorem expr_min_depth (t : Expr) (computes : ∀ x, t.eval x = posted x) : 4 ≤ t.dep := by
  have bound := (free_negation_tree_optimum t.asTree.binaryGates).mp
    ⟨t.asTree, le_rfl, fun x => (asTree_eval t x).trans (computes x)⟩
  have size := tree_capacity t
  by_contra! shallow
  have := Nat.pow_le_pow_right (n:=2) (by decide) (show t.dep ≤ 3 by omega)
  norm_num at this
  omega
abbrev Annot := Expr × Nat
def dummy : Annot := (.constant false,0)
def choose (o : GateOp) (es : List Expr) : Expr :=
  match o, es with
  | .and, [] => .constant true
  | .or, [] => .constant false
  | .and, [a] | .or, [a] => a
  | .and, a::b::_ => .branch true a b
  | .or, a::b::_ => .branch false a b
  | .not, a::_ => .neg a
  | .not, [] => .constant true
  | _, _ => .constant false
def make (o : GateOp) (ps : List Annot) : Annot :=
  (choose o (ps.map Prod.fst), (ps.map Prod.snd).foldr max 0 + 1)
def validOp (o : GateOp) := o = .and ∨ o = .or ∨ o = .not
def readout (x : Fin 6 → Bool) (p : Annot) := p.1.eval x
theorem gateEval (o : GateOp) (ps : List Annot) (x : Fin 6 → Bool) (op : validOp o) (arity : ps.length≤2) :
    readout x (make o ps)=o.eval (ps.map (readout x)) := by
  rcases op with rfl | rfl | rfl <;> rcases ps with _ | ⟨a,_|⟨b,_|⟨c,cs⟩⟩⟩ <;>
    simp_all [make,choose,readout,Expr.eval,GateOp.eval]
def safe (p : Annot) := p.1.dep ≤ p.2
theorem gateSafe (o : GateOp) (ps : List Annot) (each : ∀ p ∈ ps,safe p) (op : validOp o) (arity : ps.length≤2) :
    safe (make o ps) := by
  rcases op with rfl | rfl | rfl <;> rcases ps with _ | ⟨a,_|⟨b,_|⟨c,cs⟩⟩⟩ <;>
    simp_all [make,choose,safe,Expr.dep] <;> omega

def reading (ps : List Annot) (g : Gate) := g.inputs.map fun i => ps.getD i dummy
def step (ps : List Annot) (g : Gate) := ps ++ [make g.op (reading ps g)]
def initial : List Annot := List.ofFn fun i : Fin 6 => (Expr.var i,0)
def unfoldCircuit (C : Circuit) := (C.gates.foldl step initial).getD C.output dummy

theorem traceMap {α : Type} (proj : Annot → α) (extend : List α → Gate → List α) (gs : List Gate)
    (ok : ∀ g∈gs, validOp g.op ∧ g.inputs.length≤2)
    (comm : ∀ ps g, validOp g.op → g.inputs.length≤2 → (step ps g).map proj=extend (ps.map proj) g)
    (ps : List Annot) : (gs.foldl step ps).map proj=gs.foldl extend (ps.map proj) := by
  induction gs generalizing ps with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (fun h hm => ok h (by simp [hm])),comm ps g (ok g (by simp)).1 (ok g (by simp)).2]

theorem unfold_eval (C : Circuit) (h : FanInTwo C) (x : Fin 6 → Bool) :
    (unfoldCircuit C).1.eval x=C.eval (List.ofFn x) := by
  let f := fun (v : List Bool) (g : Gate) => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]
  have comm (ps : List Annot) (g : Gate) (op : validOp g.op) (ar : g.inputs.length≤2) :
      (step ps g).map (readout x)= f (ps.map (readout x)) g := by
    have e := gateEval g.op (reading ps g) x op (by simpa [reading] using ar)
    have m (i : Nat) : (ps.map (readout x)).getD i false=readout x (ps.getD i dummy) :=
      List.getD_map ps dummy (readout x)
    simp only [step,f,List.map_append,List.map_cons,List.map_nil,e]
    simp only [reading,List.map_map,Function.comp_def,m]
  have t := traceMap (readout x) f C.gates h comm initial
  have start : initial.map (readout x)=List.ofFn x := by simp [initial,readout,Expr.eval]
  rw [start] at t
  have out := congrArg (fun ps : List Bool => ps.getD C.output false) t
  calc readout x (unfoldCircuit C) = ((C.gates.foldl step initial).map (readout x)).getD C.output false :=
         (List.getD_map _ dummy (readout x)).symm
       _ = C.eval (List.ofFn x) := out

theorem unfold_depth (C : Circuit) (h : FanInTwo C) : (unfoldCircuit C).2=C.depth 6 := by
  let f := fun (v : List Nat) (g : Gate) => v ++ [(g.inputs.map fun i => v.getD i 0).foldr max 0+1]
  have comm (ps : List Annot) (g : Gate) (_ : validOp g.op) (_ : g.inputs.length≤2) :
      (step ps g).map Prod.snd=f (ps.map Prod.snd) g := by
    have m (i : Nat) : (ps.map Prod.snd).getD i 0=(ps.getD i dummy).2 := List.getD_map ps dummy Prod.snd
    simp only [step,f,make,List.map_append,List.map_nil,List.map_cons,reading,List.map_map,Function.comp_def,m]
  have t := traceMap Prod.snd f C.gates h comm initial
  have start : initial.map Prod.snd=List.replicate 6 0 := by decide +kernel
  rw [start] at t
  calc (unfoldCircuit C).2 = ((C.gates.foldl step initial).map Prod.snd).getD C.output 0 :=
         (List.getD_map _ dummy Prod.snd).symm
       _ = C.depth 6 := congrArg (fun ps : List Nat => ps.getD C.output 0) t

theorem readSafe (ps : List Annot) (all : ∀ p∈ps,safe p) (i : Nat) : safe (ps.getD i dummy) := by
  by_cases h : i<ps.length
  · rw [List.getD_eq_getElem _ _ h]; exact all _ (List.getElem_mem _)
  · have hi : ps.length ≤ i := by omega
    rw [List.getD_eq_default _ _ hi]
    exact Nat.le_refl 0
theorem traceSafe (gs : List Gate) (h : ∀ g∈gs,validOp g.op ∧ g.inputs.length≤2)
    (ps : List Annot) (all : ∀ p∈ps,safe p) : ∀ p∈gs.foldl step ps,safe p := by
  induction gs generalizing ps with
  | nil => exact all
  | cons g gs ih =>
    apply ih (fun q hq => h q (by simp [hq]))
    intro p hp
    rcases List.mem_append.mp hp with old | new
    · exact all p old
    · obtain rfl := List.mem_singleton.mp new
      apply gateSafe _ _ _ (h g (by simp)).1 (by simpa [reading] using (h g (by simp)).2)
      intro s hs
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hs
      exact readSafe ps all i
theorem circuit_depth_at_least_four (C : Circuit) (h : FanInTwo C)
    (computes : ∀ x : Fin 6 → Bool,C.eval (List.ofFn x)=posted x) : 4≤C.depth 6 := by
  have bound := expr_min_depth (unfoldCircuit C).1 fun x => (unfold_eval C h x).trans (computes x)
  have safeInit : ∀ p∈initial,safe p := by
    intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact Nat.le_refl 0
  have sound := readSafe _ (traceSafe C.gates h initial safeInit) C.output
  exact (bound.trans sound).trans_eq (unfold_depth C h)

def balanced : Circuit := ⟨[⟨.or, [1, 0]⟩,⟨.or, [5, 2]⟩,⟨.and, [6, 7]⟩,⟨.or, [2, 0]⟩,⟨.or, [4, 1]⟩,⟨.and, [9, 10]⟩,⟨.or, [8, 11]⟩,⟨.or, [2, 1]⟩,⟨.and, [13, 3]⟩,⟨.or, [12, 14]⟩],15⟩

theorem balanced_shape : balanced.size=10 ∧ balanced.depth 6=4 := by decide +kernel
theorem balanced_correct : ∀ x, balanced.eval (List.ofFn x)=posted x := by decide +kernel
theorem balanced_legal : FanInTwo balanced := by
  intro g hg
  simp only [balanced, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem minimum_depth (k : Nat) :
    (∃ C : Circuit, FanInTwo C ∧ C.depth 6 ≤ k ∧ ∀ x, C.eval (List.ofFn x) = posted x) ↔ 4 ≤ k := by
  constructor
  · rintro ⟨C, legal, depth, computes⟩
    exact (circuit_depth_at_least_four C legal computes).trans depth
  · intro h
    exact ⟨balanced, balanced_legal, balanced_shape.2.trans_le h, balanced_correct⟩
#print axioms minimum_depth
#print axioms circuit_depth_at_least_four
#print axioms balanced_correct
end Simlowker.ThreeSun.Depth

open PEqualNP.CircuitLowerBounds in
theorem Simlowker.ThreeSun.witness_depth : (Circuit.mk Simlowker.ThreeSun.witness 14).depth 6 = 5 := by decide +kernel
