import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Sublists
import Mathlib.Algebra.Order.Ring.Int

namespace PetersenNegated3971

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
  | var (i : Fin 13)
  | disj (l r : Formula)
  | conj (l r : Formula)

def Formula.eval (v : Fin 13 → Bool) : Formula → Bool
  | .var i => v i
  | .disj l r => l.eval v || r.eval v
  | .conj l r => l.eval v && r.eval v

def Formula.cost (c : Fin 13 → Int) : Formula → Int
  | .var i => c i
  | .disj l r | .conj l r => l.cost c + r.cost c

theorem variable_filter {xs ys : List Nat} (h : xs.Sublist ys) (p : Nat → Bool)
    (yes : ∀ i ∈ xs, p i = true) : xs.Sublist (ys.filter p) := by
  have hh := h.filter p
  rwa [List.filter_eq_self.mpr yes] at hh

theorem formula_bound (w : Matrix) (rows cols : List Nat) (yes no : Nat → Fin 13 → Bool)
    (cost : Fin 13 → Int)
    (cert : ∀ v a, a.Sublist (rows.filter fun i => yes i v) →
      upper w a (cols.filter fun j => !no j v) ≤ cost v)
    (f : Formula) {a b : List Nat} (ha : a.Sublist rows) (hb : b.Sublist cols)
    (hy : ∀ i ∈ a, f.eval (yes i) = true) (hn : ∀ j ∈ b, f.eval (no j) = false) :
    rect w a b ≤ f.cost cost := by
  induction f generalizing a b with
  | var v =>
    apply (rect_le_upper w a (variable_filter hb (fun j => !no j v) (by
      intro j hj
      have hh : no j v = false := hn j hj
      simp [hh]))).trans
    exact cert v a (variable_filter ha _ hy)
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



def positive : List Nat := [3, 6, 12, 17, 34, 68, 136, 80, 160, 144, 257, 264]
def negative : List Nat := [0, 1, 2, 4, 8, 16, 26, 32, 37, 56, 64, 74, 105, 128, 133, 193, 256, 274, 308, 352, 388, 450]

def rawValue (m i : Nat) : Bool := if i<9 then m.testBit i else m.testBit 1 || m.testBit 8
def literal (bit : Fin 10) (mask : Nat) (v : Fin 13) : Bool :=
  if v.val<10 then rawValue mask v.val else if v.val=12 then !(rawValue mask bit.val) else decide (v.val=11)

def Formula.leaves : Formula → Nat
  | .var _ => 1
  | .conj l r | .disj l r => l.leaves + r.leaves

theorem uniform_cost (f : Formula) (d : Int) :
    f.cost (fun _ => d) = (f.leaves : Int) * d := by
  induction f with
  | var i => simp [Formula.leaves,Formula.cost]
  | conj l r il ir => simp [Formula.leaves,Formula.cost,il,ir,add_mul]
  | disj l r il ir => simp [Formula.leaves,Formula.cost,il,ir,add_mul]

def ri := List.range 12
def ci := List.range 22
def yes (bit : Fin 10) i := literal bit (positive.getD i 0)
def no (bit : Fin 10) j := literal bit (negative.getD j 0)
def fromData (data : List (List Int)) : Matrix := fun i j => (data.getD i []).getD j 0
def valid (bit : Fin 10) (mat : Matrix) (d : Int) (v : Fin 13) : Bool :=
  let rs := ri.filter fun i => yes bit i v
  let cs := ci.filter fun j => !(no bit j v)
  if cs.isEmpty then true else rs.sublists.all fun rr => decide (upper mat rr cs ≤ d)
def w0 : Matrix := fromData [[0, 0, 0, 0, 0, 0, 60, 0, 0, 0, 0, 49, 0, 0, 0, 60, 0, 0, -60, 0, 0, 11], [0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, -16, 0, 0, 0, 0, 0, 11, 60, -60, 60, 76], [0, 0, 0, 0, 0, 0, 87, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, -11, 60, 0, 60, -76], [0, 0, 0, 0, 0, 0, 60, 0, 38, 0, 0, -49, 33, 0, 44, 0, 0, 0, 60, 0, 0, -71], [0, 0, 0, 0, 0, 0, 60, 0, 0, 0, 0, 60, 0, 0, 0, 0, 0, 0, 60, 60, -60, 0], [0, 0, 0, 71, 0, 0, -60, 0, 0, 0, 0, 16, 0, 0, 44, 0, 0, -11, 0, 60, 5, 44], [0, 0, 0, 0, 0, 0, 60, 0, 0, 0, 0, 27, 33, 0, 0, 0, 0, 0, -93, 0, 60, 60], [0, 0, 0, 0, 0, 0, 60, 0, 0, 0, 0, 55, 27, 0, -44, 0, 0, 60, 0, 16, -5, 22], [0, 0, 0, 0, 0, 0, -60, 0, 11, 0, 0, 0, 33, 0, 0, 0, 0, 0, 60, 16, 60, 60], [0, 0, 0, 0, 0, 0, 60, 0, -11, 0, 0, -27, -33, 0, 44, 0, 0, 0, 60, -16, 5, 71], [0, 0, 0, 0, 0, 0, -60, 0, 0, 0, 0, 0, 0, 0, 0, 60, 0, 0, 60, 0, 0, 60], [0, 0, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 60, 0, -60, 49]]
def w1 : Matrix := fromData [[0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 20, 0, 20, 0, 0, 0, -20, 0, 0, 20], [0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, -50, 0, 30, 0, 0, 0, 36, -6, 54, 56], [0, 0, 0, 0, 0, 0, 6, 0, 28, 59, 0, 6, 50, 0, 60, -32, 0, 0, 32, -26, -22, -11], [0, 0, 0, 0, 0, 80, 10, 0, 9, 10, 0, 0, 56, 0, 56, 0, 0, 0, 20, -54, -46, -10], [0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 84, 30, 0, -30, 0, 0, 0, 84, 6, -54, 0], [0, 0, 0, 0, 0, 0, -6, 0, 9, -50, 0, 0, 50, 0, 111, 32, 0, 0, 0, 32, 0, 6], [0, 0, 0, 0, 0, 0, 12, 0, -28, 42, 0, 0, 66, 0, 60, 32, 0, 0, -54, -6, 22, 6], [0, 0, 0, 0, 0, 0, 6, 0, -9, 114, 0, 0, 64, 0, -56, 0, 0, 0, 0, 54, 0, 1], [0, 0, 0, 0, 0, 0, -36, 0, 36, -42, 0, 0, 46, 36, 30, 0, 0, 0, 32, 6, 54, 0], [0, 0, 0, 0, 0, 0, 24, 0, -9, 42, 0, 0, -66, 0, 64, 0, 0, 0, 54, 0, 46, 10], [0, 0, 0, 0, 0, 0, -10, 0, 0, -10, 0, 0, 10, 0, 70, 0, 0, 0, 20, 54, 46, 0], [0, 0, 0, 0, 0, 0, 50, 0, 0, 70, 0, 0, 0, 0, -60, 0, 0, 0, 54, 32, 22, 11]]
def w2 : Matrix := fromData [[0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 41, 19, 0, 0, 0, 0, -51, 0, -19, 0, 28], [0, 0, 0, 6, 0, 0, 51, 0, 0, -19, 0, 0, -32, 0, 13, 0, 0, 6, 0, -38, 101, 63], [0, 0, 0, 0, 0, 0, 38, 0, 0, 51, 0, 0, 32, 0, 13, 0, 0, -6, 63, 0, 25, -63], [0, 0, 0, 0, 0, 0, 51, 0, 19, 19, 0, -41, 60, 0, 0, 41, 0, 51, 0, 0, 0, -60], [0, 0, 51, 0, 0, 0, 60, 0, 0, 19, 0, 9, 32, 0, -13, -19, 0, 0, 13, 57, -19, 0], [0, 0, 0, 0, 0, 0, -51, 0, 19, -32, 0, 0, 32, 0, 0, 0, 0, 0, 82, 38, 19, 51], [0, 0, 0, 0, 0, 0, 51, 0, 0, -9, 0, 9, 60, 0, 13, 19, 0, -13, -38, -51, 25, 63], [0, 0, 0, 0, 0, 0, 51, 0, -19, 32, 0, 41, 60, 0, 0, -41, 0, 0, 38, 0, -19, 19], [0, 0, 0, 0, 0, 0, -60, 0, 0, 9, 0, -9, 60, 69, 13, 19, 0, 0, 0, 51, 19, 0], [0, 0, 0, 0, 0, 0, 60, 0, 0, 9, 0, 0, -60, 0, 0, 41, 0, 13, 38, 0, 19, 60], [0, 0, 0, 0, 0, 0, -51, 0, 0, -19, 0, 0, 0, 0, 13, 88, 0, 51, 0, 19, 0, 51], [0, 0, 0, 0, 0, 0, 51, 0, 0, 19, 0, 51, 0, 0, -13, -19, 0, 13, 0, 51, -25, 57]]
def w3 : Matrix := fromData [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 60, 0, 0, 60, -60, 0, 0, 60], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 60, 60, -60, 60, 60], [0, 0, 0, 0, 0, 0, 0, 0, 40, 0, 0, 67, 0, 0, 60, 0, 0, -7, 20, -13, 0, -60], [0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 40, 0, 64, 8, 0, 60, 60, -4, -56, -60], [0, 0, 0, 0, 0, 0, 40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80, 60, 60, -60, 0], [0, 0, 0, 60, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56, 0, 0, -60, 0, 67, 4, 53], [0, 0, 0, 0, 0, 0, 40, 0, -40, 20, 0, 0, 40, 0, 60, 0, 0, 0, -60, 0, 0, 60], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40, 0, -56, 8, 0, 120, 0, 12, -4, 60], [0, 0, 0, 0, 0, 0, -40, 0, 48, 0, 0, 0, 40, 0, 0, 60, 0, -20, 20, 12, 60, 0], [0, 0, 0, 0, 0, 0, 40, 0, -8, 0, 0, 0, -40, 0, 56, -8, 0, 20, 60, -12, 56, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 60, 0, 0, -60, 60, 4, 56, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 60, 60, 0, -60, 0, 0, 7, 60, 13, 0, 40]]
def w4 : Matrix := fromData [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 60, 30, 0, 0, 0, 0, 0, 0, -30, 0, 30], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45, -45, 0, 45, 0, 0, 0, 0, -30, 75, 75], [0, 0, 0, 0, 0, 0, 0, 0, 30, 30, 0, 45, 45, 0, 60, 0, 0, 0, 20, 0, 10, -90], [0, 0, 0, 0, 0, 90, 0, 0, 30, 0, 0, -30, 60, 0, 30, 0, 0, 0, 0, 0, 0, -60], [0, 0, 45, 0, 0, 0, 35, 0, 0, 0, 0, 40, 45, 0, -45, 0, 0, 0, 0, 75, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 30, -30, 0, -45, 45, 0, 30, 0, 0, 0, 0, 30, 60, 45], [0, 0, 0, 0, 0, 0, 20, 0, -30, 0, 0, 40, 60, 0, 60, 0, 0, 0, -35, -15, -10, 60], [0, 0, 0, 0, 0, 0, 90, 0, -30, 30, 0, 30, 60, 0, -30, 0, 0, 0, 0, 0, -30, 30], [0, 0, 0, 0, 0, 0, -35, 0, 30, 0, 0, -40, 60, 0, 120, 0, 0, 0, 15, 15, 0, 0], [0, 0, 0, 0, 0, 0, 60, 0, 0, 0, 0, 0, -60, 0, 30, 0, 0, 0, 35, 0, 30, 60], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -30, 15, 0, 75, 0, 0, 0, 0, 30, 0, 60], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 90, 30, 0, -60, 0, 0, 0, 35, 15, 10, 60]]
def w5 : Matrix := fromData [[0, 0, 0, 0, 0, 0, 58, 0, 0, -4, 0, 46, 4, 0, 4, 0, 0, -55, 0, 0, -7, 16], [0, 0, 0, 0, 0, 0, 42, 0, 0, -4, 0, -24, -4, 0, 4, 0, 0, 0, 0, -53, 116, 78], [0, 0, 0, 0, 0, 0, 67, 0, 0, 4, 0, 35, 4, 0, 52, 0, 0, 0, 26, 0, 26, -78], [0, 14, 0, 0, 0, 0, 61, 0, 0, 4, 0, -46, 26, 0, 53, 28, 0, 55, 0, 0, 0, -67], [0, 0, 0, 0, 0, 0, 60, 0, 0, 4, 0, 1, 4, 0, -4, 0, 0, 58, 0, 113, -56, 0], [0, 0, 0, 0, 0, 0, -67, 0, 0, 0, 0, 24, 0, 0, 53, 0, 0, 0, 0, 53, 67, 42], [0, 0, 0, 0, 0, 0, 60, 0, 0, 0, 0, 35, 26, 0, 52, 0, 0, -59, -26, 0, -9, 68], [0, 0, 0, 0, 0, 0, 120, 0, 0, 0, 0, 67, 5, 0, -53, 28, 0, 0, 0, 0, 0, 21], [0, 0, 0, 0, 0, 0, -60, 1, 0, 34, 0, 0, 26, 0, 64, 0, 0, 0, 25, 0, 56, 0], [0, 0, 0, 0, 0, 0, 60, 0, 0, 0, 0, -34, -26, 0, 53, -28, 0, 59, 1, 0, 0, 67], [0, 0, 0, 0, 0, 0, -61, 0, 0, 0, 0, 0, 0, 0, 113, 0, 0, 55, 0, 0, 7, 58], [0, 0, 0, 0, 0, 0, 61, 0, 0, 0, 0, 59, 0, 0, -52, 0, 0, 59, 0, 0, 9, 52]]
def w6 : Matrix := fromData [[0, 0, 0, 0, 0, 0, 43, 0, 0, -8, 0, 0, 9, 0, 0, 0, 0, -34, -1, 0, 0, 35], [0, 0, 0, 0, 0, 0, 60, 0, 0, -42, 0, 0, -18, 0, 9, 0, 0, 53, 0, -7, 111, 7], [0, 0, 0, 0, 0, 0, 60, 0, 0, 42, 0, 0, 18, 0, 34, 0, 0, -53, 81, 0, 5, -24], [0, 0, 0, 0, 0, 0, 43, 0, 42, 42, 0, 0, 18, 0, 60, 0, 0, 34, 1, 0, -42, -35], [0, 0, 0, 0, 0, 0, 120, 0, 0, 42, 0, 0, 9, 0, -9, 0, 0, 0, 62, 7, -53, 0], [0, 0, 0, 0, 0, 0, -60, 0, 0, 0, 0, 36, 18, 0, 60, 0, 0, 0, 60, 7, 0, 24], [0, 0, 0, 0, 0, 0, 58, 0, 0, 23, 0, 18, 18, 0, 34, 0, 0, 0, -81, 0, 47, 24], [0, 0, 0, 0, 0, 0, 120, 0, 0, 0, 0, 18, 18, 0, -60, 0, 0, 0, 0, 0, 0, 60], [0, 0, 0, 0, 0, 0, -58, 0, 42, 19, 0, 0, 0, 0, 9, 0, 0, 0, 58, 0, 111, 0], [0, 0, 0, 0, 0, 0, 58, 0, -42, -19, 0, -18, -18, 0, 60, 0, 0, 0, 62, 0, 42, 18], [0, 0, 0, 0, 0, 0, -43, 0, 0, -34, 0, 0, 0, 0, 111, 0, 0, 34, 1, 0, 85, 0], [0, 0, 0, 0, 0, 0, 86, 0, 0, 34, 0, 0, 0, 0, -34, 0, 0, 53, 39, 0, -5, 0]]
def w7 : Matrix := fromData [[0, 0, 0, 0, 0, 0, 65, 0, 45, -10, 0, 5, 10, 0, 0, 0, 0, 10, -55, 0, 0, 40], [0, 0, 0, 0, 0, 0, 60, 0, 50, -10, 0, 0, -50, 0, 0, 0, 0, 60, 70, -10, 0, 0], [0, 0, 0, 10, 0, 0, 60, 0, 0, 10, 0, 0, 50, 0, 0, 0, 0, -60, 60, -10, 50, -40], [0, 0, 0, 0, 0, 0, 55, 0, 20, 10, 0, -5, 60, 0, 30, 10, 0, -10, 55, -55, 0, -40], [0, 0, 0, 0, 0, 0, 120, 0, -50, 10, 0, 0, 50, 0, 0, 0, 0, 0, 0, 60, 0, 0], [0, 0, 0, 70, 0, 0, -60, 0, 20, -10, 0, 0, 50, 0, 30, 0, 0, 0, 0, 30, 0, 40], [0, 0, 0, 0, 0, 0, 60, 0, 0, 0, 0, 0, 60, 0, 0, 0, 0, 0, -60, 0, 60, 40], [0, 0, 0, 0, 0, 0, 110, 0, -20, 10, 0, 5, 60, 0, -30, -10, 0, 0, 0, 55, 0, 0], [0, 0, 0, 0, 0, 0, -120, 0, 0, 0, 0, 0, 60, 0, 0, 0, 0, 0, 60, 0, 120, 0], [0, 0, 0, 0, 0, 0, 60, 0, 0, 0, 0, 0, -60, 0, 50, 10, 0, 0, 60, 0, 0, 40], [0, 20, 0, 0, 0, 0, -65, 0, 5, 0, 0, 0, 40, 0, 0, 0, 0, 10, 55, 55, 0, 0], [0, 0, 0, 0, 0, 0, 65, 0, 0, 0, 0, 55, 0, 0, 0, 0, 0, 60, 50, 10, -50, 0]]
def w8 : Matrix := fromData [[0, 0, 0, 0, 0, 0, 51, 0, 0, -51, 0, 69, 51, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 3, 8, 0, 0, 69, 0, 0, -8, 0, 20, -64, 0, 56, 0, 0, 0, 56, 0, 0, 26], [0, 0, 0, 0, 0, 0, 49, 0, 51, 8, 0, -20, 64, 0, 43, -51, 0, 0, 13, 0, 13, -26], [0, 0, 0, 0, 0, 0, 69, 0, 13, 51, 0, -69, 67, 0, 40, -11, 0, 0, 0, 0, 0, 0], [0, 0, 56, 0, 0, 0, 64, 0, 0, 51, 0, 0, 56, 0, -56, 0, 0, 0, 13, 0, 0, 0], [0, 0, 0, 69, 0, 0, -69, 0, 0, 0, 0, 20, 49, 0, 51, 51, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 53, 0, -43, -24, 0, 0, 67, 0, 43, 51, 0, 0, -26, 0, 13, 13], [0, 0, 0, 0, 0, 51, 69, 0, 0, 0, 0, 69, 40, 0, -51, 11, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, -64, 0, 56, 24, 0, 0, 40, 0, 56, 64, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 67, 0, -13, 24, 0, 0, -67, 29, 51, 11, 0, 0, 26, 0, 0, 0], [0, 0, 0, 0, 0, 0, -51, 0, 0, 0, 0, 0, 13, 0, 56, 0, 0, 0, 0, 0, 0, 51], [0, 0, 0, 0, 0, 0, 26, 0, 0, 0, 0, 94, 0, 0, -43, 0, 0, 0, 26, 31, -13, 26]]
def w9 : Matrix := fromData [[0, 0, 0, 0, 0, 0, 23, 0, 0, 0, 0, 35, 50, 0, 0, 0, 0, 17, -29, -21, 0, 26], [0, 0, 0, 0, 0, 0, 42, 0, 0, 0, 0, 18, -60, 0, 60, 0, 0, 21, 0, 0, 60, 31], [0, 0, 0, 0, 0, 0, 0, 0, 26, 42, 0, 18, 60, 0, 47, -26, 0, -21, 20, 0, 6, -31], [0, 0, 0, 0, 0, 41, 23, 0, 0, 0, 0, -35, 65, 0, 55, -5, 0, 17, 29, -25, -24, -26], [0, 0, 0, 0, 0, 0, 63, 0, 0, 0, 0, 35, 60, 0, -60, 0, 0, 22, 29, 31, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, -42, 0, -18, 60, 0, 102, 26, 0, 0, 0, 0, 18, 0], [0, 0, 0, 0, 0, 0, 3, 0, -26, 17, 0, 35, 65, 0, 47, 52, 0, -22, -20, -25, -6, 21], [0, 0, 0, 0, 0, 78, 0, 0, 0, 42, 13, 35, 42, 0, -60, 5, 0, 0, 0, 25, -18, 0], [0, 0, 0, 0, 0, 0, -3, 0, 26, -17, 0, -35, 55, 0, 60, 60, 0, -22, 14, 25, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 65, 0, 0, -65, 0, 60, 10, 0, 22, 6, 0, 24, 26], [0, 0, 0, 0, 0, 0, -23, 0, 0, 0, 0, 0, 10, 0, 60, 0, 0, -17, 29, 46, 24, 10], [0, 0, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, -47, 0, 0, 38, 20, 25, 6, 31]]

def edge (m : Nat) : Bool := ([(0, 1), (1, 2), (2, 3), (0, 4), (1, 5), (2, 6), (3, 7), (4, 6), (5, 7), (7, 4), (8, 0), (8, 3)] : List (Nat × Nat)).any fun e => m.testBit e.1 && m.testBit e.2
theorem from_certificate (bit : Fin 10) (n : Nat) (w : Matrix) (d : Int) (pos : 0<d)
    (mass : (n : Int)*d < rect w ri ci) (checked : ∀ v : Fin 13, valid bit w d v=true)
    (f : Formula) (spec : ∀ r : Fin 512, f.eval (literal bit r.val)=edge r.val) : n<f.leaves := by
  have ps : ∀ i∈ri, positive.getD i 0 < 512 ∧ edge (positive.getD i 0)=true := by decide +kernel
  have ns : ∀ j∈ci, negative.getD j 0 < 512 ∧ edge (negative.getD j 0)=false := by decide +kernel
  have h := formula_bound w ri ci (yes bit) (no bit) (fun _ => d) (by
    intro v rr sub
    have check' := checked v
    dsimp only [valid] at check'
    split at check'
    · rename_i he
      have eq := List.isEmpty_iff.mp he
      simp [eq,upper,pos.le]
    · exact decide_eq_true_iff.mp ((List.all_eq_true.mp check') rr (List.mem_sublists.mpr sub)))
    f (List.Sublist.refl ri) (List.Sublist.refl ci)
    (fun i hi => (spec ⟨_,(ps i hi).1⟩).trans (ps i hi).2)
    (fun j hj => (spec ⟨_,(ns j hj).1⟩).trans (ns j hj).2)
  rw [uniform_cost] at h
  by_contra! bad
  have cast : (f.leaves : Int)≤n := Int.ofNat_le.mpr bad
  exact (not_lt_of_ge (h.trans (mul_le_mul_of_nonneg_right cast pos.le))) mass

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem cert0 : (∀ v : Fin 13, valid 0 w0 121 v=true) ∧ 15*(121 : Int)<rect w0 ri ci := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem cert1 : (∀ v : Fin 13, valid 1 w1 122 v=true) ∧ 14*(122 : Int)<rect w1 ri ci := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem cert2 : (∀ v : Fin 13, valid 2 w2 121 v=true) ∧ 15*(121 : Int)<rect w2 ri ci := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem cert3 : (∀ v : Fin 13, valid 3 w3 121 v=true) ∧ 15*(121 : Int)<rect w3 ri ci := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem cert4 : (∀ v : Fin 13, valid 4 w4 120 v=true) ∧ 15*(120 : Int)<rect w4 ri ci := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem cert5 : (∀ v : Fin 13, valid 5 w5 122 v=true) ∧ 14*(122 : Int)<rect w5 ri ci := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem cert6 : (∀ v : Fin 13, valid 6 w6 121 v=true) ∧ 14*(121 : Int)<rect w6 ri ci := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem cert7 : (∀ v : Fin 13, valid 7 w7 120 v=true) ∧ 15*(120 : Int)<rect w7 ri ci := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem cert8 : (∀ v : Fin 13, valid 8 w8 121 v=true) ∧ 14*(121 : Int)<rect w8 ri ci := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem cert9 : (∀ v : Fin 13, valid 9 w9 121 v=true) ∧ 14*(121 : Int)<rect w9 ri ci := by decide +kernel

theorem all_raw (bit : Fin 10) (f : Formula) (spec : ∀ r : Fin 512, f.eval (literal bit r.val)=edge r.val) :
    15 ≤ f.leaves := by
  fin_cases bit
  · have bound := from_certificate 0 15 w0 121 (by decide) cert0.2 cert0.1 f spec
    omega
  · have bound := from_certificate 1 14 w1 122 (by decide) cert1.2 cert1.1 f spec
    omega
  · have bound := from_certificate 2 15 w2 121 (by decide) cert2.2 cert2.1 f spec
    omega
  · have bound := from_certificate 3 15 w3 121 (by decide) cert3.2 cert3.1 f spec
    omega
  · have bound := from_certificate 4 15 w4 120 (by decide) cert4.2 cert4.1 f spec
    omega
  · have bound := from_certificate 5 14 w5 122 (by decide) cert5.2 cert5.1 f spec
    omega
  · have bound := from_certificate 6 14 w6 121 (by decide) cert6.2 cert6.1 f spec
    omega
  · have bound := from_certificate 7 15 w7 120 (by decide) cert7.2 cert7.1 f spec
    omega
  · have bound := from_certificate 8 14 w8 121 (by decide) cert8.2 cert8.1 f spec
    omega
  · have bound := from_certificate 9 14 w9 121 (by decide) cert9.2 cert9.1 f spec
    omega

end PetersenNegated3971
