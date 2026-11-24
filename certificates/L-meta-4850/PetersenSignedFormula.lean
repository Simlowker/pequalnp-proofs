import Mathlib.Tactic
import Mathlib.Data.Nat.Bitwise
import PEqualNP.Defs

-- A signed formula for the Petersen edge predicate with two free input signals
-- needs at least fourteen literal leaves. The same circuit with no internal NOT
-- needs at least sixteen leaves when unfolded. The final theorem separately
-- specializes the earlier six-pair result to the exact posted circuit statement.
--
-- Each original vertex input must occur. For adjacent inputs, six test rows
-- make their joint restriction act as AND in one context and OR in another.
-- If both inputs occur once, the same binary formula cannot realize both.
-- Without the auxiliary OR, repeated inputs therefore cover every edge.
-- A cover of the Petersen graph minus a vertex has at least five vertices.
-- With the auxiliary present, the seven edges away from vertices 1 and 2
-- still need a cover. Its only three-vertex cover is 4, 5, 8. A separate
-- seven-row test forces at least one of 0, 1, 2 to repeat, even with the
-- auxiliary present. WindowCuts and signed_leaf_bound check these claims.
namespace PetersenRows3616

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
  | var (i : Fin 12)
  | disj (l r : Formula)
  | conj (l r : Formula)

def Formula.eval (v : Fin 12 → Bool) : Formula → Bool
  | .var i => v i
  | .disj l r => l.eval v || r.eval v
  | .conj l r => l.eval v && r.eval v

def Formula.cost (c : Fin 12 → Int) : Formula → Int
  | .var i => c i
  | .disj l r | .conj l r => l.cost c + r.cost c

theorem variable_filter {xs ys : List Nat} (h : xs.Sublist ys) (p : Nat → Bool)
    (yes : ∀ i ∈ xs, p i = true) : xs.Sublist (ys.filter p) := by
  have hh := h.filter p
  rwa [List.filter_eq_self.mpr yes] at hh

theorem formula_bound (w : Matrix) (rows cols : List Nat) (yes no : Nat → Fin 12 → Bool)
    (cost : Fin 12 → Int)
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



def positive : List Nat := [3, 6, 12, 13, 17, 24, 33, 66, 132, 133, 160, 264, 265, 288, 320, 321]
def negative : List Nat := [42, 50, 69, 104, 116, 138, 200, 201, 208, 261, 276, 385, 402]

def literal (mask : Nat) (v : Fin 12) : Bool :=
  if v.val<9 then mask.testBit v.val else if v.val=9 then !mask.testBit 0 else decide (v.val=11)
def Formula.leaves : Formula → Nat
  | .var _ => 1
  | .conj l r | .disj l r => l.leaves + r.leaves

theorem uniform_cost (f : Formula) (d : Int) :
    f.cost (fun _ => d) = (f.leaves : Int) * d := by
  induction f with
  | var i => simp [Formula.leaves,Formula.cost]
  | conj l r il ir => simp [Formula.leaves,Formula.cost,il,ir,add_mul]
  | disj l r il ir => simp [Formula.leaves,Formula.cost,il,ir,add_mul]

def ri := List.range 16
def ci := List.range 13
def yes i := literal (positive.getD i 0)
def no j := literal (negative.getD j 0)
def fromData (data : List (List Int)) : Matrix := fun i j => (data.getD i []).getD j 0
def valid (mat : Matrix) (d : Int) (v : Fin 12) : Bool :=
  let rs := ri.filter fun i => yes i v
  let cs := ci.filter fun j => !(no j v)
  if cs.isEmpty then true else rs.sublists.all fun rr => decide (upper mat rr cs ≤ d)
def weights : Matrix := fromData [[28, 0, 0, 0, -32, 4, 0, 23, 0, 29, -13, 8, 28], [29, 6, 0, -6, 18, 0, -9, -23, 0, 29, 13, -6, 25], [29, -6, 2, 6, 17, 0, 3, 2, 0, 0, 6, 0, -23], [0, 0, 15, 0, 0, 0, 0, 20, 0, 26, -6, -5, -15], [-28, 0, 2, 0, 15, -4, 0, 0, 1, 58, 27, 0, 17], [56, 6, -2, 0, 28, 4, 0, 0, 0, -26, 0, 0, 26], [28, 0, 8, 0, 32, 0, 0, 25, -1, 25, -14, 2, -28], [60, 0, 0, 6, 29, 0, 9, 16, 0, -29, 0, -2, 0], [-29, 0, 0, 0, 0, 0, 9, 16, 0, 0, 31, 4, 26], [0, 0, 4, 0, 0, 0, -3, 3, 0, 25, 0, 5, 0], [60, 0, -4, 0, 0, 4, 11, 16, 1, -25, -2, -2, 28], [29, -6, 0, 0, -23, 4, 2, 5, 0, 6, 6, 0, 23], [0, 0, -15, 0, -5, 0, 0, 20, 0, 20, 0, 5, 0], [29, 6, -4, 0, 25, -4, -11, -25, 0, 25, 16, 2, 17], [-18, 0, 2, 0, 16, 0, 11, 5, 0, 0, 18, 0, 0], [-11, 0, 15, 0, 0, 0, -2, 13, 0, 40, 0, 2, 0]]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
theorem check_weight : ∀ v, valid weights 60 v = true := by decide +kernel

def Fits (f : Formula) := (∀ r ∈ positive, f.eval (literal r) = true) ∧
  (∀ r ∈ negative, f.eval (literal r) = false)

theorem literal_bound (f : Formula) (hf : Fits f) : 17 ≤ f.leaves := by
  have hpos : ∀ i ∈ ri, positive.getD i 0 ∈ positive := by decide +kernel
  have hneg : ∀ i ∈ ci, negative.getD i 0 ∈ negative := by decide +kernel
  have bound := formula_bound weights ri ci yes no (fun _ => 60) (by
    intro v rr hrr
    have h := check_weight v
    dsimp only [valid] at h
    split at h
    · rename_i he
      have eq := List.isEmpty_iff.mp he
      simp [eq, upper]
    · exact decide_eq_true_iff.mp ((List.all_eq_true.mp h) rr (List.mem_sublists.mpr hrr)))
    f (List.Sublist.refl ri) (List.Sublist.refl ci)
    (fun i hi => hf.1 _ (hpos i hi)) (fun i hi => hf.2 _ (hneg i hi))
  have total : rect weights ri ci = 984 := by decide +kernel
  rw [total,uniform_cost] at bound
  omega

def witness : Formula := (.disj (.disj (.disj (.disj (.conj (.var 0) (.disj (.var 1) (.var 4))) (.conj (.disj (.var 1) (.var 7)) (.var 2))) (.conj (.disj (.disj (.var 2) (.var 4)) (.var 8)) (.var 3))) (.conj (.disj (.disj (.var 0) (.var 7)) (.var 8)) (.var 5))) (.conj (.disj (.var 1) (.var 8)) (.var 6)))
theorem witness_spec : Fits witness ∧ witness.leaves=17 := by
  unfold Fits
  decide +kernel

end PetersenRows3616

namespace PetersenAux3616

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



def positive : List Nat := [3, 6, 12, 13, 17, 24, 33, 66, 132, 133, 160, 264, 265, 288, 320, 321]
def negative : List Nat := [42, 50, 69, 104, 116, 138, 200, 201, 208, 261, 276, 385, 402]

def literal (mask : Nat) (v : Fin 13) : Bool :=
  if v.val<9 then mask.testBit v.val else if v.val=9 then !mask.testBit 0 else decide (v.val=11)
def Formula.leaves : Formula → Nat
  | .var _ => 1
  | .conj l r | .disj l r => l.leaves + r.leaves

theorem uniform_cost (f : Formula) (d : Int) :
    f.cost (fun _ => d) = (f.leaves : Int) * d := by
  induction f with
  | var i => simp [Formula.leaves,Formula.cost]
  | conj l r il ir => simp [Formula.leaves,Formula.cost,il,ir,add_mul]
  | disj l r il ir => simp [Formula.leaves,Formula.cost,il,ir,add_mul]

def ri := List.range 16
def ci := List.range 13
def yes i := literal (positive.getD i 0)
def no j := literal (negative.getD j 0)
def fromData (data : List (List Int)) : Matrix := fun i j => (data.getD i []).getD j 0
def valid (mat : Matrix) (d : Int) (v : Fin 13) : Bool :=
  let rs := ri.filter fun i => yes i v
  let cs := ci.filter fun j => !(no j v)
  if cs.isEmpty then true else rs.sublists.all fun rr => decide (upper mat rr cs ≤ d)


def withGate (u v : Nat) (o : Bool) (r : Nat) (i : Fin 13) : Bool :=
  if i.val=12 then
    let a := literal r (Fin.ofNat 13 u)
    let b := literal r (Fin.ofNat 13 v)
    if o then a || b else a && b
  else literal r i

def cost1 (d : Int) (i : Fin 13) : Int := if i.val=12 then 0 else d
def ordinary : Formula → Nat
  | .var i => if i.val=12 then 0 else 1
  | .conj a b | .disj a b => ordinary a + ordinary b

theorem ordinary_cost (f : Formula) (d : Int) :
    f.cost (cost1 d) = (ordinary f : Int)*d := by
  induction f with
  | var i => by_cases h : i.val=12 <;> simp [Formula.cost,cost1,ordinary,h]
  | conj a b ia ib => simp [Formula.cost,ordinary,ia,ib,add_mul]
  | disj a b ia ib => simp [Formula.cost,ordinary,ia,ib,add_mul]

def Good (u v : Nat) (o : Bool) (d : Int) (mat : Matrix) : Bool :=
  (List.finRange 13).all fun i =>
    let rs := ri.filter fun j => withGate u v o (positive.getD j 0) i
    let cs := ci.filter fun j => !(withGate u v o (negative.getD j 0) i)
    if cs.isEmpty then true else
    if i.val=12 then rs.all (fun x => cs.all fun y => decide (mat x y ≤ 0))
    else rs.sublists.all fun rr => decide (upper mat rr cs ≤ d)

theorem upperZero (m : Matrix) (rr cs : List Nat)
    (nonpos : ∀ x ∈ rr, ∀ y ∈ cs, m x y ≤ 0) : upper m rr cs = 0 := by
  have cn (rows : List Nat) (j : Nat) (h : ∀ x ∈ rows, m x j ≤ 0) : col m rows j ≤ 0 := by
    induction rows with
    | nil => simp [col]
    | cons a xs ih =>
      have h1 := h a List.mem_cons_self
      have h2 := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
      simp only [col,List.map_cons,List.sum_cons] at *
      omega
  induction cs with
  | nil => simp [upper]
  | cons j js ih =>
    have h1 := cn rr j (fun x hx => nonpos x hx j List.mem_cons_self)
    have h2 := ih (fun x hx y hy => nonpos x hx y (List.mem_cons_of_mem j hy))
    simp only [upper,List.map_cons,List.sum_cons,max_eq_left h1] at *
    omega

def FitsAux (u v : Nat) (o : Bool) (f : Formula) :=
  (∀ r ∈ positive, f.eval (withGate u v o r) = true) ∧
  (∀ r ∈ negative, f.eval (withGate u v o r) = false)

theorem via (u v : Nat) (o : Bool) (d : Int) (mat : Matrix)
    (dpos : 0<d) (total : 13*d < rect mat ri ci) (good : Good u v o d mat=true)
    (f : Formula) (hf : FitsAux u v o f) : 14 ≤ ordinary f := by
  have hpos : ∀ i ∈ ri, positive.getD i 0 ∈ positive := by decide +kernel
  have hneg : ∀ i ∈ ci, negative.getD i 0 ∈ negative := by decide +kernel
  have bound := formula_bound mat ri ci
    (fun i => withGate u v o (positive.getD i 0)) (fun j => withGate u v o (negative.getD j 0))
    (cost1 d) (by
      intro i rr hrr
      have h := List.all_eq_true.mp good i (List.mem_finRange i)
      dsimp only at h
      split at h
      · rename_i empty; rw [List.isEmpty_iff.mp empty]
        simp [upper,cost1]; split <;> omega
      · split at h
        · rename_i eq
          rw [upperZero mat rr _ (fun x hx y hy => decide_eq_true_iff.mp
            (List.all_eq_true.mp (List.all_eq_true.mp h x (hrr.subset hx)) y hy))]
          simp [cost1,eq]
        · rename_i ne
          simp only [cost1,ite_eq_right ne]
          exact decide_eq_true_iff.mp (List.all_eq_true.mp h rr (List.mem_sublists.mpr hrr)))
    f (List.Sublist.refl ri) (List.Sublist.refl ci)
    (fun i hi => hf.1 _ (hpos i hi)) (fun i hi => hf.2 _ (hneg i hi))
  rw [ordinary_cost] at bound
  by_contra! bad
  have le : (ordinary f : Int) ≤ 13 := by omega
  have := mul_le_mul_of_nonneg_right le (le_of_lt dpos)
  omega

end PetersenAux3616

namespace PetersenAux3616
def w17 : Matrix := fromData [[1574, 0, 1098, 0, -2658, 426, 0, 0, 0, 2070, 0, 0, 1168], [1584, 1553, -1098, 0, 1098, -1584, 0, 0, 0, 588, 510, 0, 31], [1584, -1553, 318, 0, 1543, 1533, 0, 0, 0, 518, 369, 0, -1533], [0, 0, 369, 0, 0, 51, 0, 0, 0, 420, -369, 0, -51], [-1594, 0, 318, 0, 1594, 0, 0, 1594, 0, 1256, 0, 0, 1574], [3168, 1553, -318, 0, 1256, 0, 0, 0, 0, -1256, 0, 0, 359], [1594, 0, 409, 0, 1574, -477, 0, 1039, 0, 1510, 0, 105, -1658], [1560, 0, 1098, 0, 2070, 0, 0, 0, 0, -1098, -510, 0, 1608], [-1615, 0, 0, 0, 1615, 1584, 0, 0, 0, 0, 0, 0, 1584], [0, 0, 43, 0, 0, 0, 0, 0, 0, 1510, 0, 0, 0], [1615, 0, -43, 1553, 0, 998, 617, 520, 0, -1510, 0, 0, 1033], [1560, -656, 318, 0, -1239, 538, 48, 335, 0, 552, 369, 0, 1526], [0, 0, -687, 0, -17, -17, 0, 704, 0, 704, 0, 0, 17], [1560, 656, -366, 0, 952, -521, -617, -1039, 0, 1510, 0, 0, 1658], [-1239, 0, 318, 0, 1239, 0, 617, 304, 0, 0, 510, 0, 1239], [-321, 0, 369, 0, 0, 0, -48, 369, 0, 1098, 0, 1560, -1239]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem case17 (f : Formula) (hf : FitsAux 1 2 true f) : 14 ≤ ordinary f :=
  via 1 2 true 3168 w17 (by decide) (by decide +kernel) (by decide +kernel) f hf
end PetersenAux3616

namespace Petersen4850
open PetersenAux3616

def expand : Formula → PetersenRows3616.Formula
  | .var i => if h : i.val < 12 then .var ⟨i.val,h⟩ else .disj (.var 1) (.var 2)
  | .conj a b => .conj (expand a) (expand b)
  | .disj a b => .disj (expand a) (expand b)

theorem expand_size (f : Formula) :
    (expand f).leaves + ordinary f = 2 * f.leaves := by
  induction f with
  | var i => fin_cases i <;> rfl
  | conj a b ih jh | disj a b ih jh =>
    simp only [expand, PetersenRows3616.Formula.leaves, ordinary, Formula.leaves]
    omega

theorem expand_eval (f : Formula) (row : Nat) :
    (expand f).eval (PetersenRows3616.literal row) =
    f.eval (withGate 1 2 true row) := by
  induction f with
  | var i => fin_cases i <;> rfl
  | conj a b ih jh | disj a b ih jh =>
    simp only [expand, PetersenRows3616.Formula.eval, Formula.eval, ih, jh]

theorem leaves_needed (f : Formula) (hf : FitsAux 1 2 true f) : 16 ≤ f.leaves := by
  have h1 := case17 f hf
  have good : PetersenRows3616.Fits (expand f) := by
    constructor
    · intro r hr
      exact (expand_eval f r).trans (hf.1 r hr)
    · intro r hr
      exact (expand_eval f r).trans (hf.2 r hr)
  have h2 := PetersenRows3616.literal_bound _ good
  have h3 := expand_size f
  omega

end Petersen4850

namespace SignedPetersen

inductive Expr where
  | lit (i : Fin 10) (neg : Bool)
  | fixed (b : Bool)
  | both (a b : Expr)
  | either (a b : Expr)

def value (r : Nat) (i : Fin 10) : Bool :=
  if i.val=9 then r.testBit 1 || r.testBit 2 else r.testBit i.val

def Expr.eval (r : Nat) : Expr → Bool
  | .lit i s => Bool.xor (value r i) s
  | .fixed b => b
  | .both a b => a.eval r && b.eval r
  | .either a b => a.eval r || b.eval r

def Expr.count (i : Nat) : Expr → Nat
  | .fixed _ => 0
  | .lit j _ => if j.val=i then 1 else 0
  | .both a b | .either a b => a.count i + b.count i

def Expr.leaves : Expr → Nat
  | .fixed _ => 0
  | .lit _ _ => 1
  | .both a b | .either a b => a.leaves+b.leaves

theorem agree (e : Expr) (a b : Nat) (h : ∀ i : Fin 10, 0<e.count i → value a i=value b i) :
    e.eval a=e.eval b := by
  induction e with
  | fixed _ => rfl
  | lit i s => simp only [Expr.eval]; rw [h i (by simp [Expr.count])]
  | both x y ih jh | either x y ih jh =>
    have hx (i : Fin 10) (z : 0<x.count i) := h i (by dsimp [Expr.count]; omega)
    have hy (i : Fin 10) (z : 0<y.count i) := h i (by dsimp [Expr.count]; omega)
    simp only [Expr.eval,ih hx,jh hy]

def pack (rs : List Nat) (p : Nat → Bool) : Nat :=
  rs.foldr (fun i a => Nat.bit (p i) a) 0

theorem pack_and (rs : List Nat) (p q : Nat → Bool) :
    pack rs (fun i => p i && q i) = pack rs p &&& pack rs q := by
  induction rs with
  | nil => simp [pack]
  | cons x xs ih => simp [pack,List.foldr_cons,Nat.land_bit] at ih ⊢; rw [ih]

theorem pack_or (rs : List Nat) (p q : Nat → Bool) :
    pack rs (fun i => p i || q i) = pack rs p ||| pack rs q := by
  induction rs with
  | nil => simp [pack]
  | cons x xs ih => simp [pack,List.foldr_cons,Nat.lor_bit] at ih ⊢; rw [ih]

structure Cut where
  rows : List Nat
  x : Nat
  y : Nat
  z : Nat

def grade (d : Cut) (e : Expr) := e.count d.x + 2*e.count d.y + 4*e.count d.z

def joinValid (lib : Nat → List Nat) :=
  ∀ a b c d e f : Fin 2, a.val+d.val≤1 → b.val+e.val≤1 → c.val+f.val≤1 →
    ∀ w∈lib (a.val+2*b.val+4*c.val), ∀ v∈lib (d.val+2*e.val+4*f.val),
      w &&& v ∈ lib (a.val+d.val+2*(b.val+e.val)+4*(c.val+f.val)) ∧
      w ||| v ∈ lib (a.val+d.val+2*(b.val+e.val)+4*(c.val+f.val))

def leafValid (lib : Nat → List Nat) (d : Cut) (forbid : Bool) :=
  (∀ b : Bool, pack d.rows (fun _ => b) ∈ lib 0) ∧
  ∀ i : Fin 10, ∀ s : Bool, (forbid=true → i.val≠9) →
      pack d.rows (fun r => (Expr.lit i s).eval r) ∈ lib (grade d (.lit i s))

theorem grade_bound (lib : Nat → List Nat) (d : Cut) (forbid : Bool)
    (hj : joinValid lib) (hl : leafValid lib d forbid) (e : Expr)
    (hf : forbid=true → e.count 9=0)
    (hx : e.count d.x≤1) (hy : e.count d.y≤1) (hz : e.count d.z≤1) :
    pack d.rows (fun r => e.eval r) ∈ lib (grade d e) := by
  induction e with
  | fixed b => exact hl.1 b
  | lit i s =>
    apply hl.2 i s
    intro forb h
    have := hf forb
    simp [Expr.count,h] at this
  | both l r ih jh | either l r ih jh =>
    simp only [Expr.count] at hf hx hy hz
    have left := ih (fun h => by have := hf h; omega) (by omega) (by omega) (by omega)
    have right := jh (fun h => by have := hf h; omega) (by omega) (by omega) (by omega)
    have comp := hj ⟨l.count d.x,by omega⟩ ⟨l.count d.y,by omega⟩ ⟨l.count d.z,by omega⟩
      ⟨r.count d.x,by omega⟩ ⟨r.count d.y,by omega⟩ ⟨r.count d.z,by omega⟩ hx hy hz _ left _ right
    first
    | exact (pack_and d.rows (fun t => l.eval t) (fun t => r.eval t)) ▸ comp.1
    | exact (pack_or d.rows (fun t => l.eval t) (fun t => r.eval t)) ▸ comp.2

def edges : List (Nat × Nat) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
def target (r : Nat) := edges.any (fun (a,b) => r.testBit a && r.testBit b)
def Fits (e : Expr) := ∀ r : Nat, e.eval r = target r

theorem cut_rule (lib : Nat → List Nat) (d : Cut) (forbid : Bool)
    (hj : joinValid lib) (hl : leafValid lib d forbid) (e : Expr) (fits : Fits e)
    (hf : forbid=true → e.count 9=0) (bad : ∀ a b c : Fin 2,
      pack d.rows target ∉ lib (a.val+2*b.val+4*c.val)) :
    2≤e.count d.x ∨ 2≤e.count d.y ∨ 2≤e.count d.z := by
  by_contra! h
  have m := grade_bound lib d forbid hj hl e hf (by omega) (by omega) (by omega)
  have same : (fun r => e.eval r)=target := funext fits
  rw [same] at m
  exact bad ⟨e.count d.x,by omega⟩ ⟨e.count d.y,by omega⟩ ⟨e.count d.z,by omega⟩ m
end SignedPetersen

namespace SignedPetersen
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def pairLib : Nat → List Nat
  | 0 => [0, 7, 56, 63]
  | 1 => [0, 2, 5, 7, 16, 21, 23, 40, 42, 47, 56, 58, 61, 63]
  | 2 => [0, 1, 6, 7, 24, 25, 31, 32, 38, 39, 56, 57, 62, 63]
  | 3 => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 16, 17, 20, 21, 22, 23, 24, 25, 26, 27, 29, 31, 32, 34, 36, 37, 38, 39, 40, 41, 42, 43, 46, 47, 48, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
  | 4 => [0, 7, 56, 63]
  | 5 => [0, 2, 5, 7, 16, 21, 23, 40, 42, 47, 56, 58, 61, 63]
  | 6 => [0, 1, 6, 7, 24, 25, 31, 32, 38, 39, 56, 57, 62, 63]
  | 7 => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 16, 17, 20, 21, 22, 23, 24, 25, 26, 27, 29, 31, 32, 34, 36, 37, 38, 39, 40, 41, 42, 43, 46, 47, 48, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
  | _ => []
theorem pairJoin : joinValid pairLib := by unfold joinValid; decide +kernel
def cut0_1_10 : Cut := ⟨[1, 2, 3, 20, 21, 22],0,1,10⟩
theorem cut0_1_10_bound (e : Expr) (fit : Fits e) (noAux : e.count 9=0) : 2≤e.count 0 ∨ 2≤e.count 1 := by
  have h := cut_rule pairLib cut0_1_10 true pairJoin (by unfold leafValid; decide +kernel) e fit (fun _ => noAux) (by decide +kernel)
  have zero : e.count 10=0 := by
    clear h fit
    clear noAux
    induction e with
    | fixed _ => rfl
    | lit i _ => have := i.isLt; simp [Expr.count,show i.val≠10 by omega]
    | both a b ih jh | either a b ih jh => simp [Expr.count,ih,jh]
  change 2≤e.count 0 ∨ 2≤e.count 1 ∨ 2≤e.count 10 at h
  omega
def cut1_2_10 : Cut := ⟨[2, 4, 6, 9, 11, 13],1,2,10⟩
theorem cut1_2_10_bound (e : Expr) (fit : Fits e) (noAux : e.count 9=0) : 2≤e.count 1 ∨ 2≤e.count 2 := by
  have h := cut_rule pairLib cut1_2_10 true pairJoin (by unfold leafValid; decide +kernel) e fit (fun _ => noAux) (by decide +kernel)
  have zero : e.count 10=0 := by
    clear h fit
    clear noAux
    induction e with
    | fixed _ => rfl
    | lit i _ => have := i.isLt; simp [Expr.count,show i.val≠10 by omega]
    | both a b ih jh | either a b ih jh => simp [Expr.count,ih,jh]
  change 2≤e.count 1 ∨ 2≤e.count 2 ∨ 2≤e.count 10 at h
  omega
def cut2_3_10 : Cut := ⟨[4, 8, 12, 18, 22, 26],2,3,10⟩
theorem cut2_3_10_bound (e : Expr) (fit : Fits e) (noAux : e.count 9=0) : 2≤e.count 2 ∨ 2≤e.count 3 := by
  have h := cut_rule pairLib cut2_3_10 true pairJoin (by unfold leafValid; decide +kernel) e fit (fun _ => noAux) (by decide +kernel)
  have zero : e.count 10=0 := by
    clear h fit
    clear noAux
    induction e with
    | fixed _ => rfl
    | lit i _ => have := i.isLt; simp [Expr.count,show i.val≠10 by omega]
    | both a b ih jh | either a b ih jh => simp [Expr.count,ih,jh]
  change 2≤e.count 2 ∨ 2≤e.count 3 ∨ 2≤e.count 10 at h
  omega
def cut3_4_10 : Cut := ⟨[8, 16, 24, 5, 13, 21],3,4,10⟩
theorem cut3_4_10_bound (e : Expr) (fit : Fits e)  : 2≤e.count 3 ∨ 2≤e.count 4 := by
  have h := cut_rule pairLib cut3_4_10 false pairJoin (by unfold leafValid; decide +kernel) e fit (by simp) (by decide +kernel)
  have zero : e.count 10=0 := by
    clear h fit
    induction e with
    | fixed _ => rfl
    | lit i _ => have := i.isLt; simp [Expr.count,show i.val≠10 by omega]
    | both a b ih jh | either a b ih jh => simp [Expr.count,ih,jh]
  change 2≤e.count 3 ∨ 2≤e.count 4 ∨ 2≤e.count 10 at h
  omega
def cut4_0_10 : Cut := ⟨[16, 1, 17, 10, 26, 11],4,0,10⟩
theorem cut4_0_10_bound (e : Expr) (fit : Fits e)  : 2≤e.count 4 ∨ 2≤e.count 0 := by
  have h := cut_rule pairLib cut4_0_10 false pairJoin (by unfold leafValid; decide +kernel) e fit (by simp) (by decide +kernel)
  have zero : e.count 10=0 := by
    clear h fit
    induction e with
    | fixed _ => rfl
    | lit i _ => have := i.isLt; simp [Expr.count,show i.val≠10 by omega]
    | both a b ih jh | either a b ih jh => simp [Expr.count,ih,jh]
  change 2≤e.count 4 ∨ 2≤e.count 0 ∨ 2≤e.count 10 at h
  omega
def cut0_5_10 : Cut := ⟨[1, 32, 33, 130, 131, 162],0,5,10⟩
theorem cut0_5_10_bound (e : Expr) (fit : Fits e)  : 2≤e.count 0 ∨ 2≤e.count 5 := by
  have h := cut_rule pairLib cut0_5_10 false pairJoin (by unfold leafValid; decide +kernel) e fit (by simp) (by decide +kernel)
  have zero : e.count 10=0 := by
    clear h fit
    induction e with
    | fixed _ => rfl
    | lit i _ => have := i.isLt; simp [Expr.count,show i.val≠10 by omega]
    | both a b ih jh | either a b ih jh => simp [Expr.count,ih,jh]
  change 2≤e.count 0 ∨ 2≤e.count 5 ∨ 2≤e.count 10 at h
  omega
def cut1_6_10 : Cut := ⟨[2, 64, 66, 257, 259, 321],1,6,10⟩
theorem cut1_6_10_bound (e : Expr) (fit : Fits e) (noAux : e.count 9=0) : 2≤e.count 1 ∨ 2≤e.count 6 := by
  have h := cut_rule pairLib cut1_6_10 true pairJoin (by unfold leafValid; decide +kernel) e fit (fun _ => noAux) (by decide +kernel)
  have zero : e.count 10=0 := by
    clear h fit
    clear noAux
    induction e with
    | fixed _ => rfl
    | lit i _ => have := i.isLt; simp [Expr.count,show i.val≠10 by omega]
    | both a b ih jh | either a b ih jh => simp [Expr.count,ih,jh]
  change 2≤e.count 1 ∨ 2≤e.count 6 ∨ 2≤e.count 10 at h
  omega
def cut2_7_10 : Cut := ⟨[4, 128, 132, 34, 38, 162],2,7,10⟩
theorem cut2_7_10_bound (e : Expr) (fit : Fits e) (noAux : e.count 9=0) : 2≤e.count 2 ∨ 2≤e.count 7 := by
  have h := cut_rule pairLib cut2_7_10 true pairJoin (by unfold leafValid; decide +kernel) e fit (fun _ => noAux) (by decide +kernel)
  have zero : e.count 10=0 := by
    clear h fit
    clear noAux
    induction e with
    | fixed _ => rfl
    | lit i _ => have := i.isLt; simp [Expr.count,show i.val≠10 by omega]
    | both a b ih jh | either a b ih jh => simp [Expr.count,ih,jh]
  change 2≤e.count 2 ∨ 2≤e.count 7 ∨ 2≤e.count 10 at h
  omega
def cut3_8_10 : Cut := ⟨[8, 256, 264, 36, 44, 292],3,8,10⟩
theorem cut3_8_10_bound (e : Expr) (fit : Fits e)  : 2≤e.count 3 ∨ 2≤e.count 8 := by
  have h := cut_rule pairLib cut3_8_10 false pairJoin (by unfold leafValid; decide +kernel) e fit (by simp) (by decide +kernel)
  have zero : e.count 10=0 := by
    clear h fit
    induction e with
    | fixed _ => rfl
    | lit i _ => have := i.isLt; simp [Expr.count,show i.val≠10 by omega]
    | both a b ih jh | either a b ih jh => simp [Expr.count,ih,jh]
  change 2≤e.count 3 ∨ 2≤e.count 8 ∨ 2≤e.count 10 at h
  omega
def cut5_7_10 : Cut := ⟨[32, 128, 160, 5, 37, 133],5,7,10⟩
theorem cut5_7_10_bound (e : Expr) (fit : Fits e)  : 2≤e.count 5 ∨ 2≤e.count 7 := by
  have h := cut_rule pairLib cut5_7_10 false pairJoin (by unfold leafValid; decide +kernel) e fit (by simp) (by decide +kernel)
  have zero : e.count 10=0 := by
    clear h fit
    induction e with
    | fixed _ => rfl
    | lit i _ => have := i.isLt; simp [Expr.count,show i.val≠10 by omega]
    | both a b ih jh | either a b ih jh => simp [Expr.count,ih,jh]
  change 2≤e.count 5 ∨ 2≤e.count 7 ∨ 2≤e.count 10 at h
  omega
def cut6_8_10 : Cut := ⟨[64, 256, 320, 10, 74, 266],6,8,10⟩
theorem cut6_8_10_bound (e : Expr) (fit : Fits e)  : 2≤e.count 6 ∨ 2≤e.count 8 := by
  have h := cut_rule pairLib cut6_8_10 false pairJoin (by unfold leafValid; decide +kernel) e fit (by simp) (by decide +kernel)
  have zero : e.count 10=0 := by
    clear h fit
    induction e with
    | fixed _ => rfl
    | lit i _ => have := i.isLt; simp [Expr.count,show i.val≠10 by omega]
    | both a b ih jh | either a b ih jh => simp [Expr.count,ih,jh]
  change 2≤e.count 6 ∨ 2≤e.count 8 ∨ 2≤e.count 10 at h
  omega
def cut8_5_10 : Cut := ⟨[256, 32, 288, 9, 265, 41],8,5,10⟩
theorem cut8_5_10_bound (e : Expr) (fit : Fits e)  : 2≤e.count 8 ∨ 2≤e.count 5 := by
  have h := cut_rule pairLib cut8_5_10 false pairJoin (by unfold leafValid; decide +kernel) e fit (by simp) (by decide +kernel)
  have zero : e.count 10=0 := by
    clear h fit
    induction e with
    | fixed _ => rfl
    | lit i _ => have := i.isLt; simp [Expr.count,show i.val≠10 by omega]
    | both a b ih jh | either a b ih jh => simp [Expr.count,ih,jh]
  change 2≤e.count 8 ∨ 2≤e.count 5 ∨ 2≤e.count 10 at h
  omega
def tripleLib : Nat → List Nat
  | 0 => [0, 15, 112, 127]
  | 1 => [0, 1, 14, 15, 32, 46, 47, 80, 81, 95, 112, 113, 126, 127]
  | 2 => [0, 4, 11, 15, 48, 52, 63, 64, 75, 79, 112, 116, 123, 127]
  | 3 => [0, 1, 4, 5, 10, 11, 14, 15, 16, 17, 20, 31, 32, 36, 42, 43, 46, 47, 48, 49, 52, 53, 62, 63, 64, 65, 74, 75, 78, 79, 80, 81, 84, 85, 91, 95, 96, 107, 110, 111, 112, 113, 116, 117, 122, 123, 126, 127]
  | 4 => [0, 3, 12, 15, 112, 115, 124, 127]
  | 5 => [0, 1, 2, 3, 12, 13, 14, 15, 32, 34, 35, 44, 46, 47, 80, 81, 83, 92, 93, 95, 112, 113, 114, 115, 124, 125, 126, 127]
  | 6 => [0, 3, 4, 7, 8, 11, 12, 15, 48, 51, 52, 55, 60, 63, 64, 67, 72, 75, 76, 79, 112, 115, 116, 119, 120, 123, 124, 127]
  | 7 => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 23, 28, 29, 31, 32, 34, 35, 36, 38, 39, 40, 42, 43, 44, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 60, 61, 62, 63, 64, 65, 66, 67, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 83, 84, 85, 87, 88, 89, 91, 92, 93, 95, 96, 98, 99, 104, 107, 108, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]
  | _ => []
theorem tripleJoin : joinValid tripleLib := by unfold joinValid; decide +kernel
def cut0_1_2 : Cut := ⟨[2, 3, 5, 7, 20, 21, 22],0,1,2⟩
theorem cut0_1_2_bound (e : Expr) (fit : Fits e)  : 2≤e.count 0 ∨ 2≤e.count 1 ∨ 2≤e.count 2 := by
  have h := cut_rule tripleLib cut0_1_2 false tripleJoin (by unfold leafValid; decide +kernel) e fit (by simp) (by decide +kernel)
  exact h
end SignedPetersen

namespace SignedPetersen
theorem raw_required (e : Expr) (fit : Fits e) (j : Fin 9) : 1≤e.count j := by
  have test : ∀ k : Fin 9, ∃ p : Fin 512, target p.val ≠ target (p.val ||| (1 <<< k.val)) ∧
      ∀ i : Fin 10, i.val ≠ k.val → value p.val i = value (p.val ||| (1 <<< k.val)) i := by
    intro k
    let rows : List Nat := [2, 4, 2, 4, 1, 1, 2, 4, 8]
    refine ⟨⟨rows.getD k.val 0,?_⟩,?_⟩
    · revert k; decide +kernel
    · revert k; decide +kernel
  obtain ⟨p,h,others⟩ := test j
  by_contra! miss
  apply h
  rw [←fit p.val,←fit (p.val ||| (1 <<< j.val))]
  apply agree
  intro i hi
  apply others i
  intro same
  rw [same] at hi
  omega
theorem total_leaves (e : Expr) : e.count 0 + e.count 1 + e.count 2 + e.count 3 + e.count 4 + e.count 5 + e.count 6 + e.count 7 + e.count 8 + e.count 9 = e.leaves := by
  induction e with
  | fixed _ => rfl
  | lit i _ => fin_cases i <;> rfl
  | both x y ih jh | either x y ih jh => simp only [Expr.count,Expr.leaves]; omega
set_option maxHeartbeats 3000000 in
theorem signed_leaf_bound (e : Expr) (fit : Fits e) : 14≤e.leaves := by
  have total := total_leaves e
  have pos0 := raw_required e fit (0 : Fin 9)
  change 1≤e.count 0 at pos0
  have pos1 := raw_required e fit (1 : Fin 9)
  change 1≤e.count 1 at pos1
  have pos2 := raw_required e fit (2 : Fin 9)
  change 1≤e.count 2 at pos2
  have pos3 := raw_required e fit (3 : Fin 9)
  change 1≤e.count 3 at pos3
  have pos4 := raw_required e fit (4 : Fin 9)
  change 1≤e.count 4 at pos4
  have pos5 := raw_required e fit (5 : Fin 9)
  change 1≤e.count 5 at pos5
  have pos6 := raw_required e fit (6 : Fin 9)
  change 1≤e.count 6 at pos6
  have pos7 := raw_required e fit (7 : Fin 9)
  change 1≤e.count 7 at pos7
  have pos8 := raw_required e fit (8 : Fin 9)
  change 1≤e.count 8 at pos8
  have e34 := cut3_4_10_bound e fit
  have e40 := cut4_0_10_bound e fit
  have e05 := cut0_5_10_bound e fit
  have e38 := cut3_8_10_bound e fit
  have e57 := cut5_7_10_bound e fit
  have e68 := cut6_8_10_bound e fit
  have e85 := cut8_5_10_bound e fit
  have triple := cut0_1_2_bound e fit
  by_cases zero : e.count 9=0
  ·
    have e01 := cut0_1_10_bound e fit zero
    have e12 := cut1_2_10_bound e fit zero
    have e23 := cut2_3_10_bound e fit zero
    have e16 := cut1_6_10_bound e fit zero
    have e27 := cut2_7_10_bound e fit zero
    omega
  · omega
end SignedPetersen

namespace SignedPetersen

inductive Tree where
  | atom (i : Fin 13)
  | both (x y : Tree)
  | either (x y : Tree)
  | flip (x : Tree)

def leafValue (r : Nat) (i : Fin 13) := PetersenAux3616.withGate 1 2 true r i

def Tree.eval (r : Nat) : Tree → Bool
  | .atom i => leafValue r i
  | .both a b => a.eval r && b.eval r
  | .either a b => a.eval r || b.eval r
  | .flip a => !a.eval r

def signedLeaf (i : Fin 13) (s : Bool) : Expr :=
  if h : i.val<9 then .lit ⟨i.val,by omega⟩ s else
  if i.val=9 then .lit 0 (!s) else
  if i.val=10 then .fixed s else if i.val=11 then .fixed (!s) else .lit 9 s

def normal (s : Bool) : Tree → Expr
  | .atom i => signedLeaf i s
  | .both a b => if s then .either (normal s a) (normal s b) else .both (normal s a) (normal s b)
  | .either a b => if s then .both (normal s a) (normal s b) else .either (normal s a) (normal s b)
  | .flip a => normal (!s) a

theorem normal_eval (t : Tree) (s : Bool) (r : Nat) :
    (normal s t).eval r = Bool.xor (t.eval r) s := by
  induction t generalizing s with
  | atom i =>
    fin_cases i <;> cases s <;> simp [normal,signedLeaf,Expr.eval,Tree.eval,value,leafValue,
      PetersenAux3616.withGate,PetersenAux3616.literal,Fin.ofNat]
  | both a b ih jh | either a b ih jh =>
    cases s <;> simp [normal,Expr.eval,Tree.eval,ih,jh,Bool.not_and,Bool.not_or]
  | flip a ih => cases s <;> simp [normal,Tree.eval,ih]

def Tree.stat : Tree → Nat × Nat
  | .atom _ => (1,0)
  | .both a b | .either a b => (a.stat.1+b.stat.1,a.stat.2+b.stat.2)
  | .flip a => (a.stat.1,a.stat.2+1)

theorem normal_size (t : Tree) (s : Bool) : (normal s t).leaves≤t.stat.1 := by
  induction t generalizing s with
  | atom i => fin_cases i <;> cases s <;> decide +kernel
  | both a b ih jh | either a b ih jh =>
    cases s <;> simp only [normal,ite_true,Expr.leaves,Tree.stat] <;> apply Nat.add_le_add <;> first | apply ih | apply jh
  | flip a ih => exact ih _

def mono : Tree → PetersenAux3616.Formula
  | .atom i => .var i
  | .both a b => .conj (mono a) (mono b)
  | .either a b => .disj (mono a) (mono b)
  | .flip a => mono a

theorem mono_eval (t : Tree) (r : Nat) (h : t.stat.2=0) :
    (mono t).eval (leafValue r)=t.eval r := by
  induction t with
  | atom _ => rfl
  | flip a _ => simp [Tree.stat] at h
  | both a b ih jh | either a b ih jh =>
    simp only [Tree.stat] at h
    simp only [mono,Tree.eval,PetersenAux3616.Formula.eval,ih (by omega),jh (by omega)]

theorem mono_size (t : Tree) : (mono t).leaves=t.stat.1 := by
  induction t with
  | atom _ => rfl
  | flip _ ih => exact ih
  | both a b ih jh | either a b ih jh => simp [mono,Tree.stat,PetersenAux3616.Formula.leaves,ih,jh]

theorem tree_bound (t : Tree) (fits : ∀ r, t.eval r=target r) :
    14≤t.stat.1 ∧ (t.stat.2=0 → 16≤t.stat.1) := by
  have sf : Fits (normal false t) := by
    intro r
    simpa [normal_eval] using fits r
  constructor
  · exact (signed_leaf_bound _ sf).trans (normal_size _ _)
  · intro n
    have mf : PetersenAux3616.FitsAux 1 2 true (mono t) := by
      have hp : ∀ r∈PetersenAux3616.positive, target r = true := by decide +kernel
      have hn : ∀ r∈PetersenAux3616.negative, target r = false := by decide +kernel
      constructor
      · intro r hr
        exact (mono_eval t r n).trans ((fits r).trans (hp r hr))
      · intro r hr
        exact (mono_eval t r n).trans ((fits r).trans (hn r hr))
    simpa only [mono_size] using Petersen4850.leaves_needed _ mf

end SignedPetersen

namespace SignedPetersen
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def arg4850 (ws : List Tree) (ls : List Nat) (j : Nat) (empty : Tree) : Tree :=
  match ls[j]? with
  | none => empty
  | some i => ws.getD i (.atom 10)

def node4850 (ws : List Tree) (g : Gate) : Tree :=
  let a := arg4850 ws g.inputs
  match g.op with
  | .and => .both (a 0 (.atom 11)) (a 1 (.atom 11))
  | .or => .either (a 0 (.atom 10)) (a 1 (.atom 10))
  | .not => .flip (a 0 (.atom 10))
  | _ => .atom 10

def sizeNode4850 (s : List (Nat × Nat)) (g : Gate) :=
  let col := fun j => (g.inputs[j]?.bind fun i => s[i]?).getD (1,0)
  let a := col 0
  let b := col 1
  ite (g.op.eval [false]=true) (a.1,a.2+1) (a.1+b.1,a.2+b.2)

def goodGate4850 (g : Gate) := (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2

theorem read_stat4850 (ws : List Tree) (ls : List Nat) (j : Nat) (d : Fin 13) :
  (arg4850 ws ls j (.atom d)).stat = (ls[j]?.bind fun i => (ws.map Tree.stat)[i]?).getD (1,0) := by
  unfold arg4850
  cases h : ls[j]? with
  | none => rfl
  | some i =>
    simp only [Option.bind_some,List.getElem?_map,List.getD_eq_getElem?_getD]
    cases ws[i]? <;> rfl

theorem project_stat4850 (ws : List Tree) (g : Gate) (h : goodGate4850 g) :
    (node4850 ws g).stat=sizeNode4850 (ws.map Tree.stat) g := by
  obtain ⟨op,l⟩ := g
  obtain ⟨h,_⟩ := h
  rcases h with h|h|h <;> change op=_ at h <;> subst op <;>
    simp [node4850,Tree.stat,read_stat4850,sizeNode4850,GateOp.eval]

theorem read_val4850 (ws : List Tree) (i r : Nat) :
    (ws.getD i (.atom 10)).eval r=(ws.map (Tree.eval r)).getD i false := by
  exact (List.getD_map (l:=ws) (n:=i) (d:=.atom 10) (Tree.eval r)).symm

theorem ev_getD4850 (x : Option Tree) (r : Nat) :
    (x.getD (.atom 10)).eval r=(x.map (Tree.eval r)).getD false := by cases x <;> rfl

theorem project_val4850 (ws : List Tree) (g : Gate) (h : goodGate4850 g) (r : Nat) :
  (node4850 ws g).eval r = g.op.eval (g.inputs.map fun i => (ws.map (Tree.eval r)).getD i false) := by
  obtain ⟨op,l⟩ := g
  obtain ⟨h,sz⟩ := h
  have shapes : l=[] ∨ (∃ a,l=[a]) ∨ ∃ a b,l=[a,b] := by
    change l.length≤2 at sz
    cases l with
    | nil => simp
    | cons a l =>
      cases l with
      | nil => simp
      | cons b l =>
        cases l with
        | nil => simp
        | cons c l => simp at sz
  rcases h with h|h|h <;> change op=_ at h <;> subst op <;>
    rcases shapes with e|⟨a,e⟩|⟨a,b,e⟩ <;> subst l <;>
    simp [node4850,arg4850,Tree.eval,ev_getD4850,GateOp.eval,leafValue,PetersenAux3616.withGate,PetersenAux3616.literal]

def treeInit4850 : List Tree := ([0,1,2,3,4,5,6,7,8,9,12] : List (Fin 13)).map Tree.atom
def treeStep4850 (ws : List Tree) (g : Gate) := ws++[node4850 ws g]
def unfold4850 (C : Circuit) := (C.gates.foldl treeStep4850 treeInit4850).getD C.output (.atom 10)

theorem fold_map4850 {α : Type} (p : Tree → α) (q : List α → Gate → α)
    (project : ∀ ws g, goodGate4850 g → p (node4850 ws g)=q (ws.map p) g)
    (gs : List Gate) (std : ∀ g∈gs, goodGate4850 g) (ws : List Tree) :
    (gs.foldl treeStep4850 ws).map p=gs.foldl (fun s g => s++[q s g]) (ws.map p) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,List.foldl_cons,ih (fun a h => std a (List.mem_cons_of_mem _ h))]
    simp only [treeStep4850,List.map_append,List.map_cons,List.map_nil,project ws g (std g List.mem_cons_self)]


def input (r : Nat) : List Bool :=
  List.ofFn (fun i : Fin 9 => r.testBit i.val) ++ [!r.testBit 0,r.testBit 1 || r.testBit 2]

theorem init_eval (r : Nat) : treeInit4850.map (Tree.eval r)=input r := by rfl

theorem eval_unfold (C : Circuit) (legal : FanInTwo C) (r : Nat) :
    (unfold4850 C).eval r = C.eval (input r) := by
  have std (g) (hg : g ∈ C.gates) : goodGate4850 g := legal g hg
  have p := fold_map4850 (Tree.eval r) (fun (w : List Bool) g => g.op.eval (g.inputs.map fun i => w.getD i false))
    (fun ws g h => project_val4850 ws g h r) C.gates std treeInit4850
  rw [init_eval] at p
  change ((C.gates.foldl treeStep4850 treeInit4850).getD C.output (.atom 10)).eval r = _
  rw [read_val4850,p]
  rfl

def stats (C : Circuit) : Nat × Nat :=
  (C.gates.foldl (fun s g => s++[sizeNode4850 s g]) (List.replicate 11 (1,0))).getD C.output (1,0)

theorem unfold_stats (C : Circuit) (legal : FanInTwo C) :
    (unfold4850 C).stat = stats C := by
  have std (g) (hg : g ∈ C.gates) : goodGate4850 g := legal g hg
  have p := fold_map4850 Tree.stat sizeNode4850 project_stat4850 C.gates std treeInit4850
  have init : treeInit4850.map Tree.stat=List.replicate 11 (1,0) := rfl
  rw [init] at p
  unfold unfold4850 stats
  have h := List.getD_map (l:=C.gates.foldl treeStep4850 treeInit4850) (n:=C.output) (d:=Tree.atom 10) Tree.stat
  simpa only [p,Tree.stat] using h.symm

theorem circuit_bound (C : Circuit) (legal : FanInTwo C) (works : ∀ r,C.eval (input r)=target r) :
    14≤(stats C).1 ∧ ((stats C).2=0 → 16≤(stats C).1) ∧ 15≤(stats C).1+(stats C).2 := by
  have h := tree_bound (unfold4850 C) (fun r => (eval_unfold C legal r).trans (works r))
  rw [unfold_stats C legal] at h
  exact ⟨h.1,h.2,by by_cases n : (stats C).2=0 <;> first | have := h.2 n; omega | omega⟩

end SignedPetersen

-- The first premise is the exact statement of the merged L-meta-3640, proved
-- by dsgallups in upstream PR 7496. Julleht identified its p=12 specialization
-- for L-meta-4850 in upstream PR 9598.
namespace PetersenSpecialization

theorem pair_twelve
  (six_pairs : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ x2 ∈ [(12 : ℕ), (13 : ℕ), (15 : ℕ), (18 : ℕ), (23 : ℕ), (28 : ℕ)], ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (13 : ℕ) → ∃ (x7 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ)), x7 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) || x7 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ)))]) ≠ x1 x7) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (13 : ℕ) → ∃ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (9 : ℕ)), x4 (1 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ))]) ≠ (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) := by
  intro C legal size
  obtain ⟨x,bad⟩ := six_pairs 12 (by decide) C legal size
  refine ⟨x,?_⟩
  convert bad using 1
  simp [List.any_cons,Bool.or_assoc]
  rfl
end PetersenSpecialization

#print axioms SignedPetersen.signed_leaf_bound
#print axioms SignedPetersen.circuit_bound
#print axioms PetersenSpecialization.pair_twelve
