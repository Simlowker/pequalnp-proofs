import Essential3971
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Ring
namespace PetersenNegated3971

def leafValue (m : Nat) (j : Fin 13) := if j.val=12 then false else literal 0 m j
def invertSub (inner : Formula) (m : Nat) := !(inner.eval (leafValue m))
def outerValue (inner : Formula) (m : Nat) := outside (invertSub inner) m
def decoded (t : Formula) := (positive++negative).foldr (fun r a => Nat.bit (t.eval (leafValue r)) a) 0
def marked (o : Formula) : Nat := (labels o).count 12
def price (d extra : Int) (j : Fin 13) := if j.val=12 then extra else d

theorem cost_once (o : Formula) (d extra : Int) :
    o.cost (price d extra) = (o.leaves : Int)*d + (marked o : Int)*(extra-d) := by
  induction o with
  | var j =>
    by_cases h : j=12
    · subst j; simp [Formula.cost,price,Formula.leaves,marked,labels]
    · have hv : j.val≠12 := fun e => h (Fin.ext e)
      simp [Formula.cost,price,Formula.leaves,marked,labels,h,hv]
  | conj a b ia ib | disj a b ia ib =>
    simp only [Formula.cost,Formula.leaves,ia,ib,marked,labels,List.count_append,Nat.cast_add]
    ring

theorem inner_anti (t : Formula) (i : Fin 9) :
    invertSub t (hiRows i)=true → invertSub t (loRows i)=true := by
  have ord : ∀ i : Fin 9, ∀ j : Fin 13, leafValue (loRows i) j=true → leafValue (hiRows i) j=true := by decide +kernel
  have pos := eval_mono_on t _ _ (fun j _ => ord i j)
  unfold invertSub
  generalize t.eval (leafValue (hiRows i)) = hi at *
  generalize t.eval (leafValue (loRows i)) = lo at *
  cases hi <;> cases lo <;> simp_all

theorem small_inner (outer inner : Formula) (once : marked outer=1)
    (spec : ∀ r : Fin 512, outer.eval (outerValue inner r.val)=edge r.val)
    (size : outer.leaves - 1 + inner.leaves≤14) : inner.leaves≤5 := by
  apply negative_budget outer _ (inner_anti inner) spec _ _ size
  have cnt : 0<(labels outer).count 12 := by change 0<marked outer; omega
  exact List.count_pos_iff.mp cnt

def rowOut (t : Formula) (i : Nat) := outerValue t (positive.getD i 0)
def colOut (t : Formula) (j : Nat) := outerValue t (negative.getD j 0)
def capacity (w : Matrix) (t : Formula) (i : Fin 13) (cap : Int) : Prop :=
  ∀ u, u.Sublist (ri.filter fun r => rowOut t r i) →
    upper w u (ci.filter fun c => !(colOut t c i)) ≤ cap

theorem outside_bound (o t : Formula) (w : Matrix) (d k : Int)
    (fit : ∀ r : Fin 512, o.eval (outerValue t r.val)=edge r.val) (once : marked o=1)
    (caps : ∀ i, capacity w t i (price d k i)) :
    rect w ri ci ≤ ((o.leaves : Int)-1)*d+k := by
  have ps : ∀ i∈ri, positive.getD i 0 < 512 ∧ edge (positive.getD i 0)=true := by decide +kernel
  have ns : ∀ j∈ci, negative.getD j 0 < 512 ∧ edge (negative.getD j 0)=false := by decide +kernel
  have h := formula_bound w ri ci (rowOut t) (colOut t) (price d k) caps o
    (List.Sublist.refl ri) (List.Sublist.refl ci)
    (fun i hi => (fit ⟨_,(ps i hi).1⟩).trans (ps i hi).2)
    (fun j hj => (fit ⟨_,(ns j hj).1⟩).trans (ns j hj).2)
  rw [cost_once,once] at h
  convert h using 1 <;> push_cast <;> ring

theorem exclude (o t : Formula) (w : Matrix) (d k : Int) (dpos : 0≤d)
    (fit : ∀ r : Fin 512, o.eval (outerValue t r.val)=edge r.val) (once : marked o=1)
    (caps : ∀ i, capacity w t i (price d k i))
    (mass : (14-(t.leaves : Int))*d+k < rect w ri ci) :
    14 < o.leaves-1+t.leaves := by
  by_contra! short
  have bound := outside_bound o t w d k fit once caps
  have ar : ((o.leaves : Int)-1)≤14-(t.leaves : Int) := by omega
  have lim := add_le_add_right (mul_le_mul_of_nonneg_right ar dpos) k
  omega

end PetersenNegated3971
