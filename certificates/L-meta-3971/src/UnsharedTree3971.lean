import TreeConclusion3971
namespace PetersenNegated3971

inductive Expr3971 where
  | atom (i : Fin 12)
  | gate (isAnd : Bool) (left right : Expr3971)
  | invert (arg : Expr3971)

def opBool (isAnd x y : Bool) := if isAnd then x && y else x || y
def opForm (isAnd : Bool) (x y : Formula) := if isAnd then Formula.conj x y else Formula.disj x y
def Expr3971.ev (r : Nat) : Expr3971 → Bool
  | .atom i => leafValue r ⟨i.val,by omega⟩
  | .gate b x y => opBool b (x.ev r) (y.ev r)
  | .invert x => !(x.ev r)
def Expr3971.stat : Expr3971 → Nat × Nat
  | .atom _ => (1,0)
  | .gate _ x y => (x.stat.1+y.stat.1,x.stat.2+y.stat.2)
  | .invert x => (x.stat.1,x.stat.2+1)

theorem opShape (b : Bool) (x y : Formula) : (opForm b x y).leaves=x.leaves+y.leaves ∧
    marked (opForm b x y)=marked x+marked y ∧
    ∀ env, (opForm b x y).eval env=opBool b (x.eval env) (y.eval env) := by
  cases b <;> simp [opForm,Formula.leaves,marked,labels,List.count_append,Formula.eval,opBool]

def Clear (x : Expr3971) := ∃ f : Formula, marked f=0 ∧ f.leaves=x.stat.1 ∧
  ∀ r, f.eval (leafValue r)=x.ev r
def WithOne (x : Expr3971) := ∃ o t : Formula, marked o=1 ∧ o.leaves-1+t.leaves=x.stat.1 ∧
  ∀ r, o.eval (outerValue t r)=x.ev r

theorem outside_clear (f : Formula) (h : marked f=0) (t : Formula) (r : Nat) :
    f.eval (outerValue t r)=f.eval (leafValue r) := by
  have non : (12 : Fin 13)∉labels f := by
    intro mem
    have p := List.count_pos_iff.mpr mem
    change 0<marked f at p
    omega
  have eq (j) (hj : j∈labels f) : outerValue t r j=leafValue r j := by
    have n : j.val≠12 := fun h => non ((Fin.ext h : j=12) ▸ hj)
    simp [outerValue,outside,leafValue,n]
  apply Bool.eq_iff_iff.mpr
  exact ⟨eval_mono_on f _ _ (fun j hj => (eq j hj) ▸ id),eval_mono_on f _ _ (fun j hj => (eq j hj) ▸ id)⟩

theorem leaves_pos (f : Formula) : 0<f.leaves := by
  induction f with
  | var _ => exact Nat.zero_lt_one
  | conj x y hx hy | disj x y hx hy => change 0<x.leaves+y.leaves; omega

theorem tree_decomp (e : Expr3971) : (e.stat.2=0 → Clear e) ∧ (e.stat.2=1 → WithOne e) := by
  induction e with
  | atom i =>
    constructor
    · intro _
      refine ⟨.var ⟨i.val,by omega⟩,?_,rfl,fun _ => rfl⟩
      have h : (⟨i.val,by omega⟩ : Fin 13)≠12 := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [marked,labels,h]
    · intro h; cases h
  | invert e ih =>
    constructor
    · intro h; change e.stat.2+1=0 at h; omega
    · intro h
      change e.stat.2+1=1 at h
      obtain ⟨t,_,len,sem⟩ := ih.1 (by omega)
      refine ⟨.var 12,t,by decide,?_,?_⟩
      · simpa [Formula.leaves,Expr3971.stat] using len
      · intro r; simp [outerValue,outside,invertSub,Formula.eval,Expr3971.ev,sem]
  | gate b x y ix iy =>
    constructor
    · intro h
      change x.stat.2+y.stat.2=0 at h
      obtain ⟨a,ma,la,sa⟩ := ix.1 (by omega)
      obtain ⟨c,mc,lc,sc⟩ := iy.1 (by omega)
      obtain ⟨form,mark,sem⟩ := opShape b a c
      refine ⟨opForm b a c,by omega,?_,?_⟩
      · change _=x.stat.1+y.stat.1; omega
      · intro r; rw [sem,sa,sc]; rfl
    · intro h
      change x.stat.2+y.stat.2=1 at h
      by_cases pos : x.stat.2=1
      · obtain ⟨a,t,ma,la,sa⟩ := ix.2 pos
        obtain ⟨c,mc,lc,sc⟩ := iy.1 (by omega)
        obtain ⟨form,mark,sem⟩ := opShape b a c
        refine ⟨opForm b a c,t,by omega,?_,?_⟩
        · have := leaves_pos a; change _=x.stat.1+y.stat.1; omega
        · intro r; rw [sem,sa,outside_clear c mc,sc]; rfl
      · obtain ⟨a,ma,la,sa⟩ := ix.1 (by omega)
        obtain ⟨c,t,mc,lc,sc⟩ := iy.2 (by omega)
        obtain ⟨form,mark,sem⟩ := opShape b a c
        refine ⟨opForm b a c,t,by omega,?_,?_⟩
        · have := leaves_pos c; change _=x.stat.1+y.stat.1; omega
        · intro r; rw [sem,outside_clear a ma,sa,sc]; rfl

end PetersenNegated3971
