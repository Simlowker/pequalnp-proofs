import PEqualNP.Outside.L_meta_3223
import PEqualNP.Outside.L_meta_5459

/-!
Partial result for L-meta-10726. Checked relative to upstream e66310d1.

Fixing input 2 to zero and identifying inputs 1 and 4 leaves the five-input
threshold-two function, which needs ten gates. This gives the lower bound
eleven on the original graph. An explicit monotone circuit uses thirteen.

For formulas, a signed integer matrix on 23 positive and 17 negative inputs
has total weight 60113. Every rectangle belonging to a single literal,
positive or negated, has weight at most 5002, verified by the kernel.
Thus even a formula with arbitrary negations needs at least 13 leaves,
or twelve binary nodes. This obstruction applies to the unrolling of a
circuit; gates used more than once can occur multiple times in that tree.

The final theorem isolates the remaining eleven- and twelve-gate circuits by
their reuse of binary gates and by a twenty-input test for replacing the
inverter at its place in the list. These are necessary conditions. The full
universal replacement assertion remains open in this file.
-/

namespace Seven10726
open PEqualNP.CircuitLowerBounds
def gates13 : List Gate := [⟨.or,[0,1]⟩, ⟨.or,[3,5]⟩, ⟨.and,[7,8]⟩, ⟨.and,[3,5]⟩, ⟨.or,[0,2]⟩, ⟨.and,[4,11]⟩, ⟨.or,[7,8]⟩, ⟨.or,[2,4]⟩, ⟨.or,[13,14]⟩, ⟨.and,[6,15]⟩, ⟨.or,[9,10]⟩, ⟨.or,[12,16]⟩, ⟨.or,[17,18]⟩]
theorem large (gates : List Gate) (hs : 13 ≤ gates.length) : ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  refine ⟨gates13,19,?_,hs,?_⟩
  · intro g hg
    simp only [gates13,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
end Seven10726

namespace Seven10726
open PEqualNP.CircuitLowerBounds
def bTick (xs : List Bool) (g : Gate) := xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]
def above (x y : List Bool) : Prop := ∀ i, x.getD i false=true → y.getD i false=true

theorem gate_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (rel : above x y) :
    g.op.eval (g.inputs.map fun i => x.getD i false) = true →
    g.op.eval (g.inputs.map fun i => y.getD i false) = true := by
  rcases hop with h | h
  · simp only [h,GateOp.eval,List.all_map,List.all_eq_true,Function.comp_def,id_eq]
    intro hx i hi
    exact rel i (hx i hi)
  · simp only [h,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_def,id_eq]
    rintro ⟨i,hi,hx⟩
    exact ⟨i,hi,rel i hx⟩

theorem get_append_other {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]

theorem get_append_last (L : List Bool) (s : Bool) : (L++[s]).getD L.length false=s := by simp
theorem raw_get {n : Nat} (x : Fin n → Bool) (i : Fin n) : (List.ofFn x).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD]

theorem run_mono (gs : List Gate) (ops : ∀ g ∈ gs, g.op=.and ∨ g.op=.or)
    (x y : List Bool) (len : x.length=y.length) (r : above x y) :
    above (gs.foldl bTick x) (gs.foldl bTick y) := by
  induction gs generalizing x y with
  | nil => exact r
  | cons g gs ih =>
    apply ih (fun h hh => ops _ (List.mem_cons_of_mem _ hh)) (bTick x g) (bTick y g) (by simp [bTick,len])
    intro i
    by_cases last : i=x.length
    · subst i
      change (x++[_]).getD x.length false=true → (y++[_]).getD x.length false=true
      rw [get_append_last,len,get_append_last]
      exact gate_mono g (ops g List.mem_cons_self) x y r
    · change (x++[_]).getD i false=true → (y++[_]).getD i false=true
      rw [get_append_other _ _ _ _ last,get_append_other _ _ _ _ (by omega)]
      exact r i

def val (x : Fin 7 → Bool) := decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

def assignment (r : Nat) (i : Fin 7) := r.testBit i.val
def pos : List Nat := [9,10,17,20,33,34,40,65,66,68,72,80,96]
def neg : List Nat := [7,12,18,24,36,48,64]
def subset (x y : Fin 7 → Bool) := ∀ i, x i=true → y i=true
def AO (gs : List Gate) := ∀ g∈gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2
def computes (C : Circuit) (x : Fin 7 → Bool) := C.eval (List.ofFn x)
def correct (C : Circuit) := ∀ x, computes C x=val x

theorem covers : (∀ x : Fin 7 → Bool, val x=true →
    ∃ r ∈ pos, subset (assignment r) x) ∧
    (∀ x : Fin 7 → Bool, val x=false →
    ∃ r ∈ neg, subset x (assignment r)) := by
  unfold subset
  decide +kernel

theorem grades : (∀ r∈pos, val (assignment r)=true) ∧ (∀ r∈neg, val (assignment r)=false) := by
  decide +kernel

theorem increasing (C : Circuit) (ok : AO C.gates) {x y : Fin 7 → Bool} (h : subset x y) :
    computes C x=true → computes C y=true := by
  apply run_mono C.gates (fun g hg => (ok g hg).1) (List.ofFn x) (List.ofFn y) (by simp) _ C.output
  intro j
  by_cases hj : j<7
  · change (List.ofFn x).getD (⟨j,hj⟩:Fin 7).val false=true → (List.ofFn y).getD (⟨j,hj⟩:Fin 7).val false=true
    rw [raw_get,raw_get];exact h _
  · simp [List.getD_eq_getElem?_getD,hj]

theorem check_boundary (C : Circuit) (ok : AO C.gates) :
    correct C ↔ (∀ r∈pos, computes C (assignment r)=true) ∧
      (∀ r∈neg, computes C (assignment r)=false) := by
  constructor
  · intro done
    exact ⟨fun r hr => (done _).trans (grades.1 r hr),fun r hr => (done _).trans (grades.2 r hr)⟩
  · rintro ⟨hp,hn⟩ x
    cases eq : val x with
    | true =>
      obtain ⟨r,hr,sub⟩ := covers.1 x eq
      exact increasing _ ok sub (hp r hr)
    | false =>
      obtain ⟨r,hr,sub⟩ := covers.2 x eq
      cases v : computes C x with
      | false => rfl
      | true => exact Bool.noConfusion ((hn _ hr).symm.trans (increasing _ ok sub v))

def constGate (b : Bool) : Gate := ⟨if b then .and else .or,[]⟩
def forced (pre post : List Gate) (o : Nat) (b : Bool) : Circuit := ⟨pre++constGate b::post,o⟩
def original (pre post : List Gate) (inputs : List Nat) (o : Nat) : Circuit :=
  ⟨pre++⟨.not,inputs⟩::post,o⟩
def cut (pre : List Gate) (inputs : List Nat) (x : Fin 7 → Bool) :=
  GateOp.not.eval (inputs.map fun i => (pre.foldl bTick (List.ofFn x)).getD i false)

theorem forced_AO (pre post : List Gate) (p : AO pre) (q : AO post) (o : Nat) (b : Bool) :
    AO (forced pre post o b).gates := by
  intro g hg
  change g ∈ pre++constGate b::post at hg
  rcases List.mem_append.mp hg with a|a
  · exact p _ a
  rcases List.mem_cons.mp a with rfl|a
  · cases b <;> simp [constGate]
  · exact q _ a

theorem at_cut (pre post : List Gate) (ls : List Nat) (o : Nat) (x : Fin 7 → Bool) :
    computes (forced pre post o (cut pre ls x)) x = computes (original pre post ls o) x := by
  change ((pre++_::post).foldl bTick (List.ofFn x)).getD o false = ((pre++_::post).foldl bTick (List.ofFn x)).getD o false
  simp only [List.foldl_append,List.foldl_cons]
  let w := pre.foldl bTick (List.ofFn x)
  have same : bTick w (constGate (cut pre ls x))=bTick w ⟨.not,ls⟩ := by
    unfold bTick
    apply congrArg (fun b : Bool => w++[b])
    change (constGate (cut pre ls x)).op.eval ((constGate (cut pre ls x)).inputs.map fun i => w.getD i false) = cut pre ls x
    cases cut pre ls x <;> rfl
  exact congrArg (fun init => (post.foldl bTick init).getD o false) same

theorem nested (pre post : List Gate) (q : AO post) (o : Nat) (x : Fin 7 → Bool) :
    computes (forced pre post o false) x=true → computes (forced pre post o true) x=true := by
  change ((pre++_::post).foldl bTick (List.ofFn x)).getD o false=true →
    ((pre++_::post).foldl bTick (List.ofFn x)).getD o false=true
  simp only [List.foldl_append,List.foldl_cons]
  apply run_mono post (fun g hg => (q g hg).1) _ _ (by simp [bTick]) _ o
  intro i hi
  let v := pre.foldl bTick (List.ofFn x)
  change (v++[false]).getD i false=true at hi
  change (v++[true]).getD i false=true
  by_cases e : i=v.length
  · subst i;rw [get_append_last]
  · rw [get_append_other _ _ _ _ e] at hi
    rwa [get_append_other _ _ _ _ e]

theorem critical (pre post : List Gate) (p : AO pre) (q : AO post) (ls : List Nat) (o : Nat)
    (hc : correct (original pre post ls o)) (lowFails : ¬correct (forced pre post o false))
    (highFails : ¬correct (forced pre post o true)) :
    (∃ r∈pos, cut pre ls (assignment r)=true ∧ computes (forced pre post o false) (assignment r)=false) ∧
    (∃ r∈neg, cut pre ls (assignment r)=false ∧ computes (forced pre post o true) (assignment r)=true) := by
  have atRow (x) : computes (forced pre post o (cut pre ls x)) x=val x :=
    (at_cut pre post ls o x).trans (hc x)
  have lo (r) (h : r∈neg) : computes (forced pre post o false) (assignment r)=false := by
    have agree := (atRow (assignment r)).trans (grades.2 r h)
    cases b : cut pre ls (assignment r) <;> rw [b] at agree
    · exact agree
    · cases e : computes (forced pre post o false) (assignment r) with
      | false => rfl
      | true => exact Bool.noConfusion (agree.symm.trans (nested _ _ q o _ e))
  have hi (r) (h : r∈pos) : computes (forced pre post o true) (assignment r)=true := by
    have agree := (atRow (assignment r)).trans (grades.1 r h)
    cases b : cut pre ls (assignment r) <;> rw [b] at agree
    · exact nested _ _ q o _ agree
    · exact agree
  constructor
  · by_contra! bad
    apply lowFails
    apply (check_boundary _ (forced_AO _ _ p q _ _)).2
    refine ⟨?_,lo⟩
    intro r hr
    have eq := (atRow (assignment r)).trans (grades.1 r hr)
    cases b : cut pre ls (assignment r) <;> rw [b] at eq
    · exact eq
    · simpa using bad r hr b
  · by_contra! bad
    apply highFails
    apply (check_boundary _ (forced_AO _ _ p q _ _)).2
    refine ⟨hi,?_⟩
    intro r hr
    have eq := (atRow (assignment r)).trans (grades.2 r hr)
    cases b : cut pre ls (assignment r) <;> rw [b] at eq
    · simpa using bad r hr b
    · exact eq

end Seven10726

namespace Seven10726
open PEqualNP.CircuitLowerBounds

def AOgate (g : Gate) := (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2
def splice (pre post : List Gate) (g : Gate) (o : Nat) : Circuit := ⟨pre++g::post,o⟩
def signal (pre : List Gate) (g : Gate) (x : Fin 7 → Bool) :=
  g.op.eval (g.inputs.map fun i => (pre.foldl bTick (List.ofFn x)).getD i false)

theorem splice_AO {pre post g o} (p : AO pre) (q : AO post) (h : AOgate g) :
    AO (splice pre post g o).gates := by
  intro a ha
  change a ∈ pre++g::post at ha
  rcases List.mem_append.mp ha with a|a
  · exact p _ a
  rcases List.mem_cons.mp a with rfl|a
  · exact h
  · exact q _ a

theorem splice_eq (pre post : List Gate) (g : Gate) (o : Nat) (x : Fin 7 → Bool) :
    computes (splice pre post g o) x = computes (forced pre post o (signal pre g x)) x := by
  change ((pre++g::post).foldl bTick (List.ofFn x)).getD o false = ((pre++_::post).foldl bTick (List.ofFn x)).getD o false
  simp only [List.foldl_append,List.foldl_cons]
  let w := pre.foldl bTick (List.ofFn x)
  have same : bTick w g=bTick w (constGate (signal pre g x)) := by
    unfold bTick
    apply congrArg (fun b : Bool => w++[b])
    change signal pre g x = _
    cases signal pre g x <;> rfl
  exact congrArg (fun init => (post.foldl bTick init).getD o false) same

def demands (pre post : List Gate) (o : Nat) (sig : (Fin 7 → Bool) → Bool) : Prop :=
    (∀ r∈pos, computes (forced pre post o false) (assignment r)=false → sig (assignment r)=true) ∧
    (∀ r∈neg, computes (forced pre post o true) (assignment r)=true → sig (assignment r)=false)

/-- A test for a proposed replacement using only thirteen positive and seven negative rows. -/
theorem rewrite_iff {pre post ls o} (p : AO pre) (q : AO post) (hc : correct (original pre post ls o))
    {g : Gate} (ok : AOgate g) :
    correct (splice pre post g o) ↔ demands pre post o (signal pre g) := by
  rw [check_boundary _ (splice_AO p q ok)]
  have atRow (x) : computes (forced pre post o (cut pre ls x)) x=val x :=
    (at_cut pre post ls o x).trans (hc x)
  have hi (r) (h : r∈pos) : computes (forced pre post o true) (assignment r)=true := by
    have eq := (atRow (assignment r)).trans (grades.1 r h)
    cases b : cut pre ls (assignment r) <;> rw [b] at eq
    · exact nested _ _ q o _ eq
    · exact eq
  have lo (r) (h : r∈neg) : computes (forced pre post o false) (assignment r)=false := by
    have eq := (atRow (assignment r)).trans (grades.2 r h)
    cases b : cut pre ls (assignment r) <;> rw [b] at eq
    · exact eq
    · cases l : computes (forced pre post o false) (assignment r) with
      | false => rfl
      | true => exact Bool.noConfusion (eq.symm.trans (nested _ _ q o _ l))
  constructor
  · rintro ⟨hp,hn⟩
    constructor
    · intro r hr bad
      have e := hp r hr
      rw [splice_eq] at e
      cases s : signal pre g (assignment r) with
      | true => rfl
      | false => rw [s,bad] at e; contradiction
    · intro r hr bad
      have e := hn r hr
      rw [splice_eq] at e
      cases s : signal pre g (assignment r) with
      | false => rfl
      | true => rw [s,bad] at e; contradiction
  · rintro ⟨hp,hn⟩
    constructor
    · intro r hr
      rw [splice_eq]
      cases s : signal pre g (assignment r) with
      | true => exact hi r hr
      | false =>
        cases l : computes (forced pre post o false) (assignment r) with
        | true => rfl
        | false => exact Bool.noConfusion (s.symm.trans (hp r hr l))
    · intro r hr
      rw [splice_eq]
      cases s : signal pre g (assignment r) with
      | false => exact lo r hr
      | true =>
        cases h : computes (forced pre post o true) (assignment r) with
        | false => rfl
        | true => exact Bool.noConfusion (s.symm.trans (hn r hr h))

def uniqueNot (gs : List Gate) := ∀ i j : Fin gs.length,
    (gs.get i).op=.not → (gs.get j).op=.not → i=j
def legal (gs : List Gate) := ∀ g∈gs, (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2

theorem decompose (gs : List Gate) (hf : legal gs) (hu : uniqueNot gs) :
    AO gs ∨ ∃ pre post ls, gs=pre++⟨.not,ls⟩::post ∧ AO pre ∧ AO post := by
  induction gs with
  | nil => left; intro g h; contradiction
  | cons g gs ih =>
    have head := hf g List.mem_cons_self
    have tail : legal gs := fun h hh => hf h (List.mem_cons_of_mem _ hh)
    by_cases ng : g.op=.not
    · right
      refine ⟨[],gs,g.inputs,by cases g; simp_all,by intro h hh;contradiction,?_⟩
      intro a ha
      obtain ⟨k,hk⟩ := List.mem_iff_get.mp ha
      have no : a.op≠.not := by
        intro n
        have both := hu 0 k.succ ng (by change (gs.get k).op=.not; rw [hk];exact n)
        have out := congrArg Fin.val both
        simp at out
      rcases (tail _ ha).1 with l|l|l
      · exact ⟨Or.inl l,(tail _ ha).2⟩
      · exact ⟨Or.inr l,(tail _ ha).2⟩
      · contradiction
    · have hgate : AOgate g := ⟨head.1.imp_right (fun h => h.resolve_right ng),head.2⟩
      have ut : uniqueNot gs := fun i j fi fj => Fin.succ_inj.mp (hu i.succ j.succ fi fj)
      have extend {l : List Gate} (good : AO l) : AO (g::l) := by
        intro a ha
        rcases List.mem_cons.mp ha with rfl|ha
        · exact hgate
        · exact good _ ha
      rcases ih tail ut with ok|⟨pre,post,ls,eq,hp,hq⟩
      · exact Or.inl (extend ok)
      · exact Or.inr ⟨g::pre,post,ls,by rw [eq]; rfl,extend hp,hq⟩

def replacement (gs : List Gate) := ∃ D : Circuit, AO D.gates ∧ D.gates.length ≤ gs.length ∧ correct D

theorem remaining {gs o} (hf : legal gs) (hu : uniqueNot gs) (hc : correct ⟨gs,o⟩)
    (failure : ¬replacement gs) :
    gs.length≤12 ∧ ∃ pre post ls, gs=pre++⟨.not,ls⟩::post ∧ AO pre ∧ AO post ∧
      ∀ g, AOgate g → ¬demands pre post o (signal pre g) := by
  have small : gs.length≤12 := by
    by_contra! h
    obtain ⟨gs',o',ok,sz,works⟩ := large gs (by omega)
    exact failure ⟨⟨gs',o'⟩,ok,sz,works⟩
  refine ⟨small,?_⟩
  rcases decompose gs hf hu with no|⟨pre,post,ls,eq,p,q⟩
  · exact False.elim (failure ⟨⟨gs,o⟩,no,le_rfl,hc⟩)
  · refine ⟨pre,post,ls,eq,p,q,?_⟩
    subst gs
    intro g ok tests
    exact failure ⟨splice pre post g o,splice_AO p q ok,by simp [splice],
      (rewrite_iff p q hc ok).2 tests⟩

end Seven10726

namespace Seven10726.Weight


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
  | var (i : Fin 16)
  | disj (l r : Formula)
  | conj (l r : Formula)

def Formula.eval (v : Fin 16 → Bool) : Formula → Bool
  | .var i => v i
  | .disj l r => l.eval v || r.eval v
  | .conj l r => l.eval v && r.eval v

def Formula.cost (c : Fin 16 → Int) : Formula → Int
  | .var i => c i
  | .disj l r | .conj l r => l.cost c + r.cost c

theorem variable_filter {xs ys : List Nat} (h : xs.Sublist ys) (p : Nat → Bool)
    (yes : ∀ i ∈ xs, p i = true) : xs.Sublist (ys.filter p) := by
  have hh := h.filter p
  rwa [List.filter_eq_self.mpr yes] at hh

theorem formula_bound (w : Matrix) (rows cols : List Nat) (yes no : Nat → Fin 16 → Bool)
    (cost : Fin 16 → Int)
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

def rowInput : List Nat := [9, 10, 17, 20, 33, 34, 40, 65, 66, 68, 72, 80, 96, 13, 14, 26, 37, 38, 70, 84, 49, 56, 88]
def colInput : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 16, 18, 24, 32, 36, 48, 64]
def rows := List.range rowInput.length
def cols := List.range colInput.length
def weights : List (List Int) := [[0, 398, 0, 730, 0, 0, 0, 73, 0, 289, 0, -1002, 1201, 0, 0, -199, -90], [0, 0, 0, 118, 0, -35, 0, 0, 48, 0, 0, 118, 70, 0, 35, -118, -83], [0, 223, 0, 0, 0, 1140, 0, 1029, 0, -1345, 0, 2609, 1472, 0, -1046, 919, -647], [0, 0, 0, 0, 0, 715, 0, 1029, 0, 1621, 0, 0, 2532, 0, 1634, 2468, -1744], [0, 530, 0, 662, 0, 0, 0, 0, 0, 0, 0, -662, -530, 530, 0, 662, 0], [0, 0, 0, 550, 0, -459, 0, 580, 0, 0, 0, 2551, -580, 1251, -121, 166, -671], [0, 0, 0, -370, 0, 459, 0, -580, 0, 1621, 0, -970, 480, 180, 1272, 970, 312], [0, 556, 0, 359, 0, 717, 0, 0, 0, -246, 0, -359, -448, 0, -246, -557, 2011], [0, 0, 0, 179, 0, 459, 0, 1029, 0, -1263, 0, 1434, -171, 0, -1121, -166, 3859], [0, 0, 0, 0, 0, 246, 0, 0, 0, 1889, 0, 0, -1889, 0, 1367, -1367, 5000], [0, -109, 0, -179, 0, -459, 0, 0, 0, 1801, 0, -1150, 2530, 0, -887, -1355, 2990], [0, 0, 0, 0, 0, -715, 0, -1029, 0, -538, 0, 1362, 996, 0, -973, 1355, 5000], [0, 0, 0, -179, 0, -459, 0, 0, 0, -1263, 0, -1075, -849, 0, 2094, 2090, 2714], [0, 0, 0, 0, 0, 1362, 0, 507, 0, 1785, 0, -729, 720, 0, -420, -720, -222], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1263, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 432, 0, -424, 0, 580, 0, 0, 0, 2763, 1865, 0, -717, 35, -588], [0, 0, 0, 32, 0, 1323, 0, 580, 0, -178, 0, -814, -942, 0, 1988, 814, -202], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1803, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, -180, 0, 0, 0, 0, 0, -180, 0, -87, 2165, 0, 180, 1339, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
def wmat : Matrix := fun i j => (weights.getD i []).getD j 0
def price : Int := 5002
def literal (input : Nat) (i : Fin 16) : Bool :=
  if i.val<7 then input.testBit i.val else if i.val<14 then !(input.testBit (i.val-7)) else decide (i.val=15)
def positive (r : Nat) := literal (rowInput.getD r 0)
def negative (r : Nat) := literal (colInput.getD r 0)

def cap (v : Fin 16) : Bool :=
  let rs := rows.filter fun i => positive i v
  let cs := cols.filter fun j => !negative j v
  if rs.isEmpty || cs.isEmpty then true else
  if rs.length ≤ cs.length then rs.sublists.all fun a => decide (upper wmat a cs ≤ price)
  else cs.sublists.all fun b => decide (upper (tr wmat) b rs ≤ price)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caps : ∀ v : Fin 16, cap v = true := by decide +kernel

theorem literal_bound (v : Fin 16) (a b : List Nat)
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

theorem total : rect wmat rows cols = 60113 := by decide +kernel

def Formula.leaves : Formula → Nat
  | .var _ => 1
  | .conj a b | .disj a b => a.leaves+b.leaves

theorem cost_eq (e : Formula) : e.cost (fun _ => price) = price*(e.leaves:Int) := by
  induction e with
  | var _ => simp [Formula.cost,Formula.leaves]
  | conj a b ih jh | disj a b ih jh => simp [Formula.cost,Formula.leaves,ih,jh,mul_add]

theorem trueRows : ∀ r ∈ rowInput, Seven10726.val (Seven10726.assignment r)=true := by decide +kernel
theorem falseCols : ∀ r ∈ colInput, Seven10726.val (Seven10726.assignment r)=false := by decide +kernel

theorem getD_in {xs : List Nat} {i : Nat} (hi : i < xs.length) : xs.getD i 0 ∈ xs := by
  simp [List.getD_eq_getElem?_getD,hi]

theorem lower (e : Formula) (ok : ∀ r, e.eval (literal r)=Seven10726.val (Seven10726.assignment r)) :
    13 ≤ e.leaves := by
  have h := formula_bound wmat rows cols positive negative (fun _ => price) literal_bound e
    (List.Sublist.refl _) (List.Sublist.refl _)
    (fun i hi => (ok _).trans (trueRows _ (getD_in (List.mem_range.mp hi))))
    (fun j hj => (ok _).trans (falseCols _ (getD_in (List.mem_range.mp hj))))
  rw [total,cost_eq] at h
  unfold price at h
  omega
end Seven10726.Weight

namespace Seven10726.Unfold
open PEqualNP.CircuitLowerBounds Seven10726.Weight

inductive Tree where
  | raw (i : Fin 7)
  | fixed (b : Bool)
  | both (x y : Tree)
  | either (x y : Tree)
  | inv (x : Tree)

def Tree.ev (r : Nat) : Tree → Bool
  | .raw i => assignment r i
  | .fixed b => b
  | .both x y => x.ev r && y.ev r
  | .either x y => x.ev r || y.ev r
  | .inv x => !(x.ev r)

def Tree.binary : Tree → Nat
  | .raw _ | .fixed _ => 0
  | .both x y | .either x y => x.binary+y.binary+1
  | .inv x => x.binary

def encode (i : Fin 7) (b : Bool) : Fin 16 :=
  ⟨if b then i.val+7 else i.val,by have := i.isLt;split <;> omega⟩

def normal (s : Bool) : Tree → Formula
  | .raw i => .var (encode i s)
  | .fixed b => .var (if Bool.xor s b then 15 else 14)
  | .both x y => if s then .disj (normal s x) (normal s y) else .conj (normal s x) (normal s y)
  | .either x y => if s then .conj (normal s x) (normal s y) else .disj (normal s x) (normal s y)
  | .inv x => normal (!s) x

theorem normal_ev (t : Tree) (s : Bool) (r : Nat) : (normal s t).eval (literal r) = Bool.xor (t.ev r) s := by
  induction t generalizing s with
  | fixed b => cases s <;> cases b <;> rfl
  | raw i =>
    have hi := i.isLt
    cases s <;> simp [normal,encode,Formula.eval,Tree.ev,assignment,literal,show i.val<7 from hi,show ¬i.val+7<7 by omega,show i.val+7<14 by omega]
  | inv x ih => cases s <;> simp [normal,Tree.ev,ih]
  | both x y ih jh | either x y ih jh =>
    cases s <;> simp [normal,Tree.ev,Formula.eval,ih,jh,Bool.not_or,Bool.not_and]

theorem normal_leaves (t : Tree) (s : Bool) : (normal s t).leaves = t.binary+1 := by
  induction t generalizing s with
  | raw _ | fixed _ => rfl
  | inv _ ih => exact ih _
  | both x y ih jh | either x y ih jh =>
    cases s <;> simp [normal,Formula.leaves,Tree.binary,ih,jh] <;> omega

def read (ws : List Tree) (j : Nat) := ws.getD j (.fixed false)
def arg (ws : List Tree) (inputs : List Nat) : Tree :=
  match inputs with
  | [] => .fixed false
  | i::_ => read ws i

def binaryGate (f : Tree → Tree → Tree) (b : Bool) (ws : List Tree) : List Nat → Tree
  | [] => .fixed b
  | [i] => read ws i
  | i::j::_ => f (read ws i) (read ws j)

def gate (ws : List Tree) (g : Gate) : Tree :=
  match g.op with
  | .and => binaryGate Tree.both true ws g.inputs
  | .or => binaryGate Tree.either false ws g.inputs
  | .not => .inv (arg ws g.inputs)
  | _ => .fixed false

def step (ws : List Tree) (g : Gate) := ws++[gate ws g]
def init : List Tree := List.ofFn (fun i : Fin 7 => Tree.raw i)
def unfoldCircuit (gs : List Gate) (o : Nat) := read (gs.foldl step init) o

theorem read_ev (r : Nat) (ws : List Tree) (i : Nat) :
    (read ws i).ev r=(ws.map (Tree.ev r)).getD i false := by
  simp only [read,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? <;> rfl

theorem gate_ev (r : Nat) (ws : List Tree) (g : Gate)
    (h : (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length ≤ 2) :
    (gate ws g).ev r=g.op.eval (g.inputs.map fun i => (ws.map (Tree.ev r)).getD i false) := by
  rcases g with ⟨op,ls⟩
  rcases h with ⟨ops,sz⟩
  change op=.and ∨ op=.or ∨ op=.not at ops
  change ls.length≤2 at sz
  rcases ops with rfl|rfl|rfl <;>
    rcases ls with _|⟨a,_|⟨b,_|⟨c,rest⟩⟩⟩ <;>
    simp_all [gate,arg,binaryGate,Tree.ev,GateOp.eval,read_ev]

theorem run_ev (r : Nat) (gs : List Gate) (hf : legal gs) (ws : List Tree) :
    (gs.foldl step ws).map (Tree.ev r)=gs.foldl bTick (ws.map (Tree.ev r)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,List.foldl_cons,ih (fun a ha => hf a (List.mem_cons_of_mem _ ha))]
    simp [step,bTick,gate_ev r ws g (hf g List.mem_cons_self)]

theorem unfold_eval (gs : List Gate) (o r : Nat) (hf : legal gs) :
    (unfoldCircuit gs o).ev r = computes ⟨gs,o⟩ (assignment r) := by
  rw [unfoldCircuit,read_ev,run_ev _ _ hf]
  have h : init.map (Tree.ev r) = List.ofFn (assignment r) := by
    simp [init,Tree.ev]
  rw [h]
  rfl

theorem actual_binary_lower (gs : List Gate) (o : Nat) (hf : legal gs) (hc : correct ⟨gs,o⟩) :
    12 ≤ (unfoldCircuit gs o).binary := by
  let t := unfoldCircuit gs o
  have fit (r : Nat) : (normal false t).eval (literal r) = Seven10726.val (assignment r) := by
    rw [normal_ev]
    change Bool.xor ((unfoldCircuit gs o).ev r) false=_
    rw [unfold_eval _ _ _ hf]
    simpa using hc (assignment r)
  have bound := Weight.lower (normal false t) fit
  rw [normal_leaves] at bound
  change 12 ≤ t.binary
  omega

def binaryGateOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or => true
  | _ => false

theorem shared_required {gs o} (hf : legal gs) (hu : uniqueNot gs) (hc : correct ⟨gs,o⟩)
    (failure : ¬replacement gs) :
    gs.countP binaryGateOp < (unfoldCircuit gs o).binary := by
  obtain ⟨small,pre,post,ls,eq,_,_,_⟩ := remaining hf hu hc failure
  have lb := actual_binary_lower gs o hf hc
  subst gs
  have l := List.countP_le_length (p := binaryGateOp) (l := pre)
  have r := List.countP_le_length (p := binaryGateOp) (l := post)
  simp only [List.length_append,List.length_cons] at small
  simp only [List.countP_append,List.countP_cons,show binaryGateOp ⟨.not,ls⟩=false by rfl, Bool.false_eq_true,↓reduceIte,Nat.add_zero]
  omega

end Seven10726.Unfold

namespace Seven10726
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3223

def projection : List (Option (Fin 5)) := [some 0,some 1,none,some 2,some 1,some 3,some 4]
def lifted (x : Fin 5 → Bool) : Fin 7 → Bool := ![x 0,x 1,false,x 2,x 1,x 3,x 4]
theorem lifted_list : ∀ x, proj projection x=List.ofFn (lifted x) := by decide +kernel
theorem lifted_target : ∀ x, val (lifted x)=PEqualNP.Outside.L_meta_5459.T25 x := by decide +kernel

theorem changes (C : Circuit) (hc : correct C) : ∃ a b : List Bool,
    a.length=projection.length ∧ b.length=projection.length ∧
      (∀ i,i≠2 → a.getD i false=b.getD i false) ∧ C.eval a ≠ C.eval b := by
  refine ⟨List.ofFn (assignment 16),List.ofFn (assignment 20),rfl,rfl,?_,?_⟩
  · intro i hi
    by_cases h : i<7
    · interval_cases i <;> first | contradiction | decide
    · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]
  · change computes C (assignment 16) ≠ computes C (assignment 20)
    rw [hc,hc];decide +kernel

theorem nonconstant_image (C : Circuit) (hc : correct C) :
    ∃ x y, C.eval (proj projection x) ≠ C.eval (proj projection y) := by
  refine ⟨fun _ => false,fun _ => true,?_⟩
  rw [lifted_list,lifted_list]
  change computes C _ ≠ computes C _
  rw [hc,hc,lifted_target,lifted_target];decide +kernel

theorem floor (C : Circuit) (hf : FanInTwo C) (hc : correct C) (b : Nat) (small : b≤1)
    (blocked : b=1 → ∀ g∈C.gates, g.op=.or → 2∉g.inputs) : 10+(b+1) ≤ C.size := by
  obtain ⟨D,df,ds,de⟩ := PEqualNP.Outside.L_meta_3223 5 C projection 2 b hf rfl small blocked
    (changes C hc) (nonconstant_image C hc)
  have cmp : HasCircuitSize 5 PEqualNP.Outside.L_meta_5459.T25 D.size := by
    refine ⟨D,df,le_rfl,fun x => ?_⟩
    rw [de]
    change C.eval (proj projection x)=_
    rw [lifted_list]
    exact (hc _).trans (lifted_target x)
  have m := PEqualNP.Outside.L_meta_5459.main _ cmp
  omega

theorem lower_eleven (C : Circuit) (hf : FanInTwo C) (hc : correct C) : 11 ≤ C.size :=
  floor C hf hc 0 (by decide) (by intro h;omega)

theorem eleven_reads_or (C : Circuit) (hf : FanInTwo C) (hc : correct C) (size : C.size=11) :
    ∃ g ∈ C.gates,g.op=.or ∧ 2∈g.inputs := by
  by_contra! bad
  have b := floor C hf hc 1 (by decide) (fun _ => bad)
  omega
end Seven10726

namespace Seven10726
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Residual (gs : List Gate) (o : Nat) :=
    (gs.length=11 ∨ gs.length=12) ∧
    gs.countP Unfold.binaryGateOp < (Unfold.unfoldCircuit gs o).binary ∧
    (gs.length=11 → ∃ g∈gs,g.op=.or ∧ 2∈g.inputs) ∧
    ∃ pre post ls, gs=pre++⟨.not,ls⟩::post ∧ AO pre ∧ AO post ∧
      ∀ g, AOgate g → ¬demands pre post o (signal pre g)

theorem failure_shape {gs o} (hf : legal gs) (hu : uniqueNot gs) (hc : correct ⟨gs,o⟩)
    (fail : ¬replacement gs) : Residual gs o := by
  let C : Circuit := ⟨gs,o⟩
  have fan : FanInTwo C := by
    intro g hg
    have h := hf g hg
    exact ⟨by simpa using h.1,h.2⟩
  have lower := lower_eleven C fan hc
  change 11 ≤ gs.length at lower
  obtain ⟨upper,rest⟩ := remaining hf hu hc fail
  exact ⟨by omega,Unfold.shared_required hf hu hc fail,fun h => eleven_reads_or C fan hc h,rest⟩

theorem complete_if (h : ∀ gs o, legal gs → uniqueNot gs → correct ⟨gs,o⟩ → Residual gs o → replacement gs)
    {gs o} (hf : legal gs) (hu : uniqueNot gs) (hc : correct ⟨gs,o⟩) : replacement gs := by
  by_contra fail
  exact fail (h gs o hf hu hc (failure_shape hf hu hc fail))

end Seven10726
#print axioms Seven10726.large
#print axioms Seven10726.lower_eleven
#print axioms Seven10726.Weight.lower
#print axioms Seven10726.Unfold.actual_binary_lower
#print axioms Seven10726.rewrite_iff
#print axioms Seven10726.failure_shape
#print axioms Seven10726.complete_if
