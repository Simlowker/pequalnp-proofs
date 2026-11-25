import TightIncidence3722
namespace IncidenceBudget
open PEqualNP.MetaComplexity.NestedCover

-- Fix an outside input. A monotone computation that sees the inside only
-- through one Boolean signal is constant, or is the signal itself.
theorem unary_id (h : Bool → Bool) (nz : h false ≠ h true) (mono : h false=true → h true=true) :
    h=id := by
  funext b
  cases a : h false <;> cases c : h true <;> cases b <;> simp_all

def restrictTo {n : Nat} (S : Finset (Fin n)) (x : Fin n → Bool) (i : Fin n) :=
  x i && decide (i∈S)
def exterior {n : Nat} (S : Finset (Fin n)) (x : Fin n → Bool) (i : Fin n) :=
  x i && decide (i∉S)

def OnePort {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) :=
  ∃ (z : (Fin n → Bool) → Bool) (h : (Fin n → Bool) → Bool → Bool),
    (∀ y, h y false=true → h y true=true) ∧
    ∀ x, graphFun G ∅ x = h (exterior S x) (z (restrictTo S x))

def combine {n : Nat} (S : Finset (Fin n)) (i o : Fin n → Bool) (v : Fin n) :=
  if v∈S then i v else o v

theorem port_cofactor {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {S : Finset (Fin n)}
    (port : OnePort G S) (a b : Fin n → Bool)
    (ca : ∃ i j, graphFun G ∅ (combine S i a)≠graphFun G ∅ (combine S j a))
    (cb : ∃ i j, graphFun G ∅ (combine S i b)≠graphFun G ∅ (combine S j b)) :
    ∀ i, graphFun G ∅ (combine S i a)=graphFun G ∅ (combine S i b) := by
  obtain ⟨z,h,m,rep⟩ := port
  have fg (i o) : graphFun G ∅ (combine S i o)=h (exterior S o) (z (restrictTo S i)) := by
    rw [rep]
    congr 1
    · funext v; by_cases hv : v∈S <;> simp [exterior,combine,hv]
    · congr 1; funext v; by_cases hv : v∈S <;> simp [restrictTo,combine,hv]
  have idAt (o : Fin n → Bool) (varies : ∃ i j, graphFun G ∅ (combine S i o)≠graphFun G ∅ (combine S j o)) :
      h (exterior S o)=id := by
    obtain ⟨i,j,ne⟩ := varies
    rw [fg,fg] at ne
    apply unary_id _ _ (m _)
    by_contra eq
    cases h1 : z (restrictTo S i) <;> cases h2 : z (restrictTo S j) <;> simp_all
  intro i
  rw [fg,fg,idAt a ca,idAt b cb]

theorem graph_pair {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a b : Fin n) :
    graphFun G ∅ (fun k => (k==a) || (k==b)) = decide (G.Adj a b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq,
    Bool.or_eq_true_iff,beq_iff_eq]
  constructor
  · rintro ⟨v,w,e,hv,hw⟩
    rcases hv with rfl|rfl <;> rcases hw with rfl|rfl <;> first | exact e | exact e.symm | exact False.elim (G.irrefl e)
  · intro e; exact ⟨a,b,e,Or.inl rfl,Or.inr rfl⟩

theorem port_separates {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {S : Finset (Fin n)}
    (port : OnePort G S) {a b : Fin n} (ha : a∈S) (hb : b∈S) (edge : G.Adj a b)
    {u v : Fin n} (hu : u∈S) (hv : v∉S) : ¬G.Adj u v := by
  intro cross
  let O : Fin n → Bool := fun _ => false
  let sing (i : Fin n) : Fin n → Bool := fun j => j==i
  let dbl (i j : Fin n) : Fin n → Bool := fun k => (k==i) || (k==j)
  have sep (x y : Fin n → Bool) (sx : ∀ j,x j=true → j∈S) (sy : ∀ j,y j=true → j∉S) :
      combine S x y = fun j => x j || y j := by
    funext j
    by_cases hj : j∈S
    · have e : y j=false := by cases h : y j <;> simp_all
      simp [combine,hj,e]
    · have e : x j=false := by cases h : x j <;> simp_all
      simp [combine,hj,e]
  have s0 : ∀ j,O j=true → j∈S := by simp [O]
  have o0 : ∀ j,O j=true → j∉S := by simp [O]
  have ou : ∀ j,sing u j=true → j∈S := by simpa [sing] using hu
  have ov : ∀ j,sing v j=true → j∉S := by simpa [sing] using hv
  have sab : ∀ j,dbl a b j=true → j∈S := by
    intro j h
    rcases Bool.or_eq_true_iff.mp h with l|r
    · exact beq_iff_eq.mp l ▸ ha
    · exact beq_iff_eq.mp r ▸ hb
  have off (t : Fin n) : graphFun G ∅ (sing t)=false := by
    have e := graph_pair G t t
    simp [sing] at e ⊢
    exact e
  have f00 : graphFun G ∅ (combine S O O)=false := by simp [combine,O,graphFun]
  have fab : graphFun G ∅ (combine S (dbl a b) O)=true := by
    rw [sep _ _ sab o0]; simpa [O,dbl] using (graph_pair G a b).trans (decide_eq_true edge)
  have f0v : graphFun G ∅ (combine S O (sing v))=false := by
    rw [sep _ _ s0 ov]; simpa [O] using off v
  have fuv : graphFun G ∅ (combine S (sing u) (sing v))=true := by
    rw [sep _ _ ou ov]; exact (graph_pair G u v).trans (decide_eq_true cross)
  have fu0 : graphFun G ∅ (combine S (sing u) O)=false := by
    rw [sep _ _ ou o0]; simpa [O] using off u
  have eq := port_cofactor port O (sing v) ⟨O,dbl a b,by rw [f00,fab]; decide⟩ ⟨O,sing u,by rw [f0v,fuv]; decide⟩ (sing u)
  rw [fu0,fuv] at eq
  contradiction

#print axioms port_separates
end IncidenceBudget
