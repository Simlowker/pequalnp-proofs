import Mathlib
import PEqualNP.Defs

namespace Simlowker.Pigeon179.TreeBounds
open PEqualNP.ProofComplexity

abbrev V := Fin 5 × Fin 4
abbrev LC := LinClause V
abbrev F := (fun C => linOfClause C) '' PHP 5 4
inductive Tree : LC → Type where
  | ax (C : LC) (h : C∈F) : Tree C
  | weak {C D : LC} (t : Tree C) (h : ∀ a, LinClauseSat a C → LinClauseSat a D) : Tree D
  | res {C D R : LC} (l : Tree C) (r : Tree D) (h : IsLinResolvent C D R) : Tree R
def Tree.leaves {C : LC} : Tree C → Nat
  | .ax .. => 1
  | .weak t _ => t.leaves
  | .res l r _ => l.leaves+r.leaves
def Tree.size {C : LC} : Tree C → Nat
  | .ax .. => 1
  | .weak t _ => t.size+1
  | .res l r _ => l.size+r.size+1
theorem leaf_cost {C : LC} (t : Tree C) : 2*t.leaves ≤ t.size+1 := by
  induction t <;> simp only [Tree.size,Tree.leaves] at * <;> omega

theorem resolve_false {C D R : LC} (p : IsLinResolvent C D R) (a : V → Bool) (no : ¬LinClauseSat a R) :
    ¬LinClauseSat a C ∨ ¬LinClauseSat a D := by
  obtain ⟨f,hf,hg,rfl⟩ := p
  by_contra! yes
  obtain ⟨u,hu,su⟩ := yes.1
  obtain ⟨v,hv,sv⟩ := yes.2
  by_cases eu : u=(f,false)
  · by_cases ev : v=(f,true)
    · subst u;subst v;exact Bool.noConfusion (su.mp (sv.mpr rfl))
    · exact no ⟨v,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨ev,hv⟩),sv⟩
  · exact no ⟨u,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eu,hu⟩),su⟩

theorem fork_bad {f : Finset V} {C D : LC} (h : ∀ a, ¬LinClauseSat a (C.erase (f,false) ∪ D.erase (f,true))) :
    (∀ a, Odd (f.filter (fun v => a v=true)).card → ¬LinClauseSat a C) ∧
    (∀ a, ¬Odd (f.filter (fun v => a v=true)).card → ¬LinClauseSat a D) := by
  constructor
  · rintro a par ⟨q,hq,sat⟩
    by_cases e : q=(f,false)
    · exact Bool.noConfusion ((e ▸ sat).mp par)
    · exact h a ⟨q,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hq⟩),sat⟩
  · rintro a par ⟨q,hq,sat⟩
    by_cases e : q=(f,true)
    · exact par ((e ▸ sat).mpr rfl)
    · exact h a ⟨q,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨e,hq⟩),sat⟩


def Tree.axioms {C : LC} : Tree C → List LC
  | .ax c _ => [c]
  | .weak t _ => t.axioms
  | .res l r _ => l.axioms ++ r.axioms

theorem axioms_length {C : LC} (t : Tree C) : t.axioms.length = t.leaves := by
  induction t <;> simp_all [Tree.axioms, Tree.leaves]

theorem axioms_mem {C : LC} (t : Tree C) : ∀ c ∈ t.axioms, c ∈ F := by
  induction t with
  | ax c h => simpa [Tree.axioms] using h
  | weak t h ih => exact ih
  | res l r h il ir =>
    intro c mem
    exact (List.mem_append.mp mem).elim (il c) (ir c)

theorem axioms_cover {C : LC} (t : Tree C) (a : V → Bool) (no : ¬LinClauseSat a C) :
    ∃ c ∈ t.axioms, ¬LinClauseSat a c := by
  induction t with
  | ax c h => exact ⟨c, List.mem_cons_self, no⟩
  | weak t h ih => exact ih (fun hc => no (h a hc))
  | res l r h il ir =>
    rcases resolve_false h a no with nl | nr
    · obtain ⟨c, mem, bad⟩ := il nl
      exact ⟨c, List.mem_append_left _ mem, bad⟩
    · obtain ⟨c, mem, bad⟩ := ir nr
      exact ⟨c, List.mem_append_right _ mem, bad⟩

/-- Each list covers its half of the assignment cube with falsified PHP axioms. -/
def RootBudget (n : Nat) : Prop :=
  ∀ (f : Finset V), f.Nonempty → ∀ (left right : List LC),
    (∀ c ∈ left, c ∈ F) → (∀ c ∈ right, c ∈ F) →
    (∀ a : V → Bool, Odd (f.filter (fun v => a v = true)).card →
      ∃ c ∈ left, ¬LinClauseSat a c) →
    (∀ a : V → Bool, ¬Odd (f.filter (fun v => a v = true)).card →
      ∃ c ∈ right, ¬LinClauseSat a c) →
    n ≤ left.length + right.length

theorem leaves_lower {n : Nat} (budget : RootBudget n) {C : LC} (t : Tree C)
    (no : ∀ a, ¬LinClauseSat a C) : n ≤ t.leaves := by
  induction t with
  | ax c h =>
    obtain ⟨d, hd, rfl⟩ := h
    rcases hd with ⟨i, rfl⟩ | ⟨i, j, k, ne, rfl⟩
    · exact False.elim (no (fun _ => true)
        ⟨({(i,0)},true), by simp [linOfClause], by simp [LinEqSat]⟩)
    · exact False.elim (no (fun _ => false)
        ⟨({(i,k)},false), by simp [linOfClause], by simp [LinEqSat]⟩)
  | weak t h ih => exact ih (fun a hc => no a (h a hc))
  | @res c d r l t h il ir =>
    obtain ⟨f, hc, hd, rfl⟩ := h
    have fork := fork_bad no
    by_cases empty : f = ∅
    · subst f
      have lower := ir (fun a => fork.2 a (by simp))
      change n ≤ l.leaves + t.leaves
      omega
    · have lower := budget f (Finset.nonempty_iff_ne_empty.mpr empty) l.axioms t.axioms
          (axioms_mem l) (axioms_mem t) (fun a ha => axioms_cover l a (fork.1 a ha))
          (fun a ha => axioms_cover t a (fork.2 a ha))
      simpa [axioms_length, Tree.leaves] using lower

theorem size_lower (budget : RootBudget 67) (t : Tree ∅) : 133 ≤ t.size := by
  have := leaves_lower budget t (by simp [LinClauseSat])
  have := leaf_cost t
  omega
def Tree.lines {C : LC} : Tree C → List LC
  | .ax c _ => [c]
  | @Tree.weak _ d t _ => d::t.lines
  | @Tree.res _ _ r l t _ => r::(l.lines++t.lines)
theorem extract {π : List LC} (h : IsLinDerivation F π) :
    ∀ C∈π, ∃ t : Tree C, ∀ d∈t.lines, d∈π := by
  induction h with
  | nil => simp
  | ax prev orig ih =>
    intro C hc
    rcases List.mem_cons.mp hc with rfl|prior
    · exact ⟨Tree.ax _ orig,by simp [Tree.lines]⟩
    · obtain ⟨t,ht⟩ := ih _ prior
      exact ⟨t,fun d hd => List.mem_cons_of_mem _ (ht d hd)⟩
  | weak prev source imp ih =>
    intro C hc
    rcases List.mem_cons.mp hc with rfl|prior
    · obtain ⟨t,ht⟩ := ih _ source
      refine ⟨Tree.weak t imp,fun d hd => ?_⟩
      exact (List.mem_cons.mp hd).elim (fun e => e ▸ List.mem_cons_self) (fun a => List.mem_cons_of_mem _ (ht d a))
    · obtain ⟨t,ht⟩ := ih _ prior
      exact ⟨t,fun d hd => List.mem_cons_of_mem _ (ht d hd)⟩
  | res prev left right rule ih =>
    intro C hc
    rcases List.mem_cons.mp hc with rfl|prior
    · obtain ⟨l,hl⟩ := ih _ left
      obtain ⟨r,hr⟩ := ih _ right
      refine ⟨Tree.res l r rule,fun d hd => ?_⟩
      rcases List.mem_cons.mp hd with e|child
      · exact e ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ ((List.mem_append.mp child).elim (hl d) (hr d))
    · obtain ⟨t,ht⟩ := ih _ prior
      exact ⟨t,fun d hd => List.mem_cons_of_mem _ (ht d hd)⟩


theorem expansion (budget : RootBudget 67) {π : List LC}
    (p : IsLinRefutation (PHP 5 4) π) (short : π.length ≤ 123) :
    ∃ t : Tree ∅, (∀ C ∈ t.lines, C ∈ π) ∧ π.length + 10 ≤ t.size := by
  obtain ⟨t, uses⟩ := extract p.1 ∅ p.2
  exact ⟨t, uses, by have := size_lower budget t; omega⟩

#print axioms expansion
end Simlowker.Pigeon179.TreeBounds
