import Mathlib.Tactic
namespace IncidenceBudget

abbrev Sig := Finset Nat × Nat
def join (a b : Sig) : Sig := (a.1 ∪ b.1,a.2+b.2)
def cover (A : Finset Sig) := A.biUnion Prod.fst
def cost (A : Finset Sig) := ∑ a ∈ A, a.2

def Budget (k : Nat) (P : Finset Sig) := ∀ A ⊆ P,
  (cover A).card ≤ k+A.card ∧ (k+A.card ≤ (cover A).card → cost A ≤ (cover A).card)

theorem initial {P : Finset Sig} (base : ∀ a∈P, a.1.card≤a.2 ∧ a.2≤1) : Budget 0 P := by
  intro A h
  have x : (cover A).card≤cost A := Finset.card_biUnion_le.trans (Finset.sum_le_sum fun a ha => (base a (h ha)).1)
  have y : cost A ≤ A.card := by
    calc
      (∑ a ∈ A, a.2) ≤ ∑ _a ∈ A, 1 := Finset.sum_le_sum (fun a ha => (base a (h ha)).2)
      _ = A.card := by simp
  constructor
  · exact x.trans (by omega)
  · omega

theorem extend {P : Finset Sig} {k : Nat} (h : Budget k P) {a b : Sig}
    (ha : a∈P) (hb : b∈P) : Budget (k+1) (insert (join a b) P) := by
  intro A sub
  let c := join a b
  by_cases hc : c∈A
  · let B := A.erase c
    let Q := insert a (insert b B)
    have Bsub : B⊆P := by
      intro v hv
      have hh := sub (Finset.mem_erase.mp hv).2
      simpa [c,(Finset.mem_erase.mp hv).1] using hh
    have Qsub : Q⊆P := Finset.insert_subset ha (Finset.insert_subset hb Bsub)
    have ce : insert c B=A := Finset.insert_erase hc
    have ne : c∉B := Finset.notMem_erase _ _
    have eq : cover A=cover Q := by
      rw [←ce]
      simp [cover,Q,c,join,Finset.union_assoc]
    have cb : A.card=B.card+1 := by rw [←ce,Finset.card_insert_of_notMem ne]
    have bound := h Q Qsub
    have upper : Q.card ≤ B.card+2 := by
      have := Finset.card_insert_le a (insert b B)
      have := Finset.card_insert_le b B
      dsimp [Q]; omega
    rw [eq]
    constructor
    · omega
    · intro tight
      have separate : a∉insert b B := by
        intro bad
        have same : Q=insert b B := Finset.insert_eq_of_mem bad
        have small := Finset.card_insert_le b B
        rw [same] at bound tight
        omega
      have single : b∉B := by
        intro bad
        have same : Q=insert a B := by simp [Q,Finset.insert_eq_of_mem bad]
        have small := Finset.card_insert_le a B
        rw [same] at bound tight
        omega
      have costs : cost A=cost Q := by
        rw [←ce]
        unfold cost
        rw [Finset.sum_insert ne]
        dsimp only [Q]
        rw [Finset.sum_insert separate,Finset.sum_insert single]
        change a.2+b.2+_=a.2+(b.2+_)
        omega
      rw [costs]
      apply bound.2
      omega
  · have sub' : A⊆P := by
      intro v hv
      rcases Finset.mem_insert.mp (sub hv) with e|h'
      · exact False.elim (hc (by simpa [c,e] using hv))
      · exact h'
    have hh := (h A sub').1
    exact ⟨by omega,by omega⟩

#print axioms extend
end IncidenceBudget
