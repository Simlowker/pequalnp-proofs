import PEqualNP.Outside.L_meta_16755
import FormulaProfiles
import Depth
namespace Simlowker.Function16756
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_16755

theorem balanced_legal : FanInTwo balanced := by
  intro g hg
  obtain ⟨mem,arity⟩ := monotone g hg
  refine ⟨?_,arity⟩
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at mem ⊢
  exact mem.elim Or.inl (fun h => Or.inr (Or.inl h))

theorem minimum_binary_gates (k : Nat) :
    (∃ C : Circuit, FanInTwo C ∧
      C.gates.countP (fun g => !Model.isNot g) ≤ k ∧
      ∀ x, C.eval (List.ofFn x) = target x) ↔ 10 ≤ k := by
  constructor
  · rintro ⟨⟨gs,out⟩,fit,cost,ok⟩
    exact (binaryLower (fullBound allgb) gs out fit ok).trans cost
  · intro h
    exact ⟨balanced, balanced_legal, h, balanced_eval⟩

theorem minimum_total_gates (k : Nat) : HasCircuitSize 6 target k ↔ 10 ≤ k := by
  constructor
  · rintro ⟨⟨gs,out⟩,fit,cost,ok⟩
    exact (binaryLower (fullBound allgb) gs out fit ok).trans (List.countP_le_length.trans cost)
  · intro h
    exact ⟨balanced, balanced_legal, h, balanced_eval⟩

#print axioms minimum_binary_gates
#print axioms minimum_total_gates
theorem minimum_circuit_depth (k : Nat) :
    (∃ C : Circuit, FanInTwo C ∧ C.depth 6 ≤ k ∧ ∀ x, C.eval (List.ofFn x) = target x) ↔ 4 ≤ k := by
  constructor
  · rintro ⟨C,fit,le,ok⟩
    exact (Simlowker.Depth16756.circuit_depth_at_least_four C fit ok).trans le
  · intro h
    exact ⟨balanced,balanced_legal,bounds.2.trans_le h,balanced_eval⟩

#print axioms minimum_circuit_depth
end Simlowker.Function16756
