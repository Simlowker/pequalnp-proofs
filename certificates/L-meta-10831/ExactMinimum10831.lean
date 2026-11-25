import Rechecked10830
namespace Simlowker10831
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[⟨.or,[4,6]⟩, ⟨.or,[9,7]⟩, ⟨.and,[0,10]⟩, ⟨.or,[5,6]⟩, ⟨.and,[1,12]⟩, ⟨.or,[6,8]⟩, ⟨.and,[2,14]⟩, ⟨.or,[3,4]⟩, ⟨.and,[7,16]⟩, ⟨.or,[3,5]⟩, ⟨.and,[8,18]⟩, ⟨.or,[11,13]⟩, ⟨.or,[20,15]⟩, ⟨.or,[21,17]⟩, ⟨.or,[22,19]⟩],23⟩
theorem upper : HasCircuitSize 9 PEqualNP.Outside.L_meta_10830.edge 15 := by
  refine ⟨witness,?_,by decide,?_⟩
  · intro g hg
    simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel

theorem exact_minimum (t : Nat) :
    HasCircuitSize 9 PEqualNP.Outside.L_meta_10830.edge t ↔ 15 ≤ t := by
  constructor
  · exact PEqualNP.Outside.L_meta_10830 t
  · intro enough
    obtain ⟨C, legal, cost, computes⟩ := upper
    exact ⟨C, legal, cost.trans enough, computes⟩

theorem no_fourteen : ¬ HasCircuitSize 9 PEqualNP.Outside.L_meta_10830.edge 14 := by
  intro h
  have impossible := (exact_minimum 14).mp h
  omega
#print axioms exact_minimum
#print axioms no_fourteen
end Simlowker10831
