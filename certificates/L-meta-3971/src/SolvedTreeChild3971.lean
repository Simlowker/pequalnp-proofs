import FirstChildFromTree3971
import TreeLower3971
namespace PetersenNegated3971
theorem solved_tree_child : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → let init : List (Nat × Nat) := List.replicate 10 (1,0)
    let ws := C.gates.foldl (fun (s : List (Nat × Nat)) g =>
      let col := fun j => (g.inputs[j]?.bind fun i => s[i]?).getD (1,0)
      let a := col 0
      let b := col 1
      s ++ [ite (g.op.eval [false]=true) (a.1,a.2+1) (a.1+b.1,a.2+b.2)]) init
    let z := ws.getD C.output (1,0)
    z.2≤1 → z.1+z.2≤15 → ∃ r : Nat, r<512 ∧ C.eval ((([1,0,4,7,5,2,8,6,3] : List Nat).map (fun i => r.testBit i)) ++ [r.testBit 1 || r.testBit 8]) ≠ (13407807929942597095939831376727811673905304651018912648022854022873869787405066962725179222507908767667956533170508564710083788841651696458571261487544520 : Nat).testBit r := first_child_given3971 tree_lower
#print axioms solved_tree_child
end PetersenNegated3971
