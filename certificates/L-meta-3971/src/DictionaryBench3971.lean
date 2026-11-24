import Dictionary3971
namespace PetersenNegated3971
def pairOK (k a b : Nat) : Bool := let u := wOf (smallId a); let v := wOf (smallId b)
  present k (u &&& v) && present k (u ||| v)
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem atoms_ok : ∀ j : Fin 13, present 1 (rawWords.getD j.val 0)=true := by decide +kernel
set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
theorem first_join : ∀ a b : Fin 12, pairOK 2 a.val b.val=true := by decide +kernel
end PetersenNegated3971
