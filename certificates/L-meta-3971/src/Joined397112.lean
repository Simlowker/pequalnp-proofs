import Joins397112Part00
namespace PetersenNegated3971
theorem joined12 : universalJoin 1 2 := by
  apply joinsTo 1 2 (by decide)
  intro q hq
  change q<1008 at hq
  let r : Fin 1008 := ⟨q-0,by omega⟩
  have e : 0+r.val=q := by dsimp [r]; omega
  exact ⟨witness12p0 r.val,e ▸ witness12p0ok r⟩
end PetersenNegated3971
