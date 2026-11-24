import Joins397111Part00
namespace PetersenNegated3971
theorem joined11 : universalJoin 1 1 := by
  apply joinsTo 1 1 (by decide)
  intro q hq
  change q<144 at hq
  let r : Fin 144 := ⟨q-0,by omega⟩
  have e : 0+r.val=q := by dsimp [r]; omega
  exact ⟨witness11p0 r.val,e ▸ witness11p0ok r⟩
end PetersenNegated3971
