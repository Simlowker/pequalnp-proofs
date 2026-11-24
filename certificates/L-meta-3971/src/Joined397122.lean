import Joins397122Part00
import Joins397122Part01
import Joins397122Part02
import Joins397122Part03
namespace PetersenNegated3971
theorem joined22 : universalJoin 2 2 := by
  apply joinsTo 2 2 (by decide)
  intro q hq
  change q<7056 at hq
  by_cases h0 : q<2048
  · let r : Fin 2048 := ⟨q-0,by omega⟩
    have e : 0+r.val=q := by dsimp [r]; omega
    exact ⟨witness22p0 r.val,e ▸ witness22p0ok r⟩
  by_cases h1 : q<4096
  · let r : Fin 2048 := ⟨q-2048,by omega⟩
    have e : 2048+r.val=q := by dsimp [r]; omega
    exact ⟨witness22p1 r.val,e ▸ witness22p1ok r⟩
  by_cases h2 : q<6144
  · let r : Fin 2048 := ⟨q-4096,by omega⟩
    have e : 4096+r.val=q := by dsimp [r]; omega
    exact ⟨witness22p2 r.val,e ▸ witness22p2ok r⟩
  let r : Fin 912 := ⟨q-6144,by omega⟩
  have e : 6144+r.val=q := by dsimp [r]; omega
  exact ⟨witness22p3 r.val,e ▸ witness22p3ok r⟩
end PetersenNegated3971
