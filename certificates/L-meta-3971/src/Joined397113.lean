import Joins397113Part00
import Joins397113Part01
import Joins397113Part02
import Joins397113Part03
namespace PetersenNegated3971
theorem joined13 : universalJoin 1 3 := by
  apply joinsTo 1 3 (by decide)
  intro q hq
  change q<7716 at hq
  by_cases h0 : q<2048
  · let r : Fin 2048 := ⟨q-0,by omega⟩
    have e : 0+r.val=q := by dsimp [r]; omega
    exact ⟨witness13p0 r.val,e ▸ witness13p0ok r⟩
  by_cases h1 : q<4096
  · let r : Fin 2048 := ⟨q-2048,by omega⟩
    have e : 2048+r.val=q := by dsimp [r]; omega
    exact ⟨witness13p1 r.val,e ▸ witness13p1ok r⟩
  by_cases h2 : q<6144
  · let r : Fin 2048 := ⟨q-4096,by omega⟩
    have e : 4096+r.val=q := by dsimp [r]; omega
    exact ⟨witness13p2 r.val,e ▸ witness13p2ok r⟩
  let r : Fin 1572 := ⟨q-6144,by omega⟩
  have e : 6144+r.val=q := by dsimp [r]; omega
  exact ⟨witness13p3 r.val,e ▸ witness13p3ok r⟩
end PetersenNegated3971
