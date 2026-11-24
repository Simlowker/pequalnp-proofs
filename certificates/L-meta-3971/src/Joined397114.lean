import Joins397114Part00
import Joins397114Part01
import Joins397114Part02
import Joins397114Part03
import Joins397114Part04
import Joins397114Part05
import Joins397114Part06
import Joins397114Part07
import Joins397114Part08
import Joins397114Part09
import Joins397114Part10
import Joins397114Part11
import Joins397114Part12
import Joins397114Part13
import Joins397114Part14
import Joins397114Part15
import Joins397114Part16
import Joins397114Part17
import Joins397114Part18
import Joins397114Part19
import Joins397114Part20
namespace PetersenNegated3971
theorem joined14 : universalJoin 1 4 := by
  apply joinsTo 1 4 (by decide)
  intro q hq
  change q<41160 at hq
  by_cases h0 : q<2048
  · let r : Fin 2048 := ⟨q-0,by omega⟩
    have e : 0+r.val=q := by dsimp [r]; omega
    exact ⟨witness14p0 r.val,e ▸ witness14p0ok r⟩
  by_cases h1 : q<4096
  · let r : Fin 2048 := ⟨q-2048,by omega⟩
    have e : 2048+r.val=q := by dsimp [r]; omega
    exact ⟨witness14p1 r.val,e ▸ witness14p1ok r⟩
  by_cases h2 : q<6144
  · let r : Fin 2048 := ⟨q-4096,by omega⟩
    have e : 4096+r.val=q := by dsimp [r]; omega
    exact ⟨witness14p2 r.val,e ▸ witness14p2ok r⟩
  by_cases h3 : q<8192
  · let r : Fin 2048 := ⟨q-6144,by omega⟩
    have e : 6144+r.val=q := by dsimp [r]; omega
    exact ⟨witness14p3 r.val,e ▸ witness14p3ok r⟩
  by_cases h4 : q<10240
  · let r : Fin 2048 := ⟨q-8192,by omega⟩
    have e : 8192+r.val=q := by dsimp [r]; omega
    exact ⟨witness14p4 r.val,e ▸ witness14p4ok r⟩
  by_cases h5 : q<12288
  · let r : Fin 2048 := ⟨q-10240,by omega⟩
    have e : 10240+r.val=q := by dsimp [r]; omega
    exact ⟨witness14p5 r.val,e ▸ witness14p5ok r⟩
  by_cases h6 : q<14336
  · let r : Fin 2048 := ⟨q-12288,by omega⟩
    have e : 12288+r.val=q := by dsimp [r]; omega
    exact ⟨witness14p6 r.val,e ▸ witness14p6ok r⟩
  by_cases h7 : q<16384
  · let r : Fin 2048 := ⟨q-14336,by omega⟩
    have e : 14336+r.val=q := by dsimp [r]; omega
    exact ⟨witness14p7 r.val,e ▸ witness14p7ok r⟩
  by_cases h8 : q<18432
  · let r : Fin 2048 := ⟨q-16384,by omega⟩
    have e : 16384+r.val=q := by dsimp [r]; omega
    exact ⟨witness14p8 r.val,e ▸ witness14p8ok r⟩
  by_cases h9 : q<20480
  · let r : Fin 2048 := ⟨q-18432,by omega⟩
    have e : 18432+r.val=q := by dsimp [r]; omega
    exact ⟨witness14p9 r.val,e ▸ witness14p9ok r⟩
  by_cases h10 : q<22528
  · let r : Fin 2048 := ⟨q-20480,by omega⟩
    have e : 20480+r.val=q := by dsimp [r]; omega
    exact ⟨witness14p10 r.val,e ▸ witness14p10ok r⟩
  by_cases h11 : q<24576
  · let r : Fin 2048 := ⟨q-22528,by omega⟩
    have e : 22528+r.val=q := by dsimp [r]; omega
    exact ⟨witness14p11 r.val,e ▸ witness14p11ok r⟩
  by_cases h12 : q<26624
  · let r : Fin 2048 := ⟨q-24576,by omega⟩
    have e : 24576+r.val=q := by dsimp [r]; omega
    exact ⟨witness14p12 r.val,e ▸ witness14p12ok r⟩
  by_cases h13 : q<28672
  · let r : Fin 2048 := ⟨q-26624,by omega⟩
    have e : 26624+r.val=q := by dsimp [r]; omega
    exact ⟨witness14p13 r.val,e ▸ witness14p13ok r⟩
  by_cases h14 : q<30720
  · let r : Fin 2048 := ⟨q-28672,by omega⟩
    have e : 28672+r.val=q := by dsimp [r]; omega
    exact ⟨witness14p14 r.val,e ▸ witness14p14ok r⟩
  by_cases h15 : q<32768
  · let r : Fin 2048 := ⟨q-30720,by omega⟩
    have e : 30720+r.val=q := by dsimp [r]; omega
    exact ⟨witness14p15 r.val,e ▸ witness14p15ok r⟩
  by_cases h16 : q<34816
  · let r : Fin 2048 := ⟨q-32768,by omega⟩
    have e : 32768+r.val=q := by dsimp [r]; omega
    exact ⟨witness14p16 r.val,e ▸ witness14p16ok r⟩
  by_cases h17 : q<36864
  · let r : Fin 2048 := ⟨q-34816,by omega⟩
    have e : 34816+r.val=q := by dsimp [r]; omega
    exact ⟨witness14p17 r.val,e ▸ witness14p17ok r⟩
  by_cases h18 : q<38912
  · let r : Fin 2048 := ⟨q-36864,by omega⟩
    have e : 36864+r.val=q := by dsimp [r]; omega
    exact ⟨witness14p18 r.val,e ▸ witness14p18ok r⟩
  by_cases h19 : q<40960
  · let r : Fin 2048 := ⟨q-38912,by omega⟩
    have e : 38912+r.val=q := by dsimp [r]; omega
    exact ⟨witness14p19 r.val,e ▸ witness14p19ok r⟩
  let r : Fin 200 := ⟨q-40960,by omega⟩
  have e : 40960+r.val=q := by dsimp [r]; omega
  exact ⟨witness14p20 r.val,e ▸ witness14p20ok r⟩
end PetersenNegated3971
