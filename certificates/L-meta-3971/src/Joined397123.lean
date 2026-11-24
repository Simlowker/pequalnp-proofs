import Joins397123Part00
import Joins397123Part01
import Joins397123Part02
import Joins397123Part03
import Joins397123Part04
import Joins397123Part05
import Joins397123Part06
import Joins397123Part07
import Joins397123Part08
import Joins397123Part09
import Joins397123Part10
import Joins397123Part11
import Joins397123Part12
import Joins397123Part13
import Joins397123Part14
import Joins397123Part15
import Joins397123Part16
import Joins397123Part17
import Joins397123Part18
import Joins397123Part19
import Joins397123Part20
import Joins397123Part21
import Joins397123Part22
import Joins397123Part23
import Joins397123Part24
import Joins397123Part25
import Joins397123Part26
namespace PetersenNegated3971
theorem joined23 : universalJoin 2 3 := by
  apply joinsTo 2 3 (by decide)
  intro q hq
  change q<54012 at hq
  by_cases h0 : q<2048
  · let r : Fin 2048 := ⟨q-0,by omega⟩
    have e : 0+r.val=q := by dsimp [r]; omega
    exact ⟨witness23p0 r.val,e ▸ witness23p0ok r⟩
  by_cases h1 : q<4096
  · let r : Fin 2048 := ⟨q-2048,by omega⟩
    have e : 2048+r.val=q := by dsimp [r]; omega
    exact ⟨witness23p1 r.val,e ▸ witness23p1ok r⟩
  by_cases h2 : q<6144
  · let r : Fin 2048 := ⟨q-4096,by omega⟩
    have e : 4096+r.val=q := by dsimp [r]; omega
    exact ⟨witness23p2 r.val,e ▸ witness23p2ok r⟩
  by_cases h3 : q<8192
  · let r : Fin 2048 := ⟨q-6144,by omega⟩
    have e : 6144+r.val=q := by dsimp [r]; omega
    exact ⟨witness23p3 r.val,e ▸ witness23p3ok r⟩
  by_cases h4 : q<10240
  · let r : Fin 2048 := ⟨q-8192,by omega⟩
    have e : 8192+r.val=q := by dsimp [r]; omega
    exact ⟨witness23p4 r.val,e ▸ witness23p4ok r⟩
  by_cases h5 : q<12288
  · let r : Fin 2048 := ⟨q-10240,by omega⟩
    have e : 10240+r.val=q := by dsimp [r]; omega
    exact ⟨witness23p5 r.val,e ▸ witness23p5ok r⟩
  by_cases h6 : q<14336
  · let r : Fin 2048 := ⟨q-12288,by omega⟩
    have e : 12288+r.val=q := by dsimp [r]; omega
    exact ⟨witness23p6 r.val,e ▸ witness23p6ok r⟩
  by_cases h7 : q<16384
  · let r : Fin 2048 := ⟨q-14336,by omega⟩
    have e : 14336+r.val=q := by dsimp [r]; omega
    exact ⟨witness23p7 r.val,e ▸ witness23p7ok r⟩
  by_cases h8 : q<18432
  · let r : Fin 2048 := ⟨q-16384,by omega⟩
    have e : 16384+r.val=q := by dsimp [r]; omega
    exact ⟨witness23p8 r.val,e ▸ witness23p8ok r⟩
  by_cases h9 : q<20480
  · let r : Fin 2048 := ⟨q-18432,by omega⟩
    have e : 18432+r.val=q := by dsimp [r]; omega
    exact ⟨witness23p9 r.val,e ▸ witness23p9ok r⟩
  by_cases h10 : q<22528
  · let r : Fin 2048 := ⟨q-20480,by omega⟩
    have e : 20480+r.val=q := by dsimp [r]; omega
    exact ⟨witness23p10 r.val,e ▸ witness23p10ok r⟩
  by_cases h11 : q<24576
  · let r : Fin 2048 := ⟨q-22528,by omega⟩
    have e : 22528+r.val=q := by dsimp [r]; omega
    exact ⟨witness23p11 r.val,e ▸ witness23p11ok r⟩
  by_cases h12 : q<26624
  · let r : Fin 2048 := ⟨q-24576,by omega⟩
    have e : 24576+r.val=q := by dsimp [r]; omega
    exact ⟨witness23p12 r.val,e ▸ witness23p12ok r⟩
  by_cases h13 : q<28672
  · let r : Fin 2048 := ⟨q-26624,by omega⟩
    have e : 26624+r.val=q := by dsimp [r]; omega
    exact ⟨witness23p13 r.val,e ▸ witness23p13ok r⟩
  by_cases h14 : q<30720
  · let r : Fin 2048 := ⟨q-28672,by omega⟩
    have e : 28672+r.val=q := by dsimp [r]; omega
    exact ⟨witness23p14 r.val,e ▸ witness23p14ok r⟩
  by_cases h15 : q<32768
  · let r : Fin 2048 := ⟨q-30720,by omega⟩
    have e : 30720+r.val=q := by dsimp [r]; omega
    exact ⟨witness23p15 r.val,e ▸ witness23p15ok r⟩
  by_cases h16 : q<34816
  · let r : Fin 2048 := ⟨q-32768,by omega⟩
    have e : 32768+r.val=q := by dsimp [r]; omega
    exact ⟨witness23p16 r.val,e ▸ witness23p16ok r⟩
  by_cases h17 : q<36864
  · let r : Fin 2048 := ⟨q-34816,by omega⟩
    have e : 34816+r.val=q := by dsimp [r]; omega
    exact ⟨witness23p17 r.val,e ▸ witness23p17ok r⟩
  by_cases h18 : q<38912
  · let r : Fin 2048 := ⟨q-36864,by omega⟩
    have e : 36864+r.val=q := by dsimp [r]; omega
    exact ⟨witness23p18 r.val,e ▸ witness23p18ok r⟩
  by_cases h19 : q<40960
  · let r : Fin 2048 := ⟨q-38912,by omega⟩
    have e : 38912+r.val=q := by dsimp [r]; omega
    exact ⟨witness23p19 r.val,e ▸ witness23p19ok r⟩
  by_cases h20 : q<43008
  · let r : Fin 2048 := ⟨q-40960,by omega⟩
    have e : 40960+r.val=q := by dsimp [r]; omega
    exact ⟨witness23p20 r.val,e ▸ witness23p20ok r⟩
  by_cases h21 : q<45056
  · let r : Fin 2048 := ⟨q-43008,by omega⟩
    have e : 43008+r.val=q := by dsimp [r]; omega
    exact ⟨witness23p21 r.val,e ▸ witness23p21ok r⟩
  by_cases h22 : q<47104
  · let r : Fin 2048 := ⟨q-45056,by omega⟩
    have e : 45056+r.val=q := by dsimp [r]; omega
    exact ⟨witness23p22 r.val,e ▸ witness23p22ok r⟩
  by_cases h23 : q<49152
  · let r : Fin 2048 := ⟨q-47104,by omega⟩
    have e : 47104+r.val=q := by dsimp [r]; omega
    exact ⟨witness23p23 r.val,e ▸ witness23p23ok r⟩
  by_cases h24 : q<51200
  · let r : Fin 2048 := ⟨q-49152,by omega⟩
    have e : 49152+r.val=q := by dsimp [r]; omega
    exact ⟨witness23p24 r.val,e ▸ witness23p24ok r⟩
  by_cases h25 : q<53248
  · let r : Fin 2048 := ⟨q-51200,by omega⟩
    have e : 51200+r.val=q := by dsimp [r]; omega
    exact ⟨witness23p25 r.val,e ▸ witness23p25ok r⟩
  let r : Fin 764 := ⟨q-53248,by omega⟩
  have e : 53248+r.val=q := by dsimp [r]; omega
  exact ⟨witness23p26 r.val,e ▸ witness23p26ok r⟩
end PetersenNegated3971
