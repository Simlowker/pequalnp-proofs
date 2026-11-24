import BoxRange3971Part00
import BoxRange3971Part01
import BoxRange3971Part02
import BoxRange3971Part03
import BoxRange3971Part04
import BoxRange3971Part05
import BoxRange3971Part06
import BoxRange3971Part07
import BoxRange3971Part08
import BoxRange3971Part09
import BoxRange3971Part10
import BoxRange3971Part11
import BoxRange3971Part12
import BoxRange3971Part13
import BoxRange3971Part14
import BoxRange3971Part15
import BoxRange3971Part16
import BoxRange3971Part17
import BoxRange3971Part18
namespace PetersenNegated3971
theorem all_boxes (idx : Nat) (h : idx<604) : checkBox (bk idx,bm idx,br idx)=true := by
  by_cases b0 : idx<32
  · let r : Fin 32 := ⟨idx-0,by omega⟩
    have e : 0+r.val=idx := by dsimp [r]; omega
    exact e ▸ boxRange0 r
  by_cases b1 : idx<64
  · let r : Fin 32 := ⟨idx-32,by omega⟩
    have e : 32+r.val=idx := by dsimp [r]; omega
    exact e ▸ boxRange1 r
  by_cases b2 : idx<96
  · let r : Fin 32 := ⟨idx-64,by omega⟩
    have e : 64+r.val=idx := by dsimp [r]; omega
    exact e ▸ boxRange2 r
  by_cases b3 : idx<128
  · let r : Fin 32 := ⟨idx-96,by omega⟩
    have e : 96+r.val=idx := by dsimp [r]; omega
    exact e ▸ boxRange3 r
  by_cases b4 : idx<160
  · let r : Fin 32 := ⟨idx-128,by omega⟩
    have e : 128+r.val=idx := by dsimp [r]; omega
    exact e ▸ boxRange4 r
  by_cases b5 : idx<192
  · let r : Fin 32 := ⟨idx-160,by omega⟩
    have e : 160+r.val=idx := by dsimp [r]; omega
    exact e ▸ boxRange5 r
  by_cases b6 : idx<224
  · let r : Fin 32 := ⟨idx-192,by omega⟩
    have e : 192+r.val=idx := by dsimp [r]; omega
    exact e ▸ boxRange6 r
  by_cases b7 : idx<256
  · let r : Fin 32 := ⟨idx-224,by omega⟩
    have e : 224+r.val=idx := by dsimp [r]; omega
    exact e ▸ boxRange7 r
  by_cases b8 : idx<288
  · let r : Fin 32 := ⟨idx-256,by omega⟩
    have e : 256+r.val=idx := by dsimp [r]; omega
    exact e ▸ boxRange8 r
  by_cases b9 : idx<320
  · let r : Fin 32 := ⟨idx-288,by omega⟩
    have e : 288+r.val=idx := by dsimp [r]; omega
    exact e ▸ boxRange9 r
  by_cases b10 : idx<352
  · let r : Fin 32 := ⟨idx-320,by omega⟩
    have e : 320+r.val=idx := by dsimp [r]; omega
    exact e ▸ boxRange10 r
  by_cases b11 : idx<384
  · let r : Fin 32 := ⟨idx-352,by omega⟩
    have e : 352+r.val=idx := by dsimp [r]; omega
    exact e ▸ boxRange11 r
  by_cases b12 : idx<416
  · let r : Fin 32 := ⟨idx-384,by omega⟩
    have e : 384+r.val=idx := by dsimp [r]; omega
    exact e ▸ boxRange12 r
  by_cases b13 : idx<448
  · let r : Fin 32 := ⟨idx-416,by omega⟩
    have e : 416+r.val=idx := by dsimp [r]; omega
    exact e ▸ boxRange13 r
  by_cases b14 : idx<480
  · let r : Fin 32 := ⟨idx-448,by omega⟩
    have e : 448+r.val=idx := by dsimp [r]; omega
    exact e ▸ boxRange14 r
  by_cases b15 : idx<512
  · let r : Fin 32 := ⟨idx-480,by omega⟩
    have e : 480+r.val=idx := by dsimp [r]; omega
    exact e ▸ boxRange15 r
  by_cases b16 : idx<544
  · let r : Fin 32 := ⟨idx-512,by omega⟩
    have e : 512+r.val=idx := by dsimp [r]; omega
    exact e ▸ boxRange16 r
  by_cases b17 : idx<576
  · let r : Fin 32 := ⟨idx-544,by omega⟩
    have e : 544+r.val=idx := by dsimp [r]; omega
    exact e ▸ boxRange17 r
  let r : Fin 28 := ⟨idx-576,by omega⟩
  have e : 576+r.val=idx := by dsimp [r]; omega
  exact e ▸ boxRange18 r
end PetersenNegated3971
