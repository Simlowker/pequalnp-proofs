import Mathlib
import PEqualNP.Defs

/-! Minimum monotone formulas for the function with table 0xfeeaeeeafeeaecc8.
The rectangle table certifies the leaf bound. On rectangles at equality,
a second certificate classifies the possible counts of each input literal. -/

namespace Simlowker.Function16756
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 6 → Bool) := Nat.testBit (4276809450 * 2^32 + 4276808904)
  (∑ i : Fin 6, if x i then 2^(i:Nat) else 0)

def factored (x : Fin 6 → Bool) :=
  (x 1 && (x 0 || (x 2 || x 3))) ||
  (((x 0 || x 4) && (x 2 && x 3)) || (x 0 && (x 4 || x 5)))

theorem agrees : ∀ x, factored x = target x := by decide +kernel

def balanced : Circuit := ⟨[
  ⟨.or,[2,3]⟩, ⟨.or,[0,6]⟩, ⟨.and,[1,7]⟩,
  ⟨.or,[0,4]⟩, ⟨.and,[2,3]⟩, ⟨.and,[9,10]⟩,
  ⟨.or,[4,5]⟩, ⟨.and,[0,12]⟩, ⟨.or,[11,13]⟩, ⟨.or,[8,14]⟩], 15⟩

theorem balanced_eval : ∀ x, balanced.eval (List.ofFn x) = target x := by decide +kernel
theorem bounds : balanced.size = 10 ∧ balanced.depth 6 = 4 := by decide +kernel

theorem monotone : Monotone2 balanced := by
  intro g hg
  simp only [balanced, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

#print axioms balanced_eval
end Simlowker.Function16756

namespace Simlowker.KW16756
abbrev R := BitVec 7
abbrev C := BitVec 6

def posInput : Fin 7 → Nat := ![3, 6, 10, 13, 17, 28, 33]
def negInput : Fin 6 → Nat := ![5, 9, 44, 50, 52, 56]
def posLit : Fin 8 → R := ![89, 7, 42, 44, 48, 64, 0, 127]
def negLit : Fin 8 → C := ![3, 8, 21, 38, 56, 60, 0, 63]
def table : Array Nat := #[
  0x0,
  0x2221222111111111222122211111111122212221111111112221222111111110,
  0x2222222211111111222221211111111122222222111111112222212111111110,
  0x3333333311111111333333321111111133333333111111113333333211111110,
  0x2222222211111111222222221111111122222211111111112222221111111110,
  0x3333333311111111333333331111111133333332111111113333333211111110,
  0x3333333311111111333333331111111133333333111111113333333211111110,
  0x4444444411111111444444441111111144444444111111114444444311111110,
  0x3221222132212221322121213221212132212211322122113221211132212110,
  0x4331433143313331433143314331323143314331433133214331433143313220,
  0x4343333343323332434331314332313143433333433233224343313143323120,
  0x6553554343323332655353424332323265535543433233226553534243323220,
  0x4433333343323332443333334332323244333311433233114433331143323210,
  0x6553545343323332655354534332323265535432433233226553543243323220,
  0x6554555443323332655453534332323265545533433233226554533243323220,
  0x7664666443323332766464644332323276646644433233227664644343323220,
  0x2221222122212221222122212221222122212221222122212221222111111110,
  0x3331333133313331333133313331333133313331333133313331333122212220,
  0x4443444333323332444343423332333244434443333233324443434222222220,
  0x5553555333323332444344423332333255535553333233324443444222222220,
  0x4443444333323332444344433332333244434432333233324443443222222220,
  0x5553555333323332555355533332333244434442333233324443444222222220,
  0x5554555433323332555455543332333255545554333233325554555322222220,
  0x6664666433323332666466643332333266646664333233325554555322222220,
  0x4331433143314331433143314331433143314331433143314331433143313220,
  0x5441544154415441544154415441544154415441544154415441544154414330,
  0x6553555354425442655353525442534265535553544254426553535254424230,
  0x7663666354425442766364525442544276636663544254427663645254424330,
  0x6553555354425442655355535442544265535532544254326553553254424320,
  0x7663666354425442766366635442544276636542544254427663654254424330,
  0x7664766454425442766475645442544276647654544254427664755354424330,
  0x8774877454425442877476745442544287747764544254428774755354424330,
  0x3333222233332222222221212222212122222211222222112222211111111110,
  0x5554444344443333444343423333323244434432333333224443433222222220,
  0x4444333344443333333331313333313144443333333333223333313122222120,
  0x5555554444443333444443423333323255555544333333224444434222222220,
  0x4444333344443333444433333333323233333311333333113333331122222210,
  0x5555545444443333555554543333323244444432333333224444443222222220,
  0x6666555544443333555553533333323255555533333333224444433222222220,
  0x7777666644443333666664643333323266666644333333225555544322222220,
  0x4444222244442222434321214343212144332211443322114333211143322110,
  0x6554444355543333655343425453323265534432554333226553433254423220,
  0x5555333355553333545431315454313155553333554433225454313154433120,
  0x7765554455553333766453425454323277655544554433227664534254433220,
  0x5555333355553333555533335454323255443311554433115544331154433210,
  0x7675545455553333767554545454323276645432554433227664543254433220,
  0x7777555555553333766653535454323276665533554433227665533254433220,
  0x8887666655553333877664645454323287766644554433228775644354433220,
  0x4444444344444443333333323333333233333332333333323333333211111110,
  0x5554555355545553444344424443444244434442444344424443444222222220,
  0x6665555455555554444443424444434255555554444444434444434222222220,
  0x6665666455555554444444424444444266656664444444434444444222222220,
  0x6665555455555554555555544444444344444432444444324444443222222220,
  0x6665666455555554666566644444444344444442444444424444444222222220,
  0x7777777655555554666665644444444366666654444444435555555322222220,
  0x8887888655555554666666644444444366666664444444435555555322222220,
  0x6664444366644443655343426553434265534432655344326553433243323220,
  0x7774555377745553766354527663545276635542766355427663544254424330,
  0x7775555477755554766453527664535276755554766455437664535254434230,
  0x8885666477755554766464527664545287856664766455437664645254434330,
  0x7775555477755554776555547664545376645532766455327664553254434320,
  0x8885666477755554887566647664545376646542766455427664654254434330,
  0x9997777677755554887675747664545387867754766455438775755354434330,
  0xa997888677755554887676747664545387867764766455438775755354434330,
  0x2221222122212221222122212221222122212221222122212221222122211110,
  0x3331333133313331333133313331333133313331333133313331333133312220,
  0x4443444333323332444343423332333244434443333233324443434233322220,
  0x5553555333323332555344423332333255535553333233325553444233322220,
  0x4443444333323332444344433332333244434432333233324443443233322220,
  0x5553555333323332555355533332333255534442333233325553444233322220,
  0x5554555433323332555455543332333255545554333233325554555333322220,
  0x6664666433323332666466643332333266646664333233326664555333322220,
  0x4331433143314331433143314331433143314331433143314331433143313220,
  0x5441544154415441544154415441544154415441544154415441544154414330,
  0x6553555354425442655353525442534265535553544254426553535254424230,
  0x7663666354425442766364525442544276636663544254427663645254424330,
  0x6553555354425442655355535442544265535532544254326553553254424320,
  0x7663666354425442766366635442544276636542544254427663654254424330,
  0x7664766454425442766475645442544276647654544254427664755354424330,
  0x8774877454425442877476745442544287747764544254428774755354424330,
  0x3331333133313331333133313331333133313331333133313331333133312220,
  0x4441444144414441444144414441444144414441444144414441444144413330,
  0x5553555344424442555354524442444255535553444244425553545244423330,
  0x6663666344424442666355524442444266636663444244426663555244423330,
  0x5553555344424442555355534442444255535542444244425553554244423330,
  0x6663666344424442666366634442444266635552444244426663555244423330,
  0x6664666444424442666466644442444266646664444244426664666344423330,
  0x7774777444424442777477744442444277747774444244427774666344423330,
  0x5441544154415441544154415441544154415441544154415441544154414330,
  0x6551655165516551655165516551655165516551655165516551655165515440,
  0x7663666365526552766364626552645276636663655265527663646265525340,
  0x8773777365526552877375626552655287737773655265528773756265525440,
  0x7663666365526552766366636552655276636642655265427663664265525430,
  0x8773777365526552877377736552655287737652655265528773765265525440,
  0x8774877465526552877486746552655287748764655265528774866365525440,
  0x9884988465526552988487846552655298848874655265529884866365525440,
  0x5554444355544443444343424443434244434432444344324443433233322220,
  0x6664555366645553555354525553545255535542555355425553544244423330,
  0x6665555466655554555453525554535266655554555455435554535244433230,
  0x7775666466655554666454525554545277756664555455436664545244433330,
  0x6665555466655554666555545554545355545532555455325554553244433320,
  0x7775666466655554777566645554545366645542555455426664554244433330,
  0x8887777666655554777675745554545377767754555455436665655344433330,
  0x9997888666655554888676745554545388867764555455437775655344433330,
  0x6664444366644443655343426553434265534432655344326553433254423220,
  0x7774555377745553766354527663545276635542766355427663544265524330,
  0x7775555477755554766453527664535277755554766455437664535265534230,
  0x8885666477755554877464527664545288856664766455438774645265534330,
  0x7775555477755554777555547664545376645532766455327664553265534320,
  0x8885666477755554888566647664545387746542766455428774654265534330,
  0x9997777677755554988675747664545398867754766455438775755365534330,
  0xaaa7888677755554a996767476645453a9967764766455439885755365534330,
  0x6664555366645553555344425553444255534442555344425553444233322220,
  0x7774666377746663666355526663555266635552666355526663555244423330,
  0x7775666477756664666454526664545277756664666455536664545244433330,
  0x8885777477756664666455526664555288857774666455536664555244433330,
  0x7775666477756664777566646664555366645542666455426664554244433330,
  0x8885777477756664888577746664555366645552666455526664555244433330,
  0x9997888677756664888676746664555388867764666455537775666344433330,
  0xaaa7999677756664888677746664555388867774666455537775666344433330,
  0x7774555377745553766354527663545276635542766355427663544254424330,
  0x8884666388846663877365628773656287736652877366528773655265525440,
  0x8885666488856664877464628774646288856664877466538774646265535340,
  0x9995777488856664877475628774656299957774877466538774756265535440,
  0x8885666488856664888566648774656387746642877466428774664265535430,
  0x9995777488856664999577748774656387747652877466528774765265535440,
  0xaaa7888688856664a996868487746563a9968864877466539885866365535440,
  0xbbb7999688856664a996878487746563a9968874877466539885866365535440]

def price (r : R) (c : C) : Nat := ((table[r.toNat]! >>> (4*c.toNat)) % 16)
def row_ok (r : R) : Bool := (List.range 128).all fun i =>
  let a := BitVec.ofNat 7 i
  (a &&& r != a) || (List.range 64).all fun j =>
    let c := BitVec.ofNat 6 j
    decide (price r c ≤ price a c + price (r &&& ~~~a) c)
def col_ok (c : C) : Bool := (List.range 64).all fun j =>
  let b := BitVec.ofNat 6 j
  (b &&& c != b) || (List.range 128).all fun i =>
    let r := BitVec.ofNat 7 i
    decide (price r c ≤ price r b + price r (c &&& ~~~b))
set_option maxHeartbeats 0
set_option maxRecDepth 50000
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem rowAt0 : row_ok 0 = true := by decide +kernel
theorem rowAt1 : row_ok 1 = true := by decide +kernel
theorem rowAt2 : row_ok 2 = true := by decide +kernel
theorem rowAt3 : row_ok 3 = true := by decide +kernel
theorem rowAt4 : row_ok 4 = true := by decide +kernel
theorem rowAt5 : row_ok 5 = true := by decide +kernel
theorem rowAt6 : row_ok 6 = true := by decide +kernel
theorem rowAt7 : row_ok 7 = true := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem rowAt8 : row_ok 8 = true := by decide +kernel
theorem rowAt9 : row_ok 9 = true := by decide +kernel
theorem rowAt10 : row_ok 10 = true := by decide +kernel
theorem rowAt11 : row_ok 11 = true := by decide +kernel
theorem rowAt12 : row_ok 12 = true := by decide +kernel
theorem rowAt13 : row_ok 13 = true := by decide +kernel
theorem rowAt14 : row_ok 14 = true := by decide +kernel
theorem rowAt15 : row_ok 15 = true := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem rowAt16 : row_ok 16 = true := by decide +kernel
theorem rowAt17 : row_ok 17 = true := by decide +kernel
theorem rowAt18 : row_ok 18 = true := by decide +kernel
theorem rowAt19 : row_ok 19 = true := by decide +kernel
theorem rowAt20 : row_ok 20 = true := by decide +kernel
theorem rowAt21 : row_ok 21 = true := by decide +kernel
theorem rowAt22 : row_ok 22 = true := by decide +kernel
theorem rowAt23 : row_ok 23 = true := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem rowAt24 : row_ok 24 = true := by decide +kernel
theorem rowAt25 : row_ok 25 = true := by decide +kernel
theorem rowAt26 : row_ok 26 = true := by decide +kernel
theorem rowAt27 : row_ok 27 = true := by decide +kernel
theorem rowAt28 : row_ok 28 = true := by decide +kernel
theorem rowAt29 : row_ok 29 = true := by decide +kernel
theorem rowAt30 : row_ok 30 = true := by decide +kernel
theorem rowAt31 : row_ok 31 = true := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem rowAt32 : row_ok 32 = true := by decide +kernel
theorem rowAt33 : row_ok 33 = true := by decide +kernel
theorem rowAt34 : row_ok 34 = true := by decide +kernel
theorem rowAt35 : row_ok 35 = true := by decide +kernel
theorem rowAt36 : row_ok 36 = true := by decide +kernel
theorem rowAt37 : row_ok 37 = true := by decide +kernel
theorem rowAt38 : row_ok 38 = true := by decide +kernel
theorem rowAt39 : row_ok 39 = true := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem rowAt40 : row_ok 40 = true := by decide +kernel
theorem rowAt41 : row_ok 41 = true := by decide +kernel
theorem rowAt42 : row_ok 42 = true := by decide +kernel
theorem rowAt43 : row_ok 43 = true := by decide +kernel
theorem rowAt44 : row_ok 44 = true := by decide +kernel
theorem rowAt45 : row_ok 45 = true := by decide +kernel
theorem rowAt46 : row_ok 46 = true := by decide +kernel
theorem rowAt47 : row_ok 47 = true := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem rowAt48 : row_ok 48 = true := by decide +kernel
theorem rowAt49 : row_ok 49 = true := by decide +kernel
theorem rowAt50 : row_ok 50 = true := by decide +kernel
theorem rowAt51 : row_ok 51 = true := by decide +kernel
theorem rowAt52 : row_ok 52 = true := by decide +kernel
theorem rowAt53 : row_ok 53 = true := by decide +kernel
theorem rowAt54 : row_ok 54 = true := by decide +kernel
theorem rowAt55 : row_ok 55 = true := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem rowAt56 : row_ok 56 = true := by decide +kernel
theorem rowAt57 : row_ok 57 = true := by decide +kernel
theorem rowAt58 : row_ok 58 = true := by decide +kernel
theorem rowAt59 : row_ok 59 = true := by decide +kernel
theorem rowAt60 : row_ok 60 = true := by decide +kernel
theorem rowAt61 : row_ok 61 = true := by decide +kernel
theorem rowAt62 : row_ok 62 = true := by decide +kernel
theorem rowAt63 : row_ok 63 = true := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem rowAt64 : row_ok 64 = true := by decide +kernel
theorem rowAt65 : row_ok 65 = true := by decide +kernel
theorem rowAt66 : row_ok 66 = true := by decide +kernel
theorem rowAt67 : row_ok 67 = true := by decide +kernel
theorem rowAt68 : row_ok 68 = true := by decide +kernel
theorem rowAt69 : row_ok 69 = true := by decide +kernel
theorem rowAt70 : row_ok 70 = true := by decide +kernel
theorem rowAt71 : row_ok 71 = true := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem rowAt72 : row_ok 72 = true := by decide +kernel
theorem rowAt73 : row_ok 73 = true := by decide +kernel
theorem rowAt74 : row_ok 74 = true := by decide +kernel
theorem rowAt75 : row_ok 75 = true := by decide +kernel
theorem rowAt76 : row_ok 76 = true := by decide +kernel
theorem rowAt77 : row_ok 77 = true := by decide +kernel
theorem rowAt78 : row_ok 78 = true := by decide +kernel
theorem rowAt79 : row_ok 79 = true := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem rowAt80 : row_ok 80 = true := by decide +kernel
theorem rowAt81 : row_ok 81 = true := by decide +kernel
theorem rowAt82 : row_ok 82 = true := by decide +kernel
theorem rowAt83 : row_ok 83 = true := by decide +kernel
theorem rowAt84 : row_ok 84 = true := by decide +kernel
theorem rowAt85 : row_ok 85 = true := by decide +kernel
theorem rowAt86 : row_ok 86 = true := by decide +kernel
theorem rowAt87 : row_ok 87 = true := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem rowAt88 : row_ok 88 = true := by decide +kernel
theorem rowAt89 : row_ok 89 = true := by decide +kernel
theorem rowAt90 : row_ok 90 = true := by decide +kernel
theorem rowAt91 : row_ok 91 = true := by decide +kernel
theorem rowAt92 : row_ok 92 = true := by decide +kernel
theorem rowAt93 : row_ok 93 = true := by decide +kernel
theorem rowAt94 : row_ok 94 = true := by decide +kernel
theorem rowAt95 : row_ok 95 = true := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem rowAt96 : row_ok 96 = true := by decide +kernel
theorem rowAt97 : row_ok 97 = true := by decide +kernel
theorem rowAt98 : row_ok 98 = true := by decide +kernel
theorem rowAt99 : row_ok 99 = true := by decide +kernel
theorem rowAt100 : row_ok 100 = true := by decide +kernel
theorem rowAt101 : row_ok 101 = true := by decide +kernel
theorem rowAt102 : row_ok 102 = true := by decide +kernel
theorem rowAt103 : row_ok 103 = true := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem rowAt104 : row_ok 104 = true := by decide +kernel
theorem rowAt105 : row_ok 105 = true := by decide +kernel
theorem rowAt106 : row_ok 106 = true := by decide +kernel
theorem rowAt107 : row_ok 107 = true := by decide +kernel
theorem rowAt108 : row_ok 108 = true := by decide +kernel
theorem rowAt109 : row_ok 109 = true := by decide +kernel
theorem rowAt110 : row_ok 110 = true := by decide +kernel
theorem rowAt111 : row_ok 111 = true := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem rowAt112 : row_ok 112 = true := by decide +kernel
theorem rowAt113 : row_ok 113 = true := by decide +kernel
theorem rowAt114 : row_ok 114 = true := by decide +kernel
theorem rowAt115 : row_ok 115 = true := by decide +kernel
theorem rowAt116 : row_ok 116 = true := by decide +kernel
theorem rowAt117 : row_ok 117 = true := by decide +kernel
theorem rowAt118 : row_ok 118 = true := by decide +kernel
theorem rowAt119 : row_ok 119 = true := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem rowAt120 : row_ok 120 = true := by decide +kernel
theorem rowAt121 : row_ok 121 = true := by decide +kernel
theorem rowAt122 : row_ok 122 = true := by decide +kernel
theorem rowAt123 : row_ok 123 = true := by decide +kernel
theorem rowAt124 : row_ok 124 = true := by decide +kernel
theorem rowAt125 : row_ok 125 = true := by decide +kernel
theorem rowAt126 : row_ok 126 = true := by decide +kernel
theorem rowAt127 : row_ok 127 = true := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem colAt0 : col_ok 0 = true := by decide +kernel
theorem colAt1 : col_ok 1 = true := by decide +kernel
theorem colAt2 : col_ok 2 = true := by decide +kernel
theorem colAt3 : col_ok 3 = true := by decide +kernel
theorem colAt4 : col_ok 4 = true := by decide +kernel
theorem colAt5 : col_ok 5 = true := by decide +kernel
theorem colAt6 : col_ok 6 = true := by decide +kernel
theorem colAt7 : col_ok 7 = true := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem colAt8 : col_ok 8 = true := by decide +kernel
theorem colAt9 : col_ok 9 = true := by decide +kernel
theorem colAt10 : col_ok 10 = true := by decide +kernel
theorem colAt11 : col_ok 11 = true := by decide +kernel
theorem colAt12 : col_ok 12 = true := by decide +kernel
theorem colAt13 : col_ok 13 = true := by decide +kernel
theorem colAt14 : col_ok 14 = true := by decide +kernel
theorem colAt15 : col_ok 15 = true := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem colAt16 : col_ok 16 = true := by decide +kernel
theorem colAt17 : col_ok 17 = true := by decide +kernel
theorem colAt18 : col_ok 18 = true := by decide +kernel
theorem colAt19 : col_ok 19 = true := by decide +kernel
theorem colAt20 : col_ok 20 = true := by decide +kernel
theorem colAt21 : col_ok 21 = true := by decide +kernel
theorem colAt22 : col_ok 22 = true := by decide +kernel
theorem colAt23 : col_ok 23 = true := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem colAt24 : col_ok 24 = true := by decide +kernel
theorem colAt25 : col_ok 25 = true := by decide +kernel
theorem colAt26 : col_ok 26 = true := by decide +kernel
theorem colAt27 : col_ok 27 = true := by decide +kernel
theorem colAt28 : col_ok 28 = true := by decide +kernel
theorem colAt29 : col_ok 29 = true := by decide +kernel
theorem colAt30 : col_ok 30 = true := by decide +kernel
theorem colAt31 : col_ok 31 = true := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem colAt32 : col_ok 32 = true := by decide +kernel
theorem colAt33 : col_ok 33 = true := by decide +kernel
theorem colAt34 : col_ok 34 = true := by decide +kernel
theorem colAt35 : col_ok 35 = true := by decide +kernel
theorem colAt36 : col_ok 36 = true := by decide +kernel
theorem colAt37 : col_ok 37 = true := by decide +kernel
theorem colAt38 : col_ok 38 = true := by decide +kernel
theorem colAt39 : col_ok 39 = true := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem colAt40 : col_ok 40 = true := by decide +kernel
theorem colAt41 : col_ok 41 = true := by decide +kernel
theorem colAt42 : col_ok 42 = true := by decide +kernel
theorem colAt43 : col_ok 43 = true := by decide +kernel
theorem colAt44 : col_ok 44 = true := by decide +kernel
theorem colAt45 : col_ok 45 = true := by decide +kernel
theorem colAt46 : col_ok 46 = true := by decide +kernel
theorem colAt47 : col_ok 47 = true := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem colAt48 : col_ok 48 = true := by decide +kernel
theorem colAt49 : col_ok 49 = true := by decide +kernel
theorem colAt50 : col_ok 50 = true := by decide +kernel
theorem colAt51 : col_ok 51 = true := by decide +kernel
theorem colAt52 : col_ok 52 = true := by decide +kernel
theorem colAt53 : col_ok 53 = true := by decide +kernel
theorem colAt54 : col_ok 54 = true := by decide +kernel
theorem colAt55 : col_ok 55 = true := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem colAt56 : col_ok 56 = true := by decide +kernel
theorem colAt57 : col_ok 57 = true := by decide +kernel
theorem colAt58 : col_ok 58 = true := by decide +kernel
theorem colAt59 : col_ok 59 = true := by decide +kernel
theorem colAt60 : col_ok 60 = true := by decide +kernel
theorem colAt61 : col_ok 61 = true := by decide +kernel
theorem colAt62 : col_ok 62 = true := by decide +kernel
theorem colAt63 : col_ok 63 = true := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem row_checked (x : R) : row_ok x = true := by
  have checked (i : Nat) (h : i < 128) : row_ok (BitVec.ofNat 7 i) = true := by
    interval_cases i
    · exact rowAt0
    · exact rowAt1
    · exact rowAt2
    · exact rowAt3
    · exact rowAt4
    · exact rowAt5
    · exact rowAt6
    · exact rowAt7
    · exact rowAt8
    · exact rowAt9
    · exact rowAt10
    · exact rowAt11
    · exact rowAt12
    · exact rowAt13
    · exact rowAt14
    · exact rowAt15
    · exact rowAt16
    · exact rowAt17
    · exact rowAt18
    · exact rowAt19
    · exact rowAt20
    · exact rowAt21
    · exact rowAt22
    · exact rowAt23
    · exact rowAt24
    · exact rowAt25
    · exact rowAt26
    · exact rowAt27
    · exact rowAt28
    · exact rowAt29
    · exact rowAt30
    · exact rowAt31
    · exact rowAt32
    · exact rowAt33
    · exact rowAt34
    · exact rowAt35
    · exact rowAt36
    · exact rowAt37
    · exact rowAt38
    · exact rowAt39
    · exact rowAt40
    · exact rowAt41
    · exact rowAt42
    · exact rowAt43
    · exact rowAt44
    · exact rowAt45
    · exact rowAt46
    · exact rowAt47
    · exact rowAt48
    · exact rowAt49
    · exact rowAt50
    · exact rowAt51
    · exact rowAt52
    · exact rowAt53
    · exact rowAt54
    · exact rowAt55
    · exact rowAt56
    · exact rowAt57
    · exact rowAt58
    · exact rowAt59
    · exact rowAt60
    · exact rowAt61
    · exact rowAt62
    · exact rowAt63
    · exact rowAt64
    · exact rowAt65
    · exact rowAt66
    · exact rowAt67
    · exact rowAt68
    · exact rowAt69
    · exact rowAt70
    · exact rowAt71
    · exact rowAt72
    · exact rowAt73
    · exact rowAt74
    · exact rowAt75
    · exact rowAt76
    · exact rowAt77
    · exact rowAt78
    · exact rowAt79
    · exact rowAt80
    · exact rowAt81
    · exact rowAt82
    · exact rowAt83
    · exact rowAt84
    · exact rowAt85
    · exact rowAt86
    · exact rowAt87
    · exact rowAt88
    · exact rowAt89
    · exact rowAt90
    · exact rowAt91
    · exact rowAt92
    · exact rowAt93
    · exact rowAt94
    · exact rowAt95
    · exact rowAt96
    · exact rowAt97
    · exact rowAt98
    · exact rowAt99
    · exact rowAt100
    · exact rowAt101
    · exact rowAt102
    · exact rowAt103
    · exact rowAt104
    · exact rowAt105
    · exact rowAt106
    · exact rowAt107
    · exact rowAt108
    · exact rowAt109
    · exact rowAt110
    · exact rowAt111
    · exact rowAt112
    · exact rowAt113
    · exact rowAt114
    · exact rowAt115
    · exact rowAt116
    · exact rowAt117
    · exact rowAt118
    · exact rowAt119
    · exact rowAt120
    · exact rowAt121
    · exact rowAt122
    · exact rowAt123
    · exact rowAt124
    · exact rowAt125
    · exact rowAt126
    · exact rowAt127
  simpa using checked x.toNat x.isLt
theorem col_checked (x : C) : col_ok x = true := by
  have checked (i : Nat) (h : i < 64) : col_ok (BitVec.ofNat 6 i) = true := by
    interval_cases i
    · exact colAt0
    · exact colAt1
    · exact colAt2
    · exact colAt3
    · exact colAt4
    · exact colAt5
    · exact colAt6
    · exact colAt7
    · exact colAt8
    · exact colAt9
    · exact colAt10
    · exact colAt11
    · exact colAt12
    · exact colAt13
    · exact colAt14
    · exact colAt15
    · exact colAt16
    · exact colAt17
    · exact colAt18
    · exact colAt19
    · exact colAt20
    · exact colAt21
    · exact colAt22
    · exact colAt23
    · exact colAt24
    · exact colAt25
    · exact colAt26
    · exact colAt27
    · exact colAt28
    · exact colAt29
    · exact colAt30
    · exact colAt31
    · exact colAt32
    · exact colAt33
    · exact colAt34
    · exact colAt35
    · exact colAt36
    · exact colAt37
    · exact colAt38
    · exact colAt39
    · exact colAt40
    · exact colAt41
    · exact colAt42
    · exact colAt43
    · exact colAt44
    · exact colAt45
    · exact colAt46
    · exact colAt47
    · exact colAt48
    · exact colAt49
    · exact colAt50
    · exact colAt51
    · exact colAt52
    · exact colAt53
    · exact colAt54
    · exact colAt55
    · exact colAt56
    · exact colAt57
    · exact colAt58
    · exact colAt59
    · exact colAt60
    · exact colAt61
    · exact colAt62
    · exact colAt63
  simpa using checked x.toNat x.isLt
end Simlowker.KW16756

namespace Simlowker.KW16756

inductive F where
  | var (v : Fin 8)
  | conj (l r : F)
  | disj (l r : F)

def F.leaves : F → Nat
  | .var _ => 1
  | .conj a b | .disj a b => a.leaves + b.leaves

def F.word {n : Nat} (x : Fin 8 → BitVec n) : F → BitVec n
  | .var i => x i
  | .conj a b => a.word x &&& b.word x
  | .disj a b => a.word x ||| b.word x

def F.eval (x : Fin 8 → Bool) : F → Bool
  | .var i => x i
  | .conj a b => a.eval x && b.eval x
  | .disj a b => a.eval x || b.eval x

theorem eval_word {n} (f : F) (x : Fin 8 → BitVec n) (i : Fin n) :
    (f.word x)[i.val] = f.eval (fun v => (x v)[i.val]) := by
  induction f <;> simp [F.word, F.eval, *]

theorem split_row (r a : R) (c : C) (ok : row_ok r = true) (sub : a &&& r = a) :
    price r c ≤ price a c + price (r &&& ~~~a) c := by
  have h := List.all_eq_true.mp ok a.toNat (List.mem_range.mpr a.isLt)
  simp [sub] at h
  simpa using h c.toNat c.isLt

theorem split_col (r : R) (c b : C) (ok : col_ok c = true) (sub : b &&& c = b) :
    price r c ≤ price r b + price r (c &&& ~~~b) := by
  have h := List.all_eq_true.mp ok b.toNat (List.mem_range.mpr b.isLt)
  simp [sub] at h
  simpa using h r.toNat r.isLt

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem leaf (v : Fin 8) (r : R) (c : C) :
    r &&& posLit v = r → c &&& negLit v = 0 → price r c ≤ 1 := by
  revert c r v
  decide +kernel

theorem pos_split {n : Nat} (s u v : BitVec n) (h : s &&& (u ||| v) = s) :
    ((s &&& u) &&& s = (s &&& u)) ∧
    ((s &&& u) &&& u = (s &&& u)) ∧
    ((s &&& ~~~(s &&& u)) &&& v = (s &&& ~~~(s &&& u))) := by
  repeat' constructor
  all_goals
    apply BitVec.eq_of_getElem_eq
    intro i hi
    have e := congrArg (fun b : BitVec n => b[i]) h
    clear h
    cases hs : s[i] <;> cases hu : u[i] <;> cases hv : v[i] <;>
      simp_all

theorem neg_split {n : Nat} (s u v : BitVec n) (h : s &&& (u &&& v) = 0) :
    ((s &&& ~~~u) &&& s = s &&& ~~~u) ∧
    ((s &&& ~~~u) &&& u = 0) ∧
    ((s &&& ~~~(s &&& ~~~u)) &&& v = 0) := by
  repeat' constructor
  all_goals
    apply BitVec.eq_of_getElem_eq
    intro i hi
    have e := congrArg (fun b : BitVec n => b[i]) h
    clear h
    cases hs : s[i] <;> cases hu : u[i] <;> cases hv : v[i] <;>
      simp_all

theorem pos_both {n : Nat} (s u v : BitVec n) (h : s &&& (u &&& v) = s) :
    s &&& u = s ∧ s &&& v = s := by
  constructor <;> apply BitVec.eq_of_getElem_eq <;> intro i hi
  all_goals
    have e := congrArg (fun b : BitVec n => b[i]) h
    clear h
    cases hs : s[i] <;> cases hu : u[i] <;> cases hv : v[i] <;> simp_all

theorem neg_both {n : Nat} (s u v : BitVec n) (h : s &&& (u ||| v) = 0) :
    s &&& u = 0 ∧ s &&& v = 0 := by
  constructor <;> apply BitVec.eq_of_getElem_eq <;> intro i hi
  all_goals
    have e := congrArg (fun b : BitVec n => b[i]) h
    clear h
    cases hs : s[i] <;> cases hu : u[i] <;> cases hv : v[i] <;> simp_all

theorem account (rows : ∀ r, row_ok r = true) (cols : ∀ c, col_ok c = true)
    (f : F) (r : R) (c : C)
    (hy : r &&& f.word posLit = r) (hn : c &&& f.word negLit = 0) : price r c ≤ f.leaves := by
  induction f generalizing r c with
  | var v => exact leaf v r c hy hn
  | conj l t ih jh =>
    obtain ⟨a,b⟩ := pos_both r (l.word posLit) (t.word posLit) hy
    obtain ⟨sub,p,q⟩ := neg_split c (l.word negLit) (t.word negLit) hn
    exact (split_col _ _ _ (cols c) sub).trans (Nat.add_le_add (ih _ _ a p) (jh _ _ b q))
  | disj l t ih jh =>
    obtain ⟨sub,p,q⟩ := pos_split r (l.word posLit) (t.word posLit) hy
    obtain ⟨a,b⟩ := neg_both c (l.word negLit) (t.word negLit) hn
    exact (split_row _ _ _ (rows r) sub).trans (Nat.add_le_add (ih _ _ p a) (jh _ _ q b))

end Simlowker.KW16756

namespace Simlowker.KW16756
open Simlowker.Function16756
set_option maxRecDepth 50000
set_option maxHeartbeats 0

def sample (r : Nat) (v : Fin 6) : Bool := r.testBit v.val
def literals (x : Fin 6 → Bool) (v : Fin 8) : Bool :=
  if h : v.val < 6 then x ⟨v.val,h⟩ else decide (v.val=7)

theorem row_bits : ∀ (i : Fin 7) (v : Fin 8), (posLit v)[i.val] = literals (sample (posInput i)) v := by decide +kernel
theorem col_bits : ∀ (i : Fin 6) (v : Fin 8), (negLit v)[i.val] = literals (sample (negInput i)) v := by decide +kernel
theorem row_values : ∀ i, target (sample (posInput i)) = true := by decide +kernel
theorem col_values : ∀ i, target (sample (negInput i)) = false := by decide +kernel

theorem lower (f : F) (computes : ∀ x, f.eval (literals x) = target x) : 11 ≤ f.leaves := by
  have yes (i : Fin 7) : (f.word posLit)[i.val] = true := by
    rw [eval_word,show (fun v => (posLit v)[i.val]) = literals (sample (posInput i)) from funext (row_bits i)]
    exact (computes _).trans (row_values i)
  have no (i : Fin 6) : (f.word negLit)[i.val] = false := by
    rw [eval_word,show (fun v => (negLit v)[i.val]) = literals (sample (negInput i)) from funext (col_bits i)]
    exact (computes _).trans (col_values i)
  have on : (127:R) &&& f.word posLit = 127 := by
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp [yes ⟨i,hi⟩]
  have off : (63:C) &&& f.word negLit = 0 := by
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp [no ⟨i,hi⟩]
  exact account row_checked col_checked f 127 63 on off

def formula : F := .disj (.conj (.var 1) (.disj (.var 0) (.disj (.var 2) (.var 3))))
  (.disj (.conj (.disj (.var 0) (.var 4)) (.conj (.var 2) (.var 3))) (.conj (.var 0) (.disj (.var 4) (.var 5))))

theorem formula_evaluates : ∀ x, formula.eval (literals x) = target x := by decide +kernel

theorem formula_minimum (k : Nat) :
    (∃ f : F, f.leaves ≤ k ∧ ∀ x, f.eval (literals x) = target x) ↔ 11 ≤ k := by
  constructor
  · rintro ⟨f, size, ok⟩
    exact (lower f ok).trans size
  · intro h
    exact ⟨formula,h,formula_evaluates⟩

#print axioms formula_minimum
end Simlowker.KW16756

namespace Simlowker.KW16756
def skeleton : Array Nat := #[
 0x0,
 0x200000000000000000000000000000002000000000000000000000000000000020000000001000000,
 0x4000004000000000100010100000000000000000003000300000000000000000000000000000400010001010000010000000000000300030000000000000000,
 0x6000000000000000100000000000000000000000000000500000000000000000000000000000600010000000000010000000000000000050000000001000000,
 0x8000008000000000101000100000000000000000008000001010001000100000000000000000707000000000000000000000000000007070000000000000000,
 0xa00000000000000010000000000000000000000000a000001000000000100000000000000000009000000000000000000000000000000090000000001000000,
 0xc00000c0000000001000001000000000000000000000000000100000000000000000000000000000000010000000000000000000000000b0000000100000000,
 0xe0000000000000001000000010000000000000000000000000100000000000000000000000000000000010000000000000000000000000d0000000001000000,
 0x200000000,
 0x2000000020000000000000000,
 0x30000000000000000,
 0x50000000000000000,
 0x70000000000000000,
 0x90000000000000000,
 0x0,
 0x0,
 0xf000000,
 0x10000000,
 0x0,
 0x10000000,
 0x0,
 0x10000000,
 0x0,
 0x10000000,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0xf00000000,
 0x0,
 0x30000000000000000,
 0x50000000000000000,
 0x70000000000000000,
 0x90000000000000000,
 0x110000000b0000001000000000,
 0x0,
 0x150000000b000000150000000b000000001400000003000000140000000300000000130000000700000013000000070000000000000000000000001200000000,
 0x0,
 0x17000000000000000000000000000000000000000003000000000000000000000000000000000000000016000000000000000000000000030000000000000000,
 0x50000000000000000,
 0x17000000000000000000000000000000000000000000000000180000000000000000000000000700000000000000000000000000000000070000000000000000,
 0x90000000000000000,
 0x1900000000000000170000000000000000000000000c000000180000000000000000000000000c000000160000000000000000000000000b0000000000000000,
 0x1a00000000000000170000000c00000000000000000e000000180000000000000000000000000e000000160000000000000000170000000d0000000000000000,
 0xf00000000,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x1b000000,
 0x1c000000,
 0x0,
 0x1c000000,
 0x0,
 0x1c000000,
 0x0,
 0x1c000000,
 0x200000000,
 0x200000000,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x1e0000021e0000021e0000021e00000200000000000000001e0000020000000000000000000000001e000002000000000000000000000000000000001d000000,
 0x2000000220000002000000000000000000000000000000020000000000000000000000000000000200000000000000000000000000000002000000001f000000,
 0x0,
 0x2100000600000000200000000000000000000000000000050000000000000000000000000000000020000000000000000000000000000005000000001f000000,
 0x0,
 0x2200000a00000000200000000000000000000000000000002000000000000000000000000000000900000000000000000000000000000009000000001f000000,
 0x0,
 0x2300000e0000000020000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000d000000001f000000,
 0x200000000,
 0x2000000020000000200000000,
 0x0,
 0x50000000000000000,
 0x0,
 0x90000000000000000,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x0,
 0x50000000000000000,
 0x0,
 0x90000000000000000,
 0x0,
 0x0,
 0x25000000240000002500000024000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001200000000,
 0x27000000260000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001200000000,
 0x27000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
 0x28000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000050000000000000000,
 0x27000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
 0x28000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000090000000000000000,
 0x0,
 0x290000000000000027000000260000000000000000000000000000000000000000000000000000000000000000000000000000170000000d0000000000000000]
def families : Array (List Nat) := #[
 [],
 [0x10],
 [0x1],
 [0x100],
 [0x110],
 [0x101],
 [0x111],
 [0x1000],
 [0x1010],
 [0x1001],
 [0x1011],
 [0x1100],
 [0x1110],
 [0x1101],
 [0x1111],
 [0x10000],
 [0x10010],
 [0x11110],
 [0x10001],
 [0x11001],
 [0x10101],
 [0x11101],
 [0x11011],
 [0x11111],
 [0x10111],
 [0x11221, 0x12121, 0x12211],
 [0x11222, 0x12122, 0x12212, 0x12221],
 [0x100000],
 [0x100010],
 [0x110000],
 [0x110001],
 [0x110010],
 [0x110011],
 [0x110112, 0x110121],
 [0x111012, 0x111021],
 [0x111112, 0x111121],
 [0x111101],
 [0x121102],
 [0x111111],
 [0x121112],
 [0x121122],
 [0x121223, 0x121232, 0x122123, 0x122132, 0x122213, 0x122222]]

def opts (r : R) (c : C) : List Nat := families[((skeleton[r.toNat]! >>> (8*c.toNat)) % 256)]!
def leafCode (v : Fin 8) : Nat := 16^v.val
def covers (out a b : List Nat) : Prop :=
  a ≠ [] ∧ b ≠ [] ∧ ∀ x ∈ a, ∀ y ∈ b, x+y ∈ out

instance (out a b : List Nat) : Decidable (covers out a b) := by unfold covers; infer_instance

def tightRule (r : R) (c : C) : Prop := opts r c ≠ [] →
  (∀ v : Fin 8, price r c = 1 → r &&& posLit v = r → c &&& negLit v = 0 → leafCode v ∈ opts r c) ∧
  (∀ a : R, a &&& r = a → 0 < price a c → 0 < price (r &&& ~~~a) c →
    price a c + price (r &&& ~~~a) c = price r c →
    covers (opts r c) (opts a c) (opts (r &&& ~~~a) c)) ∧
  (∀ b : C, b &&& c = b → 0 < price r b → 0 < price r (c &&& ~~~b) →
    price r b + price r (c &&& ~~~b) = price r c →
    covers (opts r c) (opts r b) (opts r (c &&& ~~~b)))
set_option synthInstance.maxSize 4000 in
instance (r : R) (c : C) : Decidable (tightRule r c) := by unfold tightRule; infer_instance
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem tight0 : ∀ c : C, tightRule 0 c := by decide +kernel
theorem tight1 : ∀ c : C, tightRule 1 c := by decide +kernel
theorem tight2 : ∀ c : C, tightRule 2 c := by decide +kernel
theorem tight3 : ∀ c : C, tightRule 3 c := by decide +kernel
theorem tight4 : ∀ c : C, tightRule 4 c := by decide +kernel
theorem tight5 : ∀ c : C, tightRule 5 c := by decide +kernel
theorem tight6 : ∀ c : C, tightRule 6 c := by decide +kernel
theorem tight7 : ∀ c : C, tightRule 7 c := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem tight8 : ∀ c : C, tightRule 8 c := by decide +kernel
theorem tight9 : ∀ c : C, tightRule 9 c := by decide +kernel
theorem tight10 : ∀ c : C, tightRule 10 c := by decide +kernel
theorem tight11 : ∀ c : C, tightRule 11 c := by decide +kernel
theorem tight12 : ∀ c : C, tightRule 12 c := by decide +kernel
theorem tight13 : ∀ c : C, tightRule 13 c := by decide +kernel
theorem tight14 : ∀ c : C, tightRule 14 c := by decide +kernel
theorem tight15 : ∀ c : C, tightRule 15 c := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem tight16 : ∀ c : C, tightRule 16 c := by decide +kernel
theorem tight17 : ∀ c : C, tightRule 17 c := by decide +kernel
theorem tight18 : ∀ c : C, tightRule 18 c := by decide +kernel
theorem tight19 : ∀ c : C, tightRule 19 c := by decide +kernel
theorem tight20 : ∀ c : C, tightRule 20 c := by decide +kernel
theorem tight21 : ∀ c : C, tightRule 21 c := by decide +kernel
theorem tight22 : ∀ c : C, tightRule 22 c := by decide +kernel
theorem tight23 : ∀ c : C, tightRule 23 c := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem tight24 : ∀ c : C, tightRule 24 c := by decide +kernel
theorem tight25 : ∀ c : C, tightRule 25 c := by decide +kernel
theorem tight26 : ∀ c : C, tightRule 26 c := by decide +kernel
theorem tight27 : ∀ c : C, tightRule 27 c := by decide +kernel
theorem tight28 : ∀ c : C, tightRule 28 c := by decide +kernel
theorem tight29 : ∀ c : C, tightRule 29 c := by decide +kernel
theorem tight30 : ∀ c : C, tightRule 30 c := by decide +kernel
theorem tight31 : ∀ c : C, tightRule 31 c := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem tight32 : ∀ c : C, tightRule 32 c := by decide +kernel
theorem tight33 : ∀ c : C, tightRule 33 c := by decide +kernel
theorem tight34 : ∀ c : C, tightRule 34 c := by decide +kernel
theorem tight35 : ∀ c : C, tightRule 35 c := by decide +kernel
theorem tight36 : ∀ c : C, tightRule 36 c := by decide +kernel
theorem tight37 : ∀ c : C, tightRule 37 c := by decide +kernel
theorem tight38 : ∀ c : C, tightRule 38 c := by decide +kernel
theorem tight39 : ∀ c : C, tightRule 39 c := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem tight40 : ∀ c : C, tightRule 40 c := by decide +kernel
theorem tight41 : ∀ c : C, tightRule 41 c := by decide +kernel
theorem tight42 : ∀ c : C, tightRule 42 c := by decide +kernel
theorem tight43 : ∀ c : C, tightRule 43 c := by decide +kernel
theorem tight44 : ∀ c : C, tightRule 44 c := by decide +kernel
theorem tight45 : ∀ c : C, tightRule 45 c := by decide +kernel
theorem tight46 : ∀ c : C, tightRule 46 c := by decide +kernel
theorem tight47 : ∀ c : C, tightRule 47 c := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem tight48 : ∀ c : C, tightRule 48 c := by decide +kernel
theorem tight49 : ∀ c : C, tightRule 49 c := by decide +kernel
theorem tight50 : ∀ c : C, tightRule 50 c := by decide +kernel
theorem tight51 : ∀ c : C, tightRule 51 c := by decide +kernel
theorem tight52 : ∀ c : C, tightRule 52 c := by decide +kernel
theorem tight53 : ∀ c : C, tightRule 53 c := by decide +kernel
theorem tight54 : ∀ c : C, tightRule 54 c := by decide +kernel
theorem tight55 : ∀ c : C, tightRule 55 c := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem tight56 : ∀ c : C, tightRule 56 c := by decide +kernel
theorem tight57 : ∀ c : C, tightRule 57 c := by decide +kernel
theorem tight58 : ∀ c : C, tightRule 58 c := by decide +kernel
theorem tight59 : ∀ c : C, tightRule 59 c := by decide +kernel
theorem tight60 : ∀ c : C, tightRule 60 c := by decide +kernel
theorem tight61 : ∀ c : C, tightRule 61 c := by decide +kernel
theorem tight62 : ∀ c : C, tightRule 62 c := by decide +kernel
theorem tight63 : ∀ c : C, tightRule 63 c := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem tight64 : ∀ c : C, tightRule 64 c := by decide +kernel
theorem tight65 : ∀ c : C, tightRule 65 c := by decide +kernel
theorem tight66 : ∀ c : C, tightRule 66 c := by decide +kernel
theorem tight67 : ∀ c : C, tightRule 67 c := by decide +kernel
theorem tight68 : ∀ c : C, tightRule 68 c := by decide +kernel
theorem tight69 : ∀ c : C, tightRule 69 c := by decide +kernel
theorem tight70 : ∀ c : C, tightRule 70 c := by decide +kernel
theorem tight71 : ∀ c : C, tightRule 71 c := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem tight72 : ∀ c : C, tightRule 72 c := by decide +kernel
theorem tight73 : ∀ c : C, tightRule 73 c := by decide +kernel
theorem tight74 : ∀ c : C, tightRule 74 c := by decide +kernel
theorem tight75 : ∀ c : C, tightRule 75 c := by decide +kernel
theorem tight76 : ∀ c : C, tightRule 76 c := by decide +kernel
theorem tight77 : ∀ c : C, tightRule 77 c := by decide +kernel
theorem tight78 : ∀ c : C, tightRule 78 c := by decide +kernel
theorem tight79 : ∀ c : C, tightRule 79 c := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem tight80 : ∀ c : C, tightRule 80 c := by decide +kernel
theorem tight81 : ∀ c : C, tightRule 81 c := by decide +kernel
theorem tight82 : ∀ c : C, tightRule 82 c := by decide +kernel
theorem tight83 : ∀ c : C, tightRule 83 c := by decide +kernel
theorem tight84 : ∀ c : C, tightRule 84 c := by decide +kernel
theorem tight85 : ∀ c : C, tightRule 85 c := by decide +kernel
theorem tight86 : ∀ c : C, tightRule 86 c := by decide +kernel
theorem tight87 : ∀ c : C, tightRule 87 c := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem tight88 : ∀ c : C, tightRule 88 c := by decide +kernel
theorem tight89 : ∀ c : C, tightRule 89 c := by decide +kernel
theorem tight90 : ∀ c : C, tightRule 90 c := by decide +kernel
theorem tight91 : ∀ c : C, tightRule 91 c := by decide +kernel
theorem tight92 : ∀ c : C, tightRule 92 c := by decide +kernel
theorem tight93 : ∀ c : C, tightRule 93 c := by decide +kernel
theorem tight94 : ∀ c : C, tightRule 94 c := by decide +kernel
theorem tight95 : ∀ c : C, tightRule 95 c := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem tight96 : ∀ c : C, tightRule 96 c := by decide +kernel
theorem tight97 : ∀ c : C, tightRule 97 c := by decide +kernel
theorem tight98 : ∀ c : C, tightRule 98 c := by decide +kernel
theorem tight99 : ∀ c : C, tightRule 99 c := by decide +kernel
theorem tight100 : ∀ c : C, tightRule 100 c := by decide +kernel
theorem tight101 : ∀ c : C, tightRule 101 c := by decide +kernel
theorem tight102 : ∀ c : C, tightRule 102 c := by decide +kernel
theorem tight103 : ∀ c : C, tightRule 103 c := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem tight104 : ∀ c : C, tightRule 104 c := by decide +kernel
theorem tight105 : ∀ c : C, tightRule 105 c := by decide +kernel
theorem tight106 : ∀ c : C, tightRule 106 c := by decide +kernel
theorem tight107 : ∀ c : C, tightRule 107 c := by decide +kernel
theorem tight108 : ∀ c : C, tightRule 108 c := by decide +kernel
theorem tight109 : ∀ c : C, tightRule 109 c := by decide +kernel
theorem tight110 : ∀ c : C, tightRule 110 c := by decide +kernel
theorem tight111 : ∀ c : C, tightRule 111 c := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem tight112 : ∀ c : C, tightRule 112 c := by decide +kernel
theorem tight113 : ∀ c : C, tightRule 113 c := by decide +kernel
theorem tight114 : ∀ c : C, tightRule 114 c := by decide +kernel
theorem tight115 : ∀ c : C, tightRule 115 c := by decide +kernel
theorem tight116 : ∀ c : C, tightRule 116 c := by decide +kernel
theorem tight117 : ∀ c : C, tightRule 117 c := by decide +kernel
theorem tight118 : ∀ c : C, tightRule 118 c := by decide +kernel
theorem tight119 : ∀ c : C, tightRule 119 c := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem tight120 : ∀ c : C, tightRule 120 c := by decide +kernel
theorem tight121 : ∀ c : C, tightRule 121 c := by decide +kernel
theorem tight122 : ∀ c : C, tightRule 122 c := by decide +kernel
theorem tight123 : ∀ c : C, tightRule 123 c := by decide +kernel
theorem tight124 : ∀ c : C, tightRule 124 c := by decide +kernel
theorem tight125 : ∀ c : C, tightRule 125 c := by decide +kernel
theorem tight126 : ∀ c : C, tightRule 126 c := by decide +kernel
theorem tight127 : ∀ c : C, tightRule 127 c := by decide +kernel
end Simlowker.KW16756

namespace Simlowker.KW16756
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem tightChecked (r : R) (c : C) : tightRule r c := by
  have all (i : Nat) (h : i < 128) : tightRule (BitVec.ofNat 7 i) c := by
    interval_cases i
    · exact tight0 c
    · exact tight1 c
    · exact tight2 c
    · exact tight3 c
    · exact tight4 c
    · exact tight5 c
    · exact tight6 c
    · exact tight7 c
    · exact tight8 c
    · exact tight9 c
    · exact tight10 c
    · exact tight11 c
    · exact tight12 c
    · exact tight13 c
    · exact tight14 c
    · exact tight15 c
    · exact tight16 c
    · exact tight17 c
    · exact tight18 c
    · exact tight19 c
    · exact tight20 c
    · exact tight21 c
    · exact tight22 c
    · exact tight23 c
    · exact tight24 c
    · exact tight25 c
    · exact tight26 c
    · exact tight27 c
    · exact tight28 c
    · exact tight29 c
    · exact tight30 c
    · exact tight31 c
    · exact tight32 c
    · exact tight33 c
    · exact tight34 c
    · exact tight35 c
    · exact tight36 c
    · exact tight37 c
    · exact tight38 c
    · exact tight39 c
    · exact tight40 c
    · exact tight41 c
    · exact tight42 c
    · exact tight43 c
    · exact tight44 c
    · exact tight45 c
    · exact tight46 c
    · exact tight47 c
    · exact tight48 c
    · exact tight49 c
    · exact tight50 c
    · exact tight51 c
    · exact tight52 c
    · exact tight53 c
    · exact tight54 c
    · exact tight55 c
    · exact tight56 c
    · exact tight57 c
    · exact tight58 c
    · exact tight59 c
    · exact tight60 c
    · exact tight61 c
    · exact tight62 c
    · exact tight63 c
    · exact tight64 c
    · exact tight65 c
    · exact tight66 c
    · exact tight67 c
    · exact tight68 c
    · exact tight69 c
    · exact tight70 c
    · exact tight71 c
    · exact tight72 c
    · exact tight73 c
    · exact tight74 c
    · exact tight75 c
    · exact tight76 c
    · exact tight77 c
    · exact tight78 c
    · exact tight79 c
    · exact tight80 c
    · exact tight81 c
    · exact tight82 c
    · exact tight83 c
    · exact tight84 c
    · exact tight85 c
    · exact tight86 c
    · exact tight87 c
    · exact tight88 c
    · exact tight89 c
    · exact tight90 c
    · exact tight91 c
    · exact tight92 c
    · exact tight93 c
    · exact tight94 c
    · exact tight95 c
    · exact tight96 c
    · exact tight97 c
    · exact tight98 c
    · exact tight99 c
    · exact tight100 c
    · exact tight101 c
    · exact tight102 c
    · exact tight103 c
    · exact tight104 c
    · exact tight105 c
    · exact tight106 c
    · exact tight107 c
    · exact tight108 c
    · exact tight109 c
    · exact tight110 c
    · exact tight111 c
    · exact tight112 c
    · exact tight113 c
    · exact tight114 c
    · exact tight115 c
    · exact tight116 c
    · exact tight117 c
    · exact tight118 c
    · exact tight119 c
    · exact tight120 c
    · exact tight121 c
    · exact tight122 c
    · exact tight123 c
    · exact tight124 c
    · exact tight125 c
    · exact tight126 c
    · exact tight127 c
  simpa using all r.toNat r.isLt
end Simlowker.KW16756

namespace Simlowker.KW16756

def F.code : F → Nat
  | .var v => leafCode v
  | .disj l r | .conj l r => l.code + r.code

def F.occ (v : Fin 8) : F → Nat
  | .var i => if i=v then 1 else 0
  | .disj l r | .conj l r => l.occ v + r.occ v

theorem posLeaves (f : F) : 0 < f.leaves := by
  induction f <;> simp [F.leaves, *]

theorem occ_le (f : F) (v : Fin 8) : f.occ v ≤ f.leaves := by
  induction f with
  | var i => simp [F.occ,F.leaves]; split <;> decide
  | conj a b ia ib | disj a b ia ib => exact Nat.add_le_add ia ib

theorem classification (rules : ∀ r c, tightRule r c) (f : F) (r : R) (c : C)
    (hy : r &&& f.word posLit = r) (hn : c &&& f.word negLit = 0)
    (live : opts r c ≠ []) (tight : f.leaves = price r c) : f.code ∈ opts r c := by
  induction f generalizing r c with
  | var i => exact (rules r c live).1 i tight.symm hy hn
  | conj l t ih jh =>
    obtain ⟨a,b⟩ := pos_both r (l.word posLit) (t.word posLit) hy
    obtain ⟨sub,p,q⟩ := neg_split c (l.word negLit) (t.word negLit) hn
    have low := split_col r _ _ (col_checked c) sub
    have ll := account row_checked col_checked l _ _ a p
    have rr := account row_checked col_checked t _ _ b q
    change l.leaves + t.leaves = _ at tight
    have hl : l.leaves = price r (c &&& ~~~(l.word negLit)) := by omega
    have hr : t.leaves = price r (c &&& ~~~(c &&& ~~~(l.word negLit))) := by omega
    obtain ⟨u,v,w⟩ := (rules r c live).2.2 _ sub ((posLeaves l).trans_eq hl)
      ((posLeaves t).trans_eq hr) (by omega)
    exact w _ (ih _ _ a p u hl) _ (jh _ _ b q v hr)
  | disj l t ih jh =>
    obtain ⟨sub,p,q⟩ := pos_split r (l.word posLit) (t.word posLit) hy
    obtain ⟨a,b⟩ := neg_both c (l.word negLit) (t.word negLit) hn
    have low := split_row _ _ c (row_checked r) sub
    have ll := account row_checked col_checked l _ _ p a
    have rr := account row_checked col_checked t _ _ q b
    change l.leaves + t.leaves = _ at tight
    have hl : l.leaves = price (r &&& l.word posLit) c := by omega
    have hr : t.leaves = price (r &&& ~~~(r &&& l.word posLit)) c := by omega
    obtain ⟨u,v,w⟩ := (rules r c live).2.1 _ sub ((posLeaves l).trans_eq hl)
      ((posLeaves t).trans_eq hr) (by omega)
    exact w _ (ih _ _ p a u hl) _ (jh _ _ q b v hr)

end Simlowker.KW16756

namespace Simlowker.KW16756
open Simlowker.Function16756
set_option maxRecDepth 50000
set_option maxHeartbeats 0
def examples : Fin 6 → F := ![
  (.disj (.conj (.disj (.var 0) (.conj (.disj (.var 1) (.var 4)) (.disj (.var 3) (.var 2)))) (.disj (.var 1) (.conj (.var 3) (.var 2)))) (.conj (.disj (.var 4) (.var 5)) (.var 0))),
  (.disj (.disj (.conj (.var 3) (.var 1)) (.conj (.disj (.var 1) (.conj (.disj (.var 0) (.var 4)) (.var 3))) (.var 2))) (.conj (.disj (.disj (.var 1) (.var 4)) (.var 5)) (.var 0))),
  (.disj (.disj (.conj (.var 1) (.var 2)) (.conj (.var 3) (.disj (.var 1) (.conj (.disj (.var 0) (.var 4)) (.var 2))))) (.conj (.disj (.disj (.var 1) (.var 4)) (.var 5)) (.var 0))),
  (.disj (.disj (.conj (.disj (.disj (.var 0) (.var 2)) (.var 3)) (.var 1)) (.conj (.conj (.disj (.var 0) (.var 4)) (.var 3)) (.var 2))) (.conj (.disj (.var 4) (.var 5)) (.var 0))),
  (.disj (.disj (.conj (.disj (.var 0) (.var 3)) (.var 1)) (.conj (.disj (.var 1) (.conj (.disj (.var 0) (.var 4)) (.var 3))) (.var 2))) (.conj (.disj (.var 4) (.var 5)) (.var 0))),
  (.disj (.disj (.conj (.var 1) (.disj (.var 0) (.var 2))) (.conj (.var 3) (.disj (.var 1) (.conj (.disj (.var 0) (.var 4)) (.var 2))))) (.conj (.disj (.var 4) (.var 5)) (.var 0)))]
def profiles : Fin 6 → Fin 8 → Nat := ![
  ![2, 2, 2, 2, 2, 1, 0, 0],
  ![2, 3, 1, 2, 2, 1, 0, 0],
  ![2, 3, 2, 1, 2, 1, 0, 0],
  ![3, 1, 2, 2, 2, 1, 0, 0],
  ![3, 2, 1, 2, 2, 1, 0, 0],
  ![3, 2, 2, 1, 2, 1, 0, 0]]
def pack (x : Fin 8 → Nat) : Nat := x 0 + 16 * (x 1 + 16 * (x 2 + 16 * (x 3 + 16 * (x 4 + 16 * (x 5 + 16 * (x 6 + 16 * (x 7)))))))

theorem code_eq (f : F) : f.code = pack (fun v => f.occ v) := by
  induction f with
  | var i => fin_cases i <;> decide +kernel
  | conj a b ha hb | disj a b ha hb =>
    simp only [F.code, ha, hb, pack, F.occ]
    omega

theorem pack_injective {x y : Fin 8 → Nat} (hx : ∀ i, x i < 16) (hy : ∀ i, y i < 16)
    (h : pack x = pack y) : x = y := by
  have peel {a b u v : Nat} (ha : a<16) (hb : b<16) (eq : a+16*u=b+16*v) :
      a=b ∧ u=v := by omega
  unfold pack at h
  obtain ⟨h0,h⟩ := peel (hx 0) (hy 0) h
  obtain ⟨h1,h⟩ := peel (hx 1) (hy 1) h
  obtain ⟨h2,h⟩ := peel (hx 2) (hy 2) h
  obtain ⟨h3,h⟩ := peel (hx 3) (hy 3) h
  obtain ⟨h4,h⟩ := peel (hx 4) (hy 4) h
  obtain ⟨h5,h⟩ := peel (hx 5) (hy 5) h
  obtain ⟨h6,h⟩ := peel (hx 6) (hy 6) h
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h

theorem example_profiles : ∀ i v, (examples i).occ v = profiles i v := by decide +kernel
theorem example_size : ∀ i, (examples i).leaves = 11 := by decide +kernel
theorem example_evaluations : ∀ i x, (examples i).eval (literals x) = target x := by decide +kernel

theorem optimum_profiles (q : Fin 8 → Nat) :
    (∃ f : F, f.leaves = 11 ∧ (∀ x, f.eval (literals x) = target x) ∧
      (fun v => f.occ v) = q) ↔ ∃ i, profiles i = q := by
  constructor
  · rintro ⟨f,sz,ok,rfl⟩
    have yes (i : Fin 7) : (f.word posLit)[i.val] = true := by
      rw [eval_word,show (fun v => (posLit v)[i.val]) = literals (sample (posInput i)) from funext (row_bits i)]
      exact (ok _).trans (row_values i)
    have no (i : Fin 6) : (f.word negLit)[i.val] = false := by
      rw [eval_word,show (fun v => (negLit v)[i.val]) = literals (sample (negInput i)) from funext (col_bits i)]
      exact (ok _).trans (col_values i)
    have on : (127:R) &&& f.word posLit = 127 := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simp [yes ⟨i,hi⟩]
    have off : (63:C) &&& f.word negLit = 0 := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simp [no ⟨i,hi⟩]

    have root : price 127 63 = 11 := by decide +kernel
    have code := classification tightChecked f 127 63 on off (by decide +kernel) (sz.trans root.symm)
    have choices : ∀ t ∈ opts 127 63, ∃ i, (examples i).code = t := by decide +kernel
    obtain ⟨i,hi⟩ := choices _ code
    refine ⟨i,?_⟩
    have hpack : pack (fun v => (examples i).occ v) = pack (fun v => f.occ v) := by simpa only [code_eq] using hi
    have eq := pack_injective (fun v => (occ_le (examples i) v).trans_lt (by rw [example_size]; decide))
      (fun v => (occ_le f v).trans_lt (by rw [sz]; decide)) hpack
    exact (funext (example_profiles i)).symm.trans eq
  · rintro ⟨i,rfl⟩
    exact ⟨examples i, example_size i, example_evaluations i, funext (example_profiles i)⟩

#print axioms optimum_profiles
end Simlowker.KW16756
