import Mathlib
import PEqualNP.Defs

-- A necessary condition for the 63-gate circuit in L-meta-1980.
-- The counting argument adapts the clean-circuit proof for the Heawood graph.
-- The final theorem is PlanePairClean.persistent_mixed_gate.


namespace PlaneRows
abbrev Word := BitVec 78
abbrev V := Fin 26
abbrev E := Fin 52

def words : List Word := [4944745225269945565199, 76002621210714924122352, 3250698211036024016640, 43113571722367080656896, 81490941903809234796544, 87396349965593595609088, 191270258578628095770624, 57854767533479096745984, 10664555442875150630912, 160652757189362060361728, 170162116825215999672320, 19226371476285703585792, 701489403683506487296, 22481973843982899232801, 47338970498752112230928, 152517711667365456912640, 28776986057181564637184, 152038190756304766697480, 24276167402598117146752, 80465202052954761201664, 78288990659546772963328, 40880002550483906985984, 43981074225157352980480, 86795389667601278828548, 167673986681536470057024, 283374271055817040987138]
def varWord (v : V) : Word := words.getD v.val 0
def goal : Word := 4503599627370495
def rneg (r : Fin 26) := 52 + r.val
def adjMasks : List (BitVec 26) := [42082304, 17063936, 34127872, 1155072, 2310144, 4620288, 9240576, 18481152, 36962304, 6823936, 13647872, 27295744, 54591488, 523, 1046, 2092, 4184, 177, 354, 708, 1416, 2832, 5664, 3137, 6274, 4357]
def nb (u : V) := adjMasks.getD u.val 0
def adjacent (u v : V) := (nb u).getLsbD v.val

set_option maxHeartbeats 4000000 in
theorem common : ∀ a b : V, a ≠ b → ∀ c : V, adjacent a c = true → adjacent b c = true →
    c.val = ((nb a &&& nb b).toNat.log2) := by decide +kernel

theorem no_square (a b c d : V) (ab : a ≠ b) (cd : c ≠ d)
    (ac : adjacent a c = true) (ad : adjacent a d = true) (bc : adjacent b c = true) :
    adjacent b d = false := by
  cases h : adjacent b d with
  | false => rfl
  | true => exact False.elim (cd (Fin.ext ((common a b ab c ac bc).trans (common a b ab d ad h).symm)))

end PlaneRows


namespace PlanePairRows
abbrev Word := BitVec 325
abbrev V := Fin 26
abbrev E := Fin 52

def words : List Word := [9444728462139663056911, 9903510869554580059529937136, 5192286955023958087461235681398528, 1361124275396798858229636887307027017728, 178404600463969618044045127845263813871861760, 11691834694046774952961431456307906413380292837376, 383112193381782251234190746611361959468600475114274816, 6276718623193834207636159081318962393324371062818529607680, 51415740697699572092883195673570488568980725190896013694468096, 210573167597566115633612084905191523628085269071143200717868630016, 431148573525646274688818409424383315983146952857875554594110914428928, 441280617775374155578178182788567555339096598562910946455395222167748608, 225715144306040177481341107351837693191997853657480616261367966891182653440, 926111000049564916573078433215536675949054692035344057723939517389515557716001, 1896211480391863277277059474010119874961707597551168867149866551111555707555807760, 1940772681426458478237070101835053596552728955426378070614939662137421899698014265600, 992705702918515676376861326764519098838294424167317382863379916901642115815633095626752, 253636797035865753004284028158309316858379227043175615302723106844498769227338828384108552, 32338944663716535323805964231198819645245493470892458218652504246389087236008230138546225280, 2053588890721016923127965587469943418312318451171694910542518381582364739884048706831132919808, 64696775861534987996224579677081695133344637799206518086293397171856918946031671538813937680384, 1003396059585239238222443282266289563147543958906172390757647448372862296879447844748581570871296, 7547008493590339002656861147017810875356929658446790704545639890300160240949089755421154329231360, 26841945684745683458486454535324447428400703366500196274746405277286036115560172628988061133307908, 45139943225807726587392596089654234551861866085585632400218832480724022238392143806133632323551296, 56104093876880891856464845101451518315959622145957012597188944649330124619459848732918792444707842]
def varWord (v : V) : Word := words.getD v.val 0
def goal : Word := 4503599627370495
def rneg (r : Fin 273) := 52 + r.val
def adjMasks : List (BitVec 26) := [42082304, 17063936, 34127872, 1155072, 2310144, 4620288, 9240576, 18481152, 36962304, 6823936, 13647872, 27295744, 54591488, 523, 1046, 2092, 4184, 177, 354, 708, 1416, 2832, 5664, 3137, 6274, 4357]
def nb (u : V) := adjMasks.getD u.val 0
def adjacent (u v : V) := (nb u).getLsbD v.val

theorem no_square (a b c d : V) (ab : a ≠ b) (cd : c ≠ d)
    (ac : adjacent a c = true) (ad : adjacent a d = true) (bc : adjacent b c = true) :
    adjacent b d = false := PlaneRows.no_square a b c d ab cd ac ad bc
end PlanePairRows

namespace PlanePairUnion
variable {α : Type} [DecidableEq α]
abbrev Family (α : Type) := Finset (Finset α)
def cap (pool : Family α) (n : Nat) : Prop :=
  ∀ asks ⊆ pool, (asks.biUnion id).card ≤ asks.card+n

theorem small {pool : Family α} (h : ∀ s∈pool,s.card ≤ 1) : cap pool 0 := by
  intro asks sub
  induction asks using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    rw [Finset.biUnion_insert,Finset.card_insert_of_notMem ha]
    have ca := h a (sub (Finset.mem_insert_self a t))
    have prev := ih ((Finset.subset_insert a t).trans sub)
    exact (Finset.card_union_le _ _).trans (by simp only [id_eq]; omega)

theorem merge {pool : Family α} {n : Nat} (h : cap pool n) {a b : Finset α}
    (ha : a∈pool) (hb : b∈pool) : cap (insert (a∪b) pool) (n+1) := by
  intro asks sub
  by_cases occurs : a∪b∈asks
  · let rem := asks.erase (a∪b)
    have smaller : rem ⊆ pool := by
      intro s hs
      obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hs
      exact (Finset.mem_insert.mp (sub mem)).resolve_left ne
    let replacement := insert a (insert b rem)
    have hr : replacement ⊆ pool :=
      Finset.insert_subset ha (Finset.insert_subset hb smaller)
    have cov : asks.biUnion id ⊆ replacement.biUnion id := by
      intro x hx
      obtain ⟨s,hs,hx⟩ := Finset.mem_biUnion.mp hx
      by_cases eq : s=a∪b
      · subst s
        rcases Finset.mem_union.mp hx with xa|xb
        · exact Finset.mem_biUnion.mpr ⟨_,Finset.mem_insert_self _ _,xa⟩
        · exact Finset.mem_biUnion.mpr ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),xb⟩
      · exact Finset.mem_biUnion.mpr ⟨s,Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨eq,hs⟩)),hx⟩
    have size := h replacement hr
    have r1 := Finset.card_insert_le a (insert b rem)
    have r2 := Finset.card_insert_le b rem
    have r3 : rem.card+1=asks.card := Finset.card_erase_add_one occurs
    exact (Finset.card_le_card cov).trans (by dsimp [replacement] at size ⊢; omega)
  · have orig : asks ⊆ pool := fun v hv => (Finset.mem_insert.mp (sub hv)).resolve_left
        (fun eq => occurs (eq ▸ hv))
    exact (h asks orig).trans (by omega)

theorem one {pool : Family α} {n : Nat} (h : cap pool n) {a : Finset α} (ha : a∈pool) :
    a.card ≤ n+1 := by
  simpa [Nat.add_comm] using h {a} (Finset.singleton_subset_iff.mpr ha)
end PlanePairUnion

namespace PlanePairClean
open PlanePairRows
abbrev R := Finset V
abbrev Group := Finset E
def onRow (r : Nat) (u : V) := (varWord u).getLsbD r
def Hits (X : R) (r : Nat) : Prop := ∃ u∈X, onRow r u=true
def N (c : V) := Finset.univ.filter fun u => adjacent c u
def star (c : V) (X : R) : Group :=
  Finset.univ.filter fun e : E => onRow e.val c = true ∧ ∃ u∈X, onRow e.val u=true

theorem star_mem {c X e} : e ∈ star c X ↔ onRow e.val c=true ∧ Hits X e.val := by
  simp [star,Hits]

theorem star_union (c : V) (X Y : R) : star c (X∪Y)=star c X ∪ star c Y := by
  ext e
  simp only [star_mem,Finset.mem_union,Hits]
  aesop

def negPart (v : V) : BitVec 273 := (varWord v).extractLsb' 52 273

theorem negPart_bit (v : V) (k : Fin 273) : (negPart v).getLsbD k.val = onRow (rneg k) v := by
  simp only [negPart,onRow,rneg,BitVec.getLsbD_extractLsb',k.isLt,decide_true,Bool.true_and]

set_option maxHeartbeats 4000000 in
theorem adjacent_certificate : ∀ u v : V,
    adjacent u v = true ↔ negPart u &&& negPart v = 0 := by decide +kernel

theorem adj_iff_neg (u v : V) :
    adjacent u v=true ↔ ∀ k : Fin 273, ¬ (onRow (rneg k) u=true ∧ onRow (rneg k) v=true) := by
  rw [adjacent_certificate,BitVec.eq_of_getLsbD_eq_iff]
  constructor
  · intro h k
    have hz := h k.val k.isLt
    intro ⟨hu,hv⟩
    rw [BitVec.getLsbD_and, negPart_bit u k, negPart_bit v k, hu, hv] at hz
    simp at hz
  · intro h i hi
    have hn := h ⟨i,hi⟩
    have bu := negPart_bit u ⟨i,hi⟩
    have bv := negPart_bit v ⟨i,hi⟩
    change (negPart u).getLsbD i = _ at bu
    change (negPart v).getLsbD i = _ at bv
    simp only [BitVec.getLsbD_and,bu,bv]
    cases hu : onRow (rneg ⟨i,hi⟩) u <;> cases hv : onRow (rneg ⟨i,hi⟩) v <;> simp_all

theorem adj_sym (u v : V) : adjacent u v=adjacent v u := by revert u v; decide +kernel

theorem neighbor_iff {c u : V} : u∈N c ↔ adjacent c u=true := by simp [N]

theorem unique_center {c d : V} {X : R} (large : 2≤X.card) (a : X ⊆ N c) (b : X ⊆ N d) : c=d := by
  by_contra ne
  obtain ⟨u,hu,v,hv,uv⟩ := Finset.one_lt_card.mp large
  have q := no_square c d u v ne uv (neighbor_iff.mp (a hu)) (neighbor_iff.mp (a hv))
      (neighbor_iff.mp (b hu))
  simp [neighbor_iff.mp (b hv)] at q

theorem thin_side {X Y : R}
    (safe : ∀ u∈X, ∀ v∈Y, adjacent u v=true) : X.card≤1 ∨ Y.card≤1 := by
  by_cases small : X.card≤1
  · exact Or.inl small
  · right
    by_contra! hy
    obtain ⟨u,hu,v,hv,uv⟩ := Finset.one_lt_card.mp (show 1<X.card by omega)
    obtain ⟨w,hw,z,hz,wz⟩ := Finset.one_lt_card.mp hy
    have q := no_square u v w z uv wz (safe _ hu _ hw) (safe _ hu _ hz) (safe _ hv _ hw)
    simp [safe _ hv _ hz] at q

set_option maxHeartbeats 4000000 in
theorem simple_star : ∀ c v : V, v∈N c → (star c {v}).card ≤ 1 := by
  decide +kernel

theorem star_small (c : V) (X : R) (sub : X⊆N c) (s : X.card≤1) : (star c X).card≤1 := by
  by_cases he : X=∅
  · subst X
    simp [star]
  · have hn := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
    obtain ⟨v,hv⟩ := Finset.card_eq_one.mp (show X.card=1 by omega)
    subst X
    exact simple_star _ _ (sub (Finset.mem_singleton_self _))

def matched : Fin 13 → E := ![0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48]
set_option maxHeartbeats 4000000 in
theorem disjoint_matching : ∀ i j : Fin 13, ∀ v : V,
    onRow (matched i).val v=true → onRow (matched j).val v=true → i=j := by decide +kernel
theorem matching_cover (X : R) (h : ∀ e : E, Hits X e.val) : 13≤X.card := by
  classical
  have representatives (i : Fin 13) : ∃ v : X, onRow (matched i).val v.val=true := by
    obtain ⟨v,hv,hon⟩ := h (matched i)
    exact ⟨⟨v,hv⟩,hon⟩
  choose f hf using representatives
  have inj : Function.Injective f := by
    intro i j eq
    exact disjoint_matching i j (f i).val (hf i) (eq.symm ▸ hf j)
  simpa using Fintype.card_le_of_injective _ inj

theorem raw_alive : ∀ v : V, ∃ r : Fin 273, onRow (rneg r) v=true := by decide +kernel
theorem target_pos : ∀ e : E, goal.getLsbD e.val=true := by decide +kernel
theorem target_neg : ∀ r : Fin 273, goal.getLsbD (rneg r)=false := by decide +kernel
end PlanePairClean

namespace PlanePairClean
open PlanePairRows PlanePairUnion
structure Pool where
  rich : Family E
  light : Family V
  claimed : Family E

structure Budget (s : Pool) (r l t : Nat) : Prop where
  richCost : cap s.rich r
  lightCost : cap s.light l
  claimCost : s.claimed.card ≤ t
  covers : s.claimed ⊆ s.rich
  richSmall : ∀ a : Group, a.card≤1 → a∈s.rich
  lightSmall : ∀ a : R, a.card≤1 → a∈s.light

structure Extends (s z : Pool) : Prop where
  rich : s.rich ⊆ z.rich
  light : s.light ⊆ z.light
  claimed : s.claimed ⊆ z.claimed

def blocks (s : Pool) := s.claimed.biUnion id
def Dom (w : Word) (X : R) : Prop := ∀ e : E, w.getLsbD e.val=true → Hits X e.val
structure Wire (s : Pool) (w : Word) (X : R) : Prop where
  rawSound : ∀ r, Hits X r → w.getLsbD r=true
  origin : ∀ e : E, w.getLsbD e.val=true → Hits X e.val ∨ e∈blocks s
  group : ∀ c, X⊆N c → star c X∈s.rich
  cover : X.card≤1 → ∃ Y∈s.light, Dom w Y

def Ready (s : Pool) (w : Word) := ∃ X, Wire s w X
theorem widen {s z} (h : Extends s z) {w X} (hw : Wire s w X) : Wire z w X := by
  refine ⟨hw.rawSound,?_,fun c hc => h.rich (hw.group c hc),?_⟩
  · intro e yes
    rcases hw.origin e yes with hx|hb
    · exact Or.inl hx
    · obtain ⟨block,mem,hit⟩ := Finset.mem_biUnion.mp hb
      exact Or.inr (Finset.mem_biUnion.mpr ⟨_,h.claimed mem,hit⟩)
  · intro small
    obtain ⟨Y,hy,d⟩ := hw.cover small
    exact ⟨Y,h.light hy,d⟩

def units (α : Type) [Fintype α] [DecidableEq α] :=
  (Finset.univ : Finset α).powerset.filter fun t => t.card≤1
theorem in_units {α : Type} [Fintype α] [DecidableEq α] (x : Finset α) :
    x ∈ units α ↔ x.card≤1 := by simp [units]
def start : Pool := ⟨units E,units V,∅⟩
theorem startBudget : Budget start 0 0 0 := by
  exact ⟨small (fun _ h => (in_units _).mp h), small (fun _ h => (in_units _).mp h),
    by simp [start],Finset.empty_subset _, fun _ h => (in_units _).mpr h, fun _ h => (in_units _).mpr h⟩

theorem zero_wire {s r l t} (B : Budget s r l t) : Wire s 0 ∅ := by
  refine ⟨by simp [Hits], by simp, ?_,?_⟩
  · intro c sub
    exact B.richSmall _ (star_small _ _ sub (by simp))
  · intro _
    exact ⟨∅,B.lightSmall _ (by simp),by simp [Dom]⟩

theorem input_wire {s r l t} (B : Budget s r l t) (v : V) : Wire s (varWord v) {v} := by
  refine ⟨?_,?_,?_,?_⟩
  · simp [Hits,onRow]
  · intro e h
    exact Or.inl ⟨v,by simp,h⟩
  · intro c sub
    exact B.richSmall _ (star_small _ _ sub (by simp))
  · intro _
    exact ⟨{v},B.lightSmall _ (by simp),fun e h => ⟨v,by simp,h⟩⟩

theorem addRich {s r l t} (B : Budget s r l t) (x y : Group) (hx : x∈s.rich) (hy : y∈s.rich) :
    let z : Pool := {s with rich := insert (x∪y) s.rich}
    Extends s z ∧ Budget z (r+1) l t := by
  exact ⟨⟨Finset.subset_insert _ _,Finset.Subset.rfl,Finset.Subset.rfl⟩,
    merge B.richCost hx hy,B.lightCost,B.claimCost,B.covers.trans (Finset.subset_insert _ _),
    fun a h => Finset.mem_insert_of_mem (B.richSmall a h),B.lightSmall⟩

theorem addLight {s r l t} (B : Budget s r l t) (x y : R) (hx : x∈s.light) (hy : y∈s.light) :
    let z : Pool := {s with light := insert (x∪y) s.light}
    Extends s z ∧ Budget z r (l+1) t := by
  exact ⟨⟨Finset.Subset.rfl,Finset.subset_insert _ _,Finset.Subset.rfl⟩,
    B.richCost,merge B.lightCost hx hy,B.claimCost,B.covers,B.richSmall,
    fun a h => Finset.mem_insert_of_mem (B.lightSmall a h)⟩

theorem addBlock {s r l t} (B : Budget s r l t) (x : Group) (hx : x∈s.rich) :
    let z : Pool := {s with claimed := insert x s.claimed}
    Extends s z ∧ Budget z r l (t+1) := by
  exact ⟨⟨Finset.Subset.rfl,Finset.Subset.rfl,Finset.subset_insert _ _⟩,
    B.richCost,B.lightCost,(Finset.card_insert_le _ _).trans (by have := B.claimCost;omega),
    Finset.insert_subset hx B.covers,B.richSmall,B.lightSmall⟩
end PlanePairClean

namespace PlanePairClean
open PlanePairRows PlanePairUnion

def Advance (s : Pool) (r l t : Nat) (w : Word) : Prop :=
  ∃ z r' l' t', Extends s z ∧ Budget z r' l' t' ∧ r'+l'+t'=r+l+t+1 ∧ Ready z w

theorem hits_union {X Y : R} {r : Nat} : Hits (X∪Y) r ↔ Hits X r ∨ Hits Y r := by
  simp only [Hits,Finset.mem_union]
  aesop

theorem or_wire {z : Pool} {a b : Word} {X Y : R} (ha : Wire z a X) (hb : Wire z b Y)
    (groups : ∀ c,X∪Y⊆N c → star c (X∪Y)∈z.rich)
    (light : (X∪Y).card≤1 → ∃ P∈z.light, Dom (a|||b) P) :
    Wire z (a|||b) (X∪Y) := by
  refine ⟨?_,?_,groups,light⟩
  · intro r h
    rcases hits_union.mp h with h|h
    · simp [ha.rawSound _ h]
    · simp [hb.rawSound _ h]
  · intro e h
    have split : a.getLsbD e.val=true ∨ b.getLsbD e.val=true := by simpa using h
    rcases split with yes|yes
    · exact (ha.origin _ yes).imp_left (fun v => hits_union.mpr (Or.inl v))
    · exact (hb.origin _ yes).imp_left (fun v => hits_union.mpr (Or.inr v))

theorem or_step {s r l t a b X Y} (B : Budget s r l t) (ha : Wire s a X) (hb : Wire s b Y) :
    Advance s r l t (a|||b) := by
  classical
  by_cases small : (X∪Y).card≤1
  · have sx := (Finset.card_le_card (Finset.subset_union_left (s₁:=X) (s₂:=Y))).trans small
    have sy := (Finset.card_le_card (Finset.subset_union_right (s₁:=X) (s₂:=Y))).trans small
    obtain ⟨P,hp,cp⟩ := ha.cover sx
    obtain ⟨Q,hq,cq⟩ := hb.cover sy
    let z : Pool := {s with light := insert (P∪Q) s.light}
    obtain ⟨ext,bud⟩ := addLight B _ _ hp hq
    refine ⟨z,r,l+1,t,ext,bud,by omega,X∪Y,or_wire (widen ext ha) (widen ext hb) ?_ ?_⟩
    · exact fun c sub => bud.richSmall _ (star_small c _ sub small)
    · intro _
      refine ⟨P∪Q,Finset.mem_insert_self _ _,?_⟩
      intro e h
      have split : a.getLsbD e.val=true ∨ b.getLsbD e.val=true := by simpa using h
      exact hits_union.mpr (split.imp (cp e) (cq e))
  · by_cases ok : ∃ c, X∪Y⊆N c
    · obtain ⟨c,hc⟩ := ok
      have hx := ha.group c (Finset.subset_union_left.trans hc)
      have hy := hb.group c (Finset.subset_union_right.trans hc)
      let z : Pool := {s with rich := insert (star c X ∪ star c Y) s.rich}
      obtain ⟨ext,bud⟩ := addRich B _ _ hx hy
      refine ⟨z,r+1,l,t,ext,bud,by omega,X∪Y,or_wire (widen ext ha) (widen ext hb) ?_ ?_⟩
      · intro d sub
        have eq := unique_center (X:=X∪Y) (by omega) sub hc
        subst d
        rw [star_union]
        exact Finset.mem_insert_self _ _
      · exact fun h => False.elim (small h)
    · have h0 := B.richSmall ∅ (by simp)
      obtain ⟨ext,bud⟩ := addRich B _ _ h0 h0
      refine ⟨_,r+1,l,t,ext,bud,by omega,X∪Y,or_wire (widen ext ha) (widen ext hb) ?_ ?_⟩
      · exact fun c hc => False.elim (ok ⟨c,hc⟩)
      · exact fun h => False.elim (small h)

def clean (w : Word) : Prop := ∀ k : Fin 273, w.getLsbD (rneg k)=false

theorem safe_raw {s a b X Y} (ha : Wire s a X) (hb : Wire s b Y) (safe : clean (a&&&b)) :
    ∀ u∈X, ∀ v∈Y, adjacent u v=true := by
  intro u hu v hv
  apply (adj_iff_neg _ _).mpr
  intro k both
  have h₁ := ha.rawSound _ ⟨u,hu,both.1⟩
  have h₂ := hb.rawSound _ ⟨v,hv,both.2⟩
  have no := safe k
  simp [h₁,h₂] at no

theorem rectangle_one {s : Pool} {b : Word} {X Y : R} {r l t}
    (B : Budget s r l t) (hb : Wire s b Y) (small : X.card≤1)
    (safe : ∀ u∈X, ∀ v∈Y, adjacent u v=true) :
    ∃ T∈s.rich, ∀ e : E, Hits X e.val → Hits Y e.val → e∈T := by
  by_cases emp : X=∅
  · subst X
    exact ⟨∅,B.richSmall _ (by simp),by simp [Hits]⟩
  · have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr emp)
    obtain ⟨v,hv⟩ := Finset.card_eq_one.mp (show X.card=1 by omega)
    subst X
    have sub : Y ⊆ N v := fun u hu => neighbor_iff.mpr (safe _ (by simp) _ hu)
    refine ⟨_,hb.group v sub,?_⟩
    intro e vx vy
    exact star_mem.mpr ⟨by simpa [Hits] using vx,vy⟩

theorem and_step {s r l t a b X Y} (B : Budget s r l t) (ha : Wire s a X) (hb : Wire s b Y)
    (safe : clean (a&&&b)) : Advance s r l t (a&&&b) := by
  have paired := safe_raw ha hb safe
  have thin := thin_side paired
  have rectangle : ∃ T∈s.rich, ∀ e : E, Hits X e.val → Hits Y e.val → e∈T := by
    rcases thin with x|y
    · exact rectangle_one B hb x paired
    · have sym u (hu : u∈Y) v (hv : v∈X) : adjacent u v=true := by rw [adj_sym];exact paired _ hv _ hu
      obtain ⟨T,m,h⟩ := rectangle_one B ha y sym
      exact ⟨T,m,fun e hh gg => h e gg hh⟩
  obtain ⟨block,mem,rect⟩ := rectangle
  let z : Pool := {s with claimed := insert block s.claimed}
  obtain ⟨ext,bud⟩ := addBlock B block mem
  refine ⟨z,r,l,t+1,ext,bud,by omega,∅,?_,?_,?_,?_⟩
  · simp [Hits]
  · intro e yes
    have on : a.getLsbD e.val=true ∧ b.getLsbD e.val=true := by simpa using yes
    rcases (widen ext ha).origin e on.1 with ax|old
    · rcases (widen ext hb).origin e on.2 with byy|old
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨block,Finset.mem_insert_self _ _,rect _ ax byy⟩)
      · exact Or.inr old
    · exact Or.inr old
  · exact fun c sub => bud.richSmall _ (star_small _ _ sub (by simp))
  · intro _
    rcases thin with sm|sm
    · obtain ⟨P,memP,dom⟩ := ha.cover sm
      exact ⟨P,memP,fun e h => dom e ((Bool.and_eq_true_iff.mp (by simpa only [BitVec.getLsbD_and] using h)).1)⟩
    · obtain ⟨P,memP,dom⟩ := hb.cover sm
      exact ⟨P,memP,fun e h => dom e ((Bool.and_eq_true_iff.mp (by simpa only [BitVec.getLsbD_and] using h)).2)⟩
end PlanePairClean


namespace PlanePairClean
open PlanePairRows PlanePairUnion
theorem output_lower {s r l t} (B : Budget s r l t) (h : Ready s goal) : 64 ≤ r+l+t := by
  obtain ⟨X,w⟩ := h
  have emp : X=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨k,hk⟩ := raw_alive v
    have yes := w.rawSound _ ⟨v,hv,hk⟩
    rw [target_neg k] at yes
    contradiction
  subst X
  have all : blocks s = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro e
    have v := w.origin e (target_pos e)
    simpa [Hits] using v
  obtain ⟨P,hP,dom⟩ := w.cover (by simp)
  have lb1 := matching_cover P (fun e => dom e (target_pos e))
  have lb2 := one B.lightCost hP
  have area := B.richCost s.claimed B.covers
  change (blocks s).card ≤ s.claimed.card+r at area
  rw [all] at area
  simp only [Finset.card_univ,Fintype.card_fin] at area
  have claimed := B.claimCost
  omega


end PlanePairClean

namespace PlanePairClean
open PlanePairRows PlanePairUnion PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ones : Word := BitVec.allOnes 325
@[local simp] theorem ones_or (w : Word) : ones ||| w = ones := BitVec.allOnes_or
@[local simp] theorem or_ones (w : Word) : w ||| ones = ones := BitVec.or_allOnes
@[local simp] theorem ones_and (w : Word) : ones &&& w = w := BitVec.allOnes_and
@[local simp] theorem and_ones (w : Word) : w &&& ones = w := BitVec.and_allOnes
def sparse (w : Word) : Prop := ∃ pivot : E, ∀ e : E, w.getLsbD e.val=true → e=pivot
def gateWord (g : Gate) (w : List Word) : Word :=
  let vs := g.inputs.map fun i => w.getD i 0
  match g.op with
  | .and => vs.foldr (· &&& ·) ones
  | .or => vs.foldr (· ||| ·) 0
  | _ => 0
def tick (w : List Word) (g : Gate) := w ++ [gateWord g w]

def permit (g : Gate) (w : List Word) : Prop :=
  ∀ i j, g.op = .and → g.inputs = [i,j] →
    let a := w.getD i 0
    let b := w.getD j 0
    a &&& b = a ∨ a &&& b = b ∨ sparse (a &&& b) ∨ clean (a &&& b)

def permitted (w : List Word) : List Gate → Prop
  | [] => True
  | g :: gs => permit g w ∧ permitted (tick w g) gs

def OK (s : Pool) (w : Word) : Prop := w = ones ∨ Ready s w
def UpTo (s : Pool) (r l t : Nat) (w : Word) : Prop :=
  ∃ z R L T, Extends s z ∧ Budget z R L T ∧ R+L+T ≤ r+l+t+1 ∧ OK z w

theorem keep {s r l t w} (B : Budget s r l t) (h : OK s w) : UpTo s r l t w :=
  ⟨s,r,l,t,⟨Finset.Subset.rfl,Finset.Subset.rfl,Finset.Subset.rfl⟩,B,by omega,h⟩

theorem spend {s r l t w} (h : Advance s r l t w) : UpTo s r l t w := by
  obtain ⟨z,R,L,T,ext,B,eq,ok⟩ := h
  exact ⟨z,R,L,T,ext,B,by omega,Or.inr ok⟩

theorem up_or {s r l t a b} (B : Budget s r l t) (ha : OK s a) (hb : OK s b) :
    UpTo s r l t (a ||| b) := by
  rcases ha with rfl|⟨X,hX⟩
  · apply keep B (Or.inl _)
    simp
  rcases hb with rfl|⟨Y,hY⟩
  · apply keep B (Or.inl _)
    simp
  exact spend (or_step B hX hY)

theorem has_end : ∀ e : E, ∃ v : V, onRow e.val v = true := by decide +kernel
theorem up_sparse {s r l t w} (B : Budget s r l t) (few : sparse w) : UpTo s r l t w := by
  obtain ⟨e,only⟩ := few
  obtain ⟨v,hv⟩ := has_end e
  let z : Pool := {s with claimed := insert {e} s.claimed}
  obtain ⟨ext,bud⟩ := addBlock B {e} (B.richSmall _ (by simp))
  refine ⟨z,r,l,t+1,ext,bud,by omega,Or.inr ⟨∅,?_,?_,?_,?_⟩⟩
  · simp [Hits]
  · intro j h
    have eq := only j h
    subst j
    exact Or.inr (Finset.mem_biUnion.mpr ⟨{e},Finset.mem_insert_self _ _,by simp⟩)
  · intro c sub
    exact bud.richSmall _ (star_small c _ sub (by simp))
  · intro _
    refine ⟨{v},bud.lightSmall _ (by simp),?_⟩
    intro j h
    exact ⟨v,by simp,only j h ▸ hv⟩

theorem up_and {s r l t a b} (B : Budget s r l t) (ha : OK s a) (hb : OK s b)
    (good : a &&& b = a ∨ a &&& b = b ∨ sparse (a &&& b) ∨ clean (a &&& b)) : UpTo s r l t (a &&& b) := by
  rcases good with same|same|few|cleaned
  · rw [same]; exact keep B ha
  · rw [same]; exact keep B hb
  · exact up_sparse B few
  rcases ha with rfl|⟨X,hX⟩
  · simpa using keep B hb
  rcases hb with rfl|⟨Y,hY⟩
  · simpa using keep B (show OK s a from Or.inr ⟨X,hX⟩)
  exact spend (and_step B hX hY cleaned)

theorem allowed_tick {s r l t} (B : Budget s r l t) (w : List Word)
    (old : ∀ x ∈ w, OK s x) (g : Gate) (hop : g.op = .and ∨ g.op = .or)
    (hlen : g.inputs.length ≤ 2) (p : permit g w) : UpTo s r l t (gateWord g w) := by
  have lookup (i : Nat) : OK s (w.getD i 0) := by
    by_cases h : i < w.length
    · rw [List.getD_eq_getElem _ _ h]; exact old _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inr ⟨_,zero_wire B⟩
  rcases eq : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rcases hop with h|h
    · simpa [gateWord,h,eq] using keep B (show OK s ones from Or.inl rfl)
    · simpa [gateWord,h,eq] using keep B (show OK s 0 from Or.inr ⟨_,zero_wire B⟩)
  · rcases hop with h|h <;> simpa [gateWord,h,eq] using keep B (lookup a)
  · rcases hop with h|h
    · simpa [gateWord,h,eq] using up_and B (lookup a) (lookup b) (p a b h eq)
    · simpa [gateWord,h,eq] using up_or B (lookup a) (lookup b)
  · simp [eq] at hlen

theorem word_program (gs : List Gate) (w : List Word) {s r l t} (B : Budget s r l t)
    (ops : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (old : ∀ x ∈ w, OK s x) (p : permitted w gs) :
    ∃ z R L T, Budget z R L T ∧ R+L+T ≤ r+l+t+gs.length ∧ ∀ x ∈ gs.foldl tick w, OK z x := by
  induction gs generalizing w s r l t with
  | nil => exact ⟨s,r,l,t,B,by simp,old⟩
  | cons g gs ih =>
    have hg := ops g List.mem_cons_self
    obtain ⟨m,r',l',t',ext,bud,cost,new⟩ := allowed_tick B w old g hg.1 hg.2 p.1
    have next : ∀ x ∈ tick w g, OK m x := by
      intro x hx
      rcases List.mem_append.mp hx with prior|last
      · rcases old x prior with h|⟨X,hX⟩
        · exact Or.inl h
        · exact Or.inr ⟨X,widen ext hX⟩
      · exact List.mem_singleton.mp last ▸ new
    obtain ⟨z,R,L,T,Bz,sz,endok⟩ := ih _ bud (fun g' hg' => ops g' (List.mem_cons_of_mem _ hg')) next p.2
    exact ⟨z,R,L,T,Bz,by simp only [List.length_cons];omega,endok⟩

theorem word_lower (C : Circuit) (hm : Monotone2 C) (h : permitted words C.gates)
    (hit : (C.gates.foldl tick words).getD C.output 0 = goal) : 64 ≤ C.size := by
  obtain ⟨s,r,l,t,B,sz,ready⟩ := word_program C.gates words startBudget
    (fun g hg => by simpa using hm g hg) (by
      intro x hx
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hx
      have len : words.length=26 := rfl
      let j : V := ⟨i.val, by rw [←len]; exact i.isLt⟩
      exact Or.inr ⟨_, by simpa [varWord,j,List.getD_eq_getElem?_getD,i.isLt] using input_wire startBudget j⟩) h
  have meet : goal ∈ C.gates.foldl tick words := by
    by_cases hi : C.output < (C.gates.foldl tick words).length
    · rw [List.getD_eq_getElem _ _ hi] at hit
      exact hit ▸ List.getElem_mem hi
    · rw [List.getD_eq_default _ _ (by omega)] at hit
      exact False.elim ((by decide : (0 : Word) ≠ goal) hit)
  rcases ready goal meet with eq|ok
  · exact False.elim ((by decide : goal ≠ ones) eq)
  have bound := output_lower B ok
  change 64 ≤ C.gates.length
  omega
end PlanePairClean

namespace PlanePairClean
open PlanePairRows PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def bitAt (k : Nat) (a : Word) := a.getLsbD k
theorem map_lookup (k i : Nat) (w : List Word) :
    (w.map (bitAt k)).getD i false = bitAt k (w.getD i 0) := by
  by_cases h : i<w.length <;> simp [List.getD_eq_getElem?_getD,h,bitAt]

theorem read_and (k : Fin 325) (xs : List Word) :
    bitAt k.val (xs.foldr (· &&& ·) ones) = (xs.map (bitAt k.val)).all id := by
  induction xs with
  | nil => exact (BitVec.getLsbD_allOnes.trans (decide_eq_true k.isLt))
  | cons a xs ih => simp [bitAt] at ih ⊢; rw [ih]

theorem read_or (k : Fin 325) (xs : List Word) :
    bitAt k.val (xs.foldr (· ||| ·) 0) = (xs.map (bitAt k.val)).any id := by
  induction xs with
  | nil => simp [bitAt]
  | cons a xs ih => simp [bitAt] at ih ⊢; rw [ih]

theorem eval_step (k : Fin 325) (g : Gate) (w : List Word) (h : g.op = .and ∨ g.op = .or) :
    bitAt k.val (gateWord g w) = g.op.eval (g.inputs.map fun i => (w.map (bitAt k.val)).getD i false) := by
  rcases h with h|h
  · simp only [gateWord,h,read_and,GateOp.eval,List.map_map,Function.comp_def,map_lookup]
  · simp only [gateWord,h,read_or,GateOp.eval,List.map_map,Function.comp_def,map_lookup]

theorem rows_run (k : Fin 325) (gs : List Gate) (w : List Word)
    (hm : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    (gs.foldl tick w).map (bitAt k.val) =
      gs.foldl (fun xs g => xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]) (w.map (bitAt k.val)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (tick w g) (fun g' hg' => hm g' (List.mem_cons_of_mem _ hg'))]
    rw [tick,List.map_append,List.map_singleton,eval_step k g w (hm g List.mem_cons_self)]

theorem word_output (C : Circuit) (hm : Monotone2 C) (k : Fin 325) :
    bitAt k.val ((C.gates.foldl tick words).getD C.output 0) = C.eval (words.map (bitAt k.val)) := by
  rw [← map_lookup,rows_run k C.gates words (fun g hg => by simpa using (hm g hg).1)]
  rfl

def diff : Finset (Fin 13) := {0,1,3,9}
def point (e : E) : Fin 13 := ⟨e.val/4, by omega⟩
def line (e : E) : Fin 13 := point e - (![0,1,3,9] : Fin 4 → Fin 13) ⟨e.val%4, by omega⟩
def edgeInput (p l : Fin 13) (i : Fin 26) := decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
def setInput (P L : Finset (Fin 13)) (i : Fin 26) :=
  decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨ ∃ l ∈ L, i = Fin.natAdd 13 l)
def ptSet (j : Fin 273) : Finset (Fin 13) := (#[{0,1}, {0,2}, {0,3}, {0,4}, {0,5}, {0,6}, {0,7}, {0,8}, {0,9}, {0,10}, {0,11}, {0,12}, {0}, {0}, {0}, {0}, {0}, {0}, {0}, {0}, {0}, {1,2}, {1,3}, {1,4}, {1,5}, {1,6}, {1,7}, {1,8}, {1,9}, {1,10}, {1,11}, {1,12}, {1}, {1}, {1}, {1}, {1}, {1}, {1}, {1}, {1}, {2,3}, {2,4}, {2,5}, {2,6}, {2,7}, {2,8}, {2,9}, {2,10}, {2,11}, {2,12}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {2}, {3,4}, {3,5}, {3,6}, {3,7}, {3,8}, {3,9}, {3,10}, {3,11}, {3,12}, {3}, {3}, {3}, {3}, {3}, {3}, {3}, {3}, {3}, {4,5}, {4,6}, {4,7}, {4,8}, {4,9}, {4,10}, {4,11}, {4,12}, {4}, {4}, {4}, {4}, {4}, {4}, {4}, {4}, {4}, {5,6}, {5,7}, {5,8}, {5,9}, {5,10}, {5,11}, {5,12}, {5}, {5}, {5}, {5}, {5}, {5}, {5}, {5}, {5}, {6,7}, {6,8}, {6,9}, {6,10}, {6,11}, {6,12}, {6}, {6}, {6}, {6}, {6}, {6}, {6}, {6}, {6}, {7,8}, {7,9}, {7,10}, {7,11}, {7,12}, {7}, {7}, {7}, {7}, {7}, {7}, {7}, {7}, {7}, {8,9}, {8,10}, {8,11}, {8,12}, {8}, {8}, {8}, {8}, {8}, {8}, {8}, {8}, {8}, {9,10}, {9,11}, {9,12}, {9}, {9}, {9}, {9}, {9}, {9}, {9}, {9}, {9}, {10,11}, {10,12}, {10}, {10}, {10}, {10}, {10}, {10}, {10}, {10}, {10}, {11,12}, {11}, {11}, {11}, {11}, {11}, {11}, {11}, {11}, {11}, {12}, {12}, {12}, {12}, {12}, {12}, {12}, {12}, {12}, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅] : Array (Finset (Fin 13)))[j.val]!
def lnSet (j : Fin 273) : Finset (Fin 13) := (#[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, {1}, {2}, {3}, {5}, {6}, {7}, {8}, {9}, {11}, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, {2}, {3}, {4}, {6}, {7}, {8}, {9}, {10}, {12}, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, {0}, {3}, {4}, {5}, {7}, {8}, {9}, {10}, {11}, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, {1}, {4}, {5}, {6}, {8}, {9}, {10}, {11}, {12}, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, {0}, {2}, {5}, {6}, {7}, {9}, {10}, {11}, {12}, ∅, ∅, ∅, ∅, ∅, ∅, ∅, {0}, {1}, {3}, {6}, {7}, {8}, {10}, {11}, {12}, ∅, ∅, ∅, ∅, ∅, ∅, {0}, {1}, {2}, {4}, {7}, {8}, {9}, {11}, {12}, ∅, ∅, ∅, ∅, ∅, {0}, {1}, {2}, {3}, {5}, {8}, {9}, {10}, {12}, ∅, ∅, ∅, ∅, {0}, {1}, {2}, {3}, {4}, {6}, {9}, {10}, {11}, ∅, ∅, ∅, {1}, {2}, {3}, {4}, {5}, {7}, {10}, {11}, {12}, ∅, ∅, {0}, {2}, {3}, {4}, {5}, {6}, {8}, {11}, {12}, ∅, {0}, {1}, {3}, {4}, {5}, {6}, {7}, {9}, {12}, {0}, {1}, {2}, {4}, {5}, {6}, {7}, {8}, {10}, {0,1}, {0,2}, {0,3}, {0,4}, {0,5}, {0,6}, {0,7}, {0,8}, {0,9}, {0,10}, {0,11}, {0,12}, {1,2}, {1,3}, {1,4}, {1,5}, {1,6}, {1,7}, {1,8}, {1,9}, {1,10}, {1,11}, {1,12}, {2,3}, {2,4}, {2,5}, {2,6}, {2,7}, {2,8}, {2,9}, {2,10}, {2,11}, {2,12}, {3,4}, {3,5}, {3,6}, {3,7}, {3,8}, {3,9}, {3,10}, {3,11}, {3,12}, {4,5}, {4,6}, {4,7}, {4,8}, {4,9}, {4,10}, {4,11}, {4,12}, {5,6}, {5,7}, {5,8}, {5,9}, {5,10}, {5,11}, {5,12}, {6,7}, {6,8}, {6,9}, {6,10}, {6,11}, {6,12}, {7,8}, {7,9}, {7,10}, {7,11}, {7,12}, {8,9}, {8,10}, {8,11}, {8,12}, {9,10}, {9,11}, {9,12}, {10,11}, {10,12}, {11,12}] : Array (Finset (Fin 13)))[j.val]!

def Positives (C : Circuit) := ∀ p l : Fin 13, p-l ∈ diff → circuitFun 26 C (edgeInput p l) = true
def Negatives (C : Circuit) := ∀ P L : Finset (Fin 13),
    (∀ p ∈ P, ∀ l ∈ L, p - l ∉ diff) →
    (∀ l : Fin 13, (P.filter fun p => p - l ∈ diff).card ≤ 2) →
    (∀ p : Fin 13, (L.filter fun l => p - l ∈ diff).card ≤ 2) →
    circuitFun 26 C (setInput P L) = false

theorem pos_inc : ∀ e : E, point e - line e ∈ diff := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem pos_row : ∀ e : E, words.map (bitAt e.val) = List.ofFn (edgeInput (point e) (line e)) := by decide +kernel

theorem pos_get (C : Circuit) (p : Positives C) (e : E) :
    C.eval (words.map (bitAt e.val)) = true := by
  rw [pos_row]
  exact p _ _ (pos_inc e)

set_option maxHeartbeats 4000000 in
theorem neg_inc : ∀ j : Fin 273, ∀ p ∈ ptSet j, ∀ l ∈ lnSet j, p - l ∉ diff := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem neg_pt : ∀ j : Fin 273, ∀ l : Fin 13, ((ptSet j).filter fun p => p-l ∈ diff).card ≤ 2 := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem neg_ln : ∀ j : Fin 273, ∀ p : Fin 13, ((lnSet j).filter fun l => p-l ∈ diff).card ≤ 2 := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem neg_row : ∀ j : Fin 273, words.map (bitAt (rneg j)) = List.ofFn (setInput (ptSet j) (lnSet j)) := by decide +kernel

theorem neg_get (C : Circuit) (h : Negatives C) (j : Fin 273) :
    C.eval (words.map (bitAt (rneg j))) = false := by
  rw [neg_row]
  exact h _ _ (neg_inc j) (neg_pt j) (neg_ln j)

theorem actual_lower (C : Circuit) (hm : Monotone2 C) (p : Positives C) (n : Negatives C)
    (allowed : permitted words C.gates) : 64 ≤ C.size := by
  apply word_lower C hm allowed
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  change bitAt i _ = _
  rw [word_output C hm ⟨i,hi⟩]
  change C.eval (words.map (bitAt i)) = goal.getLsbD i
  by_cases ip : i<52
  · let e : E := ⟨i,ip⟩
    exact (pos_get C p e).trans (target_pos e).symm
  · let j : Fin 273 := ⟨i-52,by omega⟩
    have eq : rneg j=i := by simp [rneg,j]; omega
    rw [← eq]
    exact (neg_get C n j).trans (target_neg j).symm

end PlanePairClean

namespace PlanePairClean
open PlanePairRows PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def obstruction (g : Gate) (w : List Word) : Prop :=
  ∃ i j, g.op = .and ∧ g.inputs = [i,j] ∧
    let a := w.getD i 0
    let b := w.getD j 0
    let v := a &&& b
    v ≠ a ∧ v ≠ b ∧
    (∃ e f : E, e ≠ f ∧ v.getLsbD e.val=true ∧ v.getLsbD f.val=true) ∧
    ∃ k : Fin 273, v.getLsbD (rneg k)=true

theorem obstruct {g : Gate} {w : List Word} (h : ¬ permit g w) : obstruction g w := by
  unfold permit at h
  dsimp only at h
  push Not at h
  obtain ⟨i,j,op,ins,na,nb,np,nc⟩ := h
  let v := w.getD i 0 &&& w.getD j 0
  change ¬ sparse v at np
  change ¬ clean v at nc
  unfold sparse at np
  push Not at np
  obtain ⟨e,he,_⟩ := np 0
  obtain ⟨f,hf,ne⟩ := np e
  unfold clean at nc
  push Not at nc
  obtain ⟨k,hk⟩ := nc
  have yes : v.getLsbD (rneg k)=true := by simpa using hk
  exact ⟨i,j,op,ins,na,nb,⟨e,f,Ne.symm ne,he,hf⟩,k,yes⟩

theorem locate (gs : List Gate) (w : List Word) (h : ¬ permitted w gs) :
    ∃ pre g post, gs = pre ++ g :: post ∧ obstruction g (pre.foldl tick w) := by
  induction gs generalizing w with
  | nil => exact False.elim (h trivial)
  | cons g gs ih =>
    by_cases head : permit g w
    · obtain ⟨pre,found,post,eq,bad⟩ := ih (tick w g) (fun htail => h ⟨head,htail⟩)
      exact ⟨g::pre,found,post,by simp [eq],bad⟩
    · exact ⟨[],g,gs,rfl,obstruct head⟩

theorem distinct_edges : ∀ e f : E, point e = point f → line e = line f → e=f := by decide +kernel
theorem pair_size : ∀ j : Fin 273, (ptSet j).card + (lnSet j).card = 2 := by decide +kernel

theorem must_have_mixed_gate (C : Circuit) (hm : Monotone2 C) (small : C.size ≤ 63)
    (p : Positives C) (n : Negatives C) :
    ∃ pre g post, C.gates = pre ++ g :: post ∧ obstruction g (pre.foldl tick words) := by
  exact locate _ _ (fun h => by have := actual_lower C hm p n h; omega)

end PlanePairClean

namespace PlanePairClean
open PlanePairRows PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def bTick (xs : List Bool) (g : Gate) := xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]
def probe (pre : List Gate) (g : Gate) (x : Fin 26 → Bool) :=
  g.op.eval (g.inputs.map fun i => (pre.foldl bTick (List.ofFn x)).getD i false)

theorem bit_probe (pre : List Gate) (g : Gate) (ops : ∀ h ∈ g::pre, h.op=.and ∨ h.op=.or)
    (k : Fin 325) (x : Fin 26 → Bool) (row : words.map (bitAt k.val) = List.ofFn x) :
    bitAt k.val (gateWord g (pre.foldl tick words)) = probe pre g x := by
  rw [eval_step k g _ (ops _ List.mem_cons_self),rows_run k pre words
    (fun h hh => ops _ (List.mem_cons_of_mem _ hh)),row]
  rfl

def above (x y : List Bool) : Prop := ∀ i, x.getD i false=true → y.getD i false=true

theorem gate_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (rel : above x y) :
    g.op.eval (g.inputs.map fun i => x.getD i false) = true →
    g.op.eval (g.inputs.map fun i => y.getD i false) = true := by
  rcases hop with h | h
  · simp only [h,GateOp.eval,List.all_map,List.all_eq_true,Function.comp_def,id_eq]
    intro hx i hi
    exact rel i (hx i hi)
  · simp only [h,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_def,id_eq]
    rintro ⟨i,hi,hx⟩
    exact ⟨i,hi,rel i hx⟩

theorem get_append_other {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]

theorem get_append_last (L : List Bool) (s : Bool) : (L++[s]).getD L.length false=s := by simp
theorem raw_get {n : Nat} (x : Fin n → Bool) (i : Fin n) : (List.ofFn x).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD]

theorem run_mono (gs : List Gate) (ops : ∀ g ∈ gs, g.op=.and ∨ g.op=.or)
    (x y : List Bool) (len : x.length=y.length) (r : above x y) :
    above (gs.foldl bTick x) (gs.foldl bTick y) := by
  induction gs generalizing x y with
  | nil => exact r
  | cons g gs ih =>
    apply ih (fun h hh => ops _ (List.mem_cons_of_mem _ hh)) (bTick x g) (bTick y g) (by simp [bTick,len])
    intro i
    by_cases last : i=x.length
    · subst i
      change (x++[_]).getD x.length false=true → (y++[_]).getD x.length false=true
      rw [get_append_last,len,get_append_last]
      exact gate_mono g (ops g List.mem_cons_self) x y r
    · change (x++[_]).getD i false=true → (y++[_]).getD i false=true
      rw [get_append_other _ _ _ _ last,get_append_other _ _ _ _ (by omega)]
      exact r i

theorem probe_mono {pre : List Gate} {g : Gate} (ops : ∀ h ∈ g::pre, h.op=.and ∨ h.op=.or)
    {x y : Fin 26 → Bool} (xy : ∀ i, x i=true → y i=true) :
    probe pre g x=true → probe pre g y=true := by
  apply gate_mono g (ops _ List.mem_cons_self) _ _
  apply run_mono pre (fun h hh => ops _ (List.mem_cons_of_mem _ hh)) _ _ (by simp)
  intro i
  by_cases h : i<26
  · change (List.ofFn x).getD (⟨i,h⟩ : Fin 26).val false=true → (List.ofFn y).getD (⟨i,h⟩ : Fin 26).val false=true
    rw [raw_get,raw_get]
    exact xy ⟨i,h⟩
  · simp [List.getD_eq_getElem?_getD,h]

theorem set_mono {P L P' L' : Finset (Fin 13)} (hp : P ⊆ P') (hl : L ⊆ L') (i : Fin 26) :
    setInput P L i=true → setInput P' L' i=true := by
  simp only [setInput,decide_eq_true_eq]
  rintro (⟨p,hp',h⟩ | ⟨l,hl',h⟩)
  · exact Or.inl ⟨p,hp hp',h⟩
  · exact Or.inr ⟨l,hl hl',h⟩

theorem physical_obstruction (C : Circuit) (hm : Monotone2 C) (small : C.size ≤ 63)
    (p : Positives C) (n : Negatives C) :
    ∃ pre g post, C.gates = pre ++ g :: post ∧ g.op=.and ∧ g.inputs.length=2 ∧
      (∃ e f : E, e≠f ∧ probe pre g (edgeInput (point e) (line e))=true ∧
        probe pre g (edgeInput (point f) (line f))=true) ∧
      ∃ j : Fin 273, ∀ (P L : Finset (Fin 13)), ptSet j ⊆ P → lnSet j ⊆ L →
        probe pre g (setInput P L)=true := by
  obtain ⟨pre,g,post,split, i,j,op,ins,_,_,⟨e,f,ef,he,hf⟩,k,hk⟩ := must_have_mixed_gate C hm small p n
  have ops : ∀ h ∈ g::pre, h.op=.and ∨ h.op=.or := by
    intro h hh
    have inC : h ∈ C.gates := by
      rw [split]
      rcases List.mem_cons.mp hh with rfl | inpre
      · exact List.mem_append_right _ List.mem_cons_self
      · exact List.mem_append_left _ inpre
    simpa using (hm h inC).1
  let out := gateWord g (pre.foldl tick words)
  have isWord : out = (pre.foldl tick words).getD i 0 &&& (pre.foldl tick words).getD j 0 := by
    simp [out,gateWord,op,ins,PlanePairClean.and_ones]
  have yes_pos (a : E) (yes : out.getLsbD a.val=true) : probe pre g (edgeInput (point a) (line a))=true :=
    (bit_probe pre g ops ⟨a.val,by omega⟩ _ (pos_row a)).symm.trans yes
  refine ⟨pre,g,post,split,op,by simp [ins],⟨e,f,ef,yes_pos e (isWord ▸ he),yes_pos f (isWord ▸ hf)⟩,k,?_⟩
  intro P L hp hl
  apply probe_mono ops (set_mono hp hl)
  exact (bit_probe pre g ops ⟨rneg k,by simp [rneg];omega⟩ _ (neg_row k)).symm.trans (isWord ▸ hk)
end PlanePairClean

namespace PlanePairClean
open PlanePairRows
abbrev Config := Finset (Fin 13) × Finset (Fin 13)
def maximalConfig (z : Config) : Prop :=
    (∀ p ∈ z.1, ∀ l ∈ z.2, p-l ∉ diff) ∧
    (∀ l : Fin 13, (z.1.filter fun p => p-l ∈ diff).card ≤ 2) ∧
    (∀ p : Fin 13, (z.2.filter fun l => p-l ∈ diff).card ≤ 2) ∧
    (∀ p : Fin 13, p ∉ z.1 → ∃ l ∈ z.2, p-l ∈ diff) ∧
    (∀ l : Fin 13, l ∉ z.2 → ∃ p ∈ z.1, p-l ∈ diff)
def key (z : Config) : ℕ := (∑ p ∈ z.1, 2^p.val) + 8192*(∑ l ∈ z.2, 2^l.val)
def fan (j : Fin 273) := if (ptSet j).Nonempty ∧ (lnSet j).Nonempty then 48 else 27

def block0 : Array Config := #[({6,7,8,12},{0,1,2}), ({5,7,8,11},{0,1,3}), ({0,7,8,9},{1,2,3}), ({6,8,11,12},{0,1,4}), ({6,8,10,12},{0,2,4}), ({6,8,9,12},{1,2,4}), ({6,8,12},{0,1,2,4}), ({2,8,10,11},{0,3,4}), ({1,8,9,10},{2,3,4}), ({4,7,10,12},{0,2,5}), ({0,7,9,12},{1,2,5}), ({2,7,10,11},{0,3,5})]
def block1 : Array Config := #[({0,7,9,11},{1,3,5}), ({0,7,9,10},{2,3,5}), ({0,7,9},{1,2,3,5}), ({2,10,11,12},{0,4,5}), ({3,9,11,12},{1,4,5}), ({2,9,10,11},{3,4,5}), ({2,10,11},{0,3,4,5}), ({5,8,11,12},{0,1,6}), ({4,8,10,12},{0,2,6}), ({5,8,10,11},{0,3,6}), ({0,5,8,11},{1,3,6}), ({5,8,11},{0,1,3,6})]
def block2 : Array Config := #[({0,1,8,10},{2,3,6}), ({8,10,11,12},{0,4,6}), ({3,8,11,12},{1,4,6}), ({8,11,12},{0,1,4,6}), ({1,8,10,12},{2,4,6}), ({8,10,12},{0,2,4,6}), ({1,8,10,11},{3,4,6}), ({8,10,11},{0,3,4,6}), ({1,8,10},{2,3,4,6}), ({4,10,11,12},{0,5,6}), ({0,3,11,12},{1,5,6}), ({0,4,10,12},{2,5,6})]
def block3 : Array Config := #[({4,10,12},{0,2,5,6}), ({3,10,11,12},{4,5,6}), ({10,11,12},{0,4,5,6}), ({3,11,12},{1,4,5,6}), ({5,6,11,12},{0,1,7}), ({0,6,9,12},{1,2,7}), ({0,5,9,11},{1,3,7}), ({2,6,11,12},{0,4,7}), ({6,9,11,12},{1,4,7}), ({6,11,12},{0,1,4,7}), ({1,6,9,12},{2,4,7}), ({6,9,12},{1,2,4,7})]
def block4 : Array Config := #[({1,2,9,11},{3,4,7}), ({2,4,11,12},{0,5,7}), ({0,9,11,12},{1,5,7}), ({0,4,9,12},{2,5,7}), ({0,9,12},{1,2,5,7}), ({0,2,9,11},{3,5,7}), ({0,9,11},{1,3,5,7}), ({2,9,11,12},{4,5,7}), ({2,11,12},{0,4,5,7}), ({9,11,12},{1,4,5,7}), ({2,9,11},{3,4,5,7}), ({4,5,11,12},{0,6,7})]
def block5 : Array Config := #[({0,5,11,12},{1,6,7}), ({5,11,12},{0,1,6,7}), ({0,1,4,12},{2,6,7}), ({0,1,5,11},{3,6,7}), ({0,5,11},{1,3,6,7}), ({0,4,11,12},{5,6,7}), ({4,11,12},{0,5,6,7}), ({0,11,12},{1,5,6,7}), ({0,4,12},{2,5,6,7}), ({5,6,7,12},{0,1,8}), ({6,7,10,12},{0,2,8}), ({0,6,7,12},{1,2,8})]
def block6 : Array Config := #[({6,7,12},{0,1,2,8}), ({2,5,7,10},{0,3,8}), ({0,1,7,10},{2,3,8}), ({2,6,10,12},{0,4,8}), ({1,6,10,12},{2,4,8}), ({6,10,12},{0,2,4,8}), ({2,7,10,12},{0,5,8}), ({0,3,7,12},{1,5,8}), ({0,7,10,12},{2,5,8}), ({7,10,12},{0,2,5,8}), ({0,7,12},{1,2,5,8}), ({0,2,7,10},{3,5,8})]
def block7 : Array Config := #[({2,7,10},{0,3,5,8}), ({0,7,10},{2,3,5,8}), ({2,3,10,12},{4,5,8}), ({2,10,12},{0,4,5,8}), ({0,3,5,12},{1,6,8}), ({0,1,10,12},{2,6,8}), ({0,1,5,10},{3,6,8}), ({0,1,10},{2,3,6,8}), ({1,3,10,12},{4,6,8}), ({1,10,12},{2,4,6,8}), ({0,3,10,12},{5,6,8}), ({0,3,12},{1,5,6,8})]
def block8 : Array Config := #[({0,10,12},{2,5,6,8}), ({3,10,12},{4,5,6,8}), ({2,5,6,12},{0,7,8}), ({0,5,6,12},{1,7,8}), ({5,6,12},{0,1,7,8}), ({0,1,6,12},{2,7,8}), ({0,6,12},{1,2,7,8}), ({0,1,2,5},{3,7,8}), ({1,2,6,12},{4,7,8}), ({2,6,12},{0,4,7,8}), ({1,6,12},{2,4,7,8}), ({0,1,5,12},{6,7,8})]
def block9 : Array Config := #[({0,5,12},{1,6,7,8}), ({0,1,12},{2,6,7,8}), ({0,1,5},{3,6,7,8}), ({6,7,8,11},{0,1,9}), ({4,6,7,8},{0,2,9}), ({0,6,7,8},{1,2,9}), ({6,7,8},{0,1,2,9}), ({2,7,8,11},{0,3,9}), ({0,7,8,11},{1,3,9}), ({7,8,11},{0,1,3,9}), ({0,1,7,8},{2,3,9}), ({0,7,8},{1,2,3,9})]
def block10 : Array Config := #[({2,6,8,11},{0,4,9}), ({3,6,8,11},{1,4,9}), ({6,8,11},{0,1,4,9}), ({1,2,8,11},{3,4,9}), ({2,8,11},{0,3,4,9}), ({2,4,7,11},{0,5,9}), ({0,3,7,11},{1,5,9}), ({0,2,7,11},{3,5,9}), ({2,7,11},{0,3,5,9}), ({0,7,11},{1,3,5,9}), ({0,3,8,11},{1,6,9}), ({0,1,4,8},{2,6,9})]
def block11 : Array Config := #[({0,1,8,11},{3,6,9}), ({0,8,11},{1,3,6,9}), ({0,1,8},{2,3,6,9}), ({1,3,8,11},{4,6,9}), ({3,8,11},{1,4,6,9}), ({1,8,11},{3,4,6,9}), ({0,3,4,11},{5,6,9}), ({0,3,11},{1,5,6,9}), ({2,4,6,11},{0,7,9}), ({0,1,4,6},{2,7,9}), ({0,1,2,11},{3,7,9}), ({1,2,6,11},{4,7,9})]
def block12 : Array Config := #[({2,6,11},{0,4,7,9}), ({1,2,11},{3,4,7,9}), ({0,2,4,11},{5,7,9}), ({2,4,11},{0,5,7,9}), ({0,2,11},{3,5,7,9}), ({0,1,4,11},{6,7,9}), ({0,1,4},{2,6,7,9}), ({0,1,11},{3,6,7,9}), ({0,4,11},{5,6,7,9}), ({0,3,6,7},{1,8,9}), ({0,1,6,7},{2,8,9}), ({0,6,7},{1,2,8,9})]
def block13 : Array Config := #[({0,1,2,7},{3,8,9}), ({0,1,7},{2,3,8,9}), ({1,2,3,6},{4,8,9}), ({0,2,3,7},{5,8,9}), ({0,3,7},{1,5,8,9}), ({0,2,7},{3,5,8,9}), ({0,1,2,6},{7,8,9}), ({0,1,6},{2,7,8,9}), ({0,1,2},{3,7,8,9}), ({1,2,6},{4,7,8,9}), ({5,7,8,12},{0,1,10}), ({4,7,8,12},{0,2,10})]
def block14 : Array Config := #[({7,8,9,12},{1,2,10}), ({7,8,12},{0,1,2,10}), ({2,5,7,8},{0,3,10}), ({5,7,8,9},{1,3,10}), ({5,7,8},{0,1,3,10}), ({1,7,8,9},{2,3,10}), ({7,8,9},{1,2,3,10}), ({3,8,9,12},{1,4,10}), ({1,8,9,12},{2,4,10}), ({8,9,12},{1,2,4,10}), ({1,2,8,9},{3,4,10}), ({1,8,9},{2,3,4,10})]
def block15 : Array Config := #[({2,4,7,12},{0,5,10}), ({3,7,9,12},{1,5,10}), ({4,7,9,12},{2,5,10}), ({4,7,12},{0,2,5,10}), ({7,9,12},{1,2,5,10}), ({2,3,9,12},{4,5,10}), ({3,9,12},{1,4,5,10}), ({4,5,8,12},{0,6,10}), ({3,5,8,12},{1,6,10}), ({5,8,12},{0,1,6,10}), ({1,4,8,12},{2,6,10}), ({4,8,12},{0,2,6,10})]
def block16 : Array Config := #[({1,3,8,12},{4,6,10}), ({3,8,12},{1,4,6,10}), ({1,8,12},{2,4,6,10}), ({2,4,5,12},{0,7,10}), ({1,4,9,12},{2,7,10}), ({1,2,5,9},{3,7,10}), ({1,2,9,12},{4,7,10}), ({1,9,12},{2,4,7,10}), ({1,2,9},{3,4,7,10}), ({2,4,9,12},{5,7,10}), ({2,4,12},{0,5,7,10}), ({4,9,12},{2,5,7,10})]
def block17 : Array Config := #[({2,9,12},{4,5,7,10}), ({1,4,5,12},{6,7,10}), ({4,5,12},{0,6,7,10}), ({1,4,12},{2,6,7,10}), ({2,5,7,12},{0,8,10}), ({3,5,7,12},{1,8,10}), ({5,7,12},{0,1,8,10}), ({1,2,5,7},{3,8,10}), ({2,5,7},{0,3,8,10}), ({1,2,3,12},{4,8,10}), ({2,3,7,12},{5,8,10}), ({2,7,12},{0,5,8,10})]
def block18 : Array Config := #[({3,7,12},{1,5,8,10}), ({2,3,12},{4,5,8,10}), ({1,3,5,12},{6,8,10}), ({3,5,12},{1,6,8,10}), ({1,3,12},{4,6,8,10}), ({1,2,5,12},{7,8,10}), ({2,5,12},{0,7,8,10}), ({1,2,5},{3,7,8,10}), ({1,2,12},{4,7,8,10}), ({1,5,12},{6,7,8,10}), ({2,4,7,8},{0,9,10}), ({1,4,7,8},{2,9,10})]
def block19 : Array Config := #[({4,7,8},{0,2,9,10}), ({1,2,7,8},{3,9,10}), ({2,7,8},{0,3,9,10}), ({1,7,8},{2,3,9,10}), ({1,2,3,8},{4,9,10}), ({1,2,8},{3,4,9,10}), ({2,3,4,7},{5,9,10}), ({2,4,7},{0,5,9,10}), ({1,3,4,8},{6,9,10}), ({1,4,8},{2,6,9,10}), ({1,3,8},{4,6,9,10}), ({1,2,3,7},{8,9,10})]
def block20 : Array Config := #[({1,2,7},{3,8,9,10}), ({1,2,3},{4,8,9,10}), ({2,3,7},{5,8,9,10}), ({4,6,8,10},{0,2,11}), ({0,6,8,9},{1,2,11}), ({2,5,8,10},{0,3,11}), ({0,5,8,9},{1,3,11}), ({0,8,9,10},{2,3,11}), ({0,8,9},{1,2,3,11}), ({2,6,8,10},{0,4,11}), ({3,6,8,9},{1,4,11}), ({6,8,9,10},{2,4,11})]
def block21 : Array Config := #[({6,8,10},{0,2,4,11}), ({6,8,9},{1,2,4,11}), ({2,8,9,10},{3,4,11}), ({2,8,10},{0,3,4,11}), ({8,9,10},{2,3,4,11}), ({0,4,9,10},{2,5,11}), ({0,2,9,10},{3,5,11}), ({0,9,10},{2,3,5,11}), ({2,3,9,10},{4,5,11}), ({2,9,10},{3,4,5,11}), ({4,5,8,10},{0,6,11}), ({0,3,5,8},{1,6,11})]
def block22 : Array Config := #[({0,4,8,10},{2,6,11}), ({4,8,10},{0,2,6,11}), ({0,5,8,10},{3,6,11}), ({5,8,10},{0,3,6,11}), ({0,5,8},{1,3,6,11}), ({0,8,10},{2,3,6,11}), ({0,3,4,10},{5,6,11}), ({0,4,10},{2,5,6,11}), ({2,4,5,6},{0,7,11}), ({0,5,6,9},{1,7,11}), ({0,4,6,9},{2,7,11}), ({0,6,9},{1,2,7,11})]
def block23 : Array Config := #[({0,2,5,9},{3,7,11}), ({0,5,9},{1,3,7,11}), ({0,2,4,9},{5,7,11}), ({0,4,9},{2,5,7,11}), ({0,2,9},{3,5,7,11}), ({2,5,6,10},{0,8,11}), ({0,3,5,6},{1,8,11}), ({0,2,5,10},{3,8,11}), ({2,5,10},{0,3,8,11}), ({2,3,6,10},{4,8,11}), ({2,6,10},{0,4,8,11}), ({0,2,3,10},{5,8,11})]
def block24 : Array Config := #[({0,2,10},{3,5,8,11}), ({2,3,10},{4,5,8,11}), ({0,3,5,10},{6,8,11}), ({0,3,5},{1,6,8,11}), ({0,5,10},{3,6,8,11}), ({0,3,10},{5,6,8,11}), ({0,2,5,6},{7,8,11}), ({2,5,6},{0,7,8,11}), ({0,5,6},{1,7,8,11}), ({0,2,5},{3,7,8,11}), ({2,4,6,8},{0,9,11}), ({0,3,6,8},{1,9,11})]
def block25 : Array Config := #[({0,4,6,8},{2,9,11}), ({4,6,8},{0,2,9,11}), ({0,6,8},{1,2,9,11}), ({2,3,6,8},{4,9,11}), ({2,6,8},{0,4,9,11}), ({3,6,8},{1,4,9,11}), ({0,2,3,4},{5,9,11}), ({0,3,4,8},{6,9,11}), ({0,3,8},{1,6,9,11}), ({0,4,8},{2,6,9,11}), ({0,3,4},{5,6,9,11}), ({0,2,4,6},{7,9,11})]
def block26 : Array Config := #[({2,4,6},{0,7,9,11}), ({0,4,6},{2,7,9,11}), ({0,2,4},{5,7,9,11}), ({0,2,3,6},{8,9,11}), ({0,3,6},{1,8,9,11}), ({2,3,6},{4,8,9,11}), ({0,2,3},{5,8,9,11}), ({0,2,6},{7,8,9,11}), ({2,4,5,8},{0,10,11}), ({3,5,8,9},{1,10,11}), ({2,5,8,9},{3,10,11}), ({2,5,8},{0,3,10,11})]
def block27 : Array Config := #[({5,8,9},{1,3,10,11}), ({2,3,8,9},{4,10,11}), ({3,8,9},{1,4,10,11}), ({2,8,9},{3,4,10,11}), ({2,3,4,9},{5,10,11}), ({2,3,9},{4,5,10,11}), ({3,4,5,8},{6,10,11}), ({4,5,8},{0,6,10,11}), ({3,5,8},{1,6,10,11}), ({2,4,5,9},{7,10,11}), ({2,4,5},{0,7,10,11}), ({2,5,9},{3,7,10,11})]
def block28 : Array Config := #[({2,4,9},{5,7,10,11}), ({2,3,4,8},{9,10,11}), ({2,4,8},{0,9,10,11}), ({2,3,8},{4,9,10,11}), ({2,3,4},{5,9,10,11}), ({3,4,8},{6,9,10,11}), ({5,6,7,11},{0,1,12}), ({4,6,7,10},{0,2,12}), ({5,7,10,11},{0,3,12}), ({5,7,9,11},{1,3,12}), ({5,7,11},{0,1,3,12}), ({1,7,9,10},{2,3,12})]
def block29 : Array Config := #[({3,6,9,11},{1,4,12}), ({1,6,9,10},{2,4,12}), ({1,9,10,11},{3,4,12}), ({1,9,10},{2,3,4,12}), ({4,7,10,11},{0,5,12}), ({3,7,9,11},{1,5,12}), ({4,7,9,10},{2,5,12}), ({4,7,10},{0,2,5,12}), ({7,9,10,11},{3,5,12}), ({7,10,11},{0,3,5,12}), ({7,9,11},{1,3,5,12}), ({7,9,10},{2,3,5,12})]
def block30 : Array Config := #[({3,9,10,11},{4,5,12}), ({3,9,11},{1,4,5,12}), ({9,10,11},{3,4,5,12}), ({4,5,10,11},{0,6,12}), ({1,5,10,11},{3,6,12}), ({5,10,11},{0,3,6,12}), ({1,3,10,11},{4,6,12}), ({1,10,11},{3,4,6,12}), ({3,4,10,11},{5,6,12}), ({4,10,11},{0,5,6,12}), ({3,10,11},{4,5,6,12}), ({4,5,6,11},{0,7,12})]
def block31 : Array Config := #[({5,6,9,11},{1,7,12}), ({5,6,11},{0,1,7,12}), ({1,4,6,9},{2,7,12}), ({1,5,9,11},{3,7,12}), ({5,9,11},{1,3,7,12}), ({1,6,9,11},{4,7,12}), ({6,9,11},{1,4,7,12}), ({1,6,9},{2,4,7,12}), ({1,9,11},{3,4,7,12}), ({1,4,5,11},{6,7,12}), ({4,5,11},{0,6,7,12}), ({1,5,11},{3,6,7,12})]
def block32 : Array Config := #[({5,6,7,10},{0,8,12}), ({3,5,6,7},{1,8,12}), ({5,6,7},{0,1,8,12}), ({1,6,7,10},{2,8,12}), ({6,7,10},{0,2,8,12}), ({1,5,7,10},{3,8,12}), ({5,7,10},{0,3,8,12}), ({1,7,10},{2,3,8,12}), ({1,3,6,10},{4,8,12}), ({1,6,10},{2,4,8,12}), ({1,3,5,10},{6,8,12}), ({1,5,10},{3,6,8,12})]
def block33 : Array Config := #[({1,3,10},{4,6,8,12}), ({4,6,7,11},{0,9,12}), ({3,6,7,11},{1,9,12}), ({6,7,11},{0,1,9,12}), ({1,4,6,7},{2,9,12}), ({4,6,7},{0,2,9,12}), ({1,3,6,11},{4,9,12}), ({3,6,11},{1,4,9,12}), ({3,4,7,11},{5,9,12}), ({4,7,11},{0,5,9,12}), ({3,7,11},{1,5,9,12}), ({1,3,4,11},{6,9,12})]
def block34 : Array Config := #[({1,3,11},{4,6,9,12}), ({3,4,11},{5,6,9,12}), ({1,4,6,11},{7,9,12}), ({4,6,11},{0,7,9,12}), ({1,4,6},{2,7,9,12}), ({1,6,11},{4,7,9,12}), ({1,4,11},{6,7,9,12}), ({1,3,6,7},{8,9,12}), ({3,6,7},{1,8,9,12}), ({1,6,7},{2,8,9,12}), ({1,3,6},{4,8,9,12}), ({3,5,7,9},{1,10,12})]
def block35 : Array Config := #[({1,4,7,9},{2,10,12}), ({1,5,7,9},{3,10,12}), ({5,7,9},{1,3,10,12}), ({1,7,9},{2,3,10,12}), ({3,4,7,9},{5,10,12}), ({3,7,9},{1,5,10,12}), ({4,7,9},{2,5,10,12}), ({1,3,4,5},{6,10,12}), ({1,4,5,9},{7,10,12}), ({1,4,9},{2,7,10,12}), ({1,5,9},{3,7,10,12}), ({1,4,5},{6,7,10,12})]
def block36 : Array Config := #[({1,3,5,7},{8,10,12}), ({3,5,7},{1,8,10,12}), ({1,5,7},{3,8,10,12}), ({1,3,5},{6,8,10,12}), ({1,3,4,7},{9,10,12}), ({1,4,7},{2,9,10,12}), ({3,4,7},{5,9,10,12}), ({1,3,4},{6,9,10,12}), ({1,3,7},{8,9,10,12}), ({4,5,6,10},{0,11,12}), ({3,5,6,9},{1,11,12}), ({4,6,9,10},{2,11,12})]
def block37 : Array Config := #[({4,6,10},{0,2,11,12}), ({3,6,9,10},{4,11,12}), ({3,6,9},{1,4,11,12}), ({6,9,10},{2,4,11,12}), ({3,4,9,10},{5,11,12}), ({4,9,10},{2,5,11,12}), ({3,9,10},{4,5,11,12}), ({3,4,5,10},{6,11,12}), ({4,5,10},{0,6,11,12}), ({3,4,10},{5,6,11,12}), ({4,5,6,9},{7,11,12}), ({4,5,6},{0,7,11,12})]
def block38 : Array Config := #[({5,6,9},{1,7,11,12}), ({4,6,9},{2,7,11,12}), ({3,5,6,10},{8,11,12}), ({5,6,10},{0,8,11,12}), ({3,5,6},{1,8,11,12}), ({3,6,10},{4,8,11,12}), ({3,5,10},{6,8,11,12}), ({3,4,5,9},{10,11,12}), ({3,5,9},{1,10,11,12}), ({3,4,9},{5,10,11,12}), ({3,4,5},{6,10,11,12}), ({4,5,9},{7,10,11,12})]
def table : Array (Array Config) := #[block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31, block32, block33, block34, block35, block36, block37, block38]
def config (i : Fin 468) : Config := (table[i.val/12]!)[i.val%12]!
def sel0 : Array (Array Nat) := #[#[24, 62, 63, 74, 89, 90, 91, 101, 103, 107, 109, 110, 118, 131, 132, 134, 141, 142, 149, 150, 151, 154, 156, 157, 162, 163, 164], #[53, 83, 103, 127, 142, 146, 148, 156, 159, 161, 162, 164, 258, 276, 278, 280, 283, 287, 288, 294, 297, 306, 311, 314, 315, 318, 319], #[34, 79, 88, 94, 95, 126, 130, 138, 139, 153, 159, 160, 263, 270, 282, 287, 290, 291, 293, 299, 306, 307, 308, 310, 315, 316, 318], #[35, 51, 62, 65, 68, 131, 138, 141, 146, 149, 150, 152, 257, 264, 270, 271, 274, 278, 279, 300, 306, 307, 309, 310, 311, 313, 314], #[22, 42, 60, 63, 64, 88, 90, 99, 103, 107, 108, 110, 246, 263, 266, 268, 273, 276, 277, 282, 283, 290, 291, 292, 294, 296, 297], #[41, 71, 99, 101, 102, 113, 141, 153, 154, 155, 162, 163, 244, 273, 274, 275, 282, 294, 296, 299, 300, 302, 311, 313, 315, 316, 319], #[2, 10, 12, 13, 14, 71, 74, 79, 80, 82, 83, 85, 113, 116, 118, 119, 126, 127, 129, 153, 154, 155, 156, 157, 159, 160, 161], #[2, 22, 24, 113, 116, 118, 119, 130, 131, 132, 133, 134, 244, 246, 247, 248, 263, 264, 266, 268, 269, 299, 300, 302, 307, 308, 309], #[2, 10, 12, 13, 14, 41, 42, 50, 51, 52, 53, 54, 244, 246, 247, 248, 257, 258, 259, 273, 274, 275, 276, 277, 278, 279, 280], #[13, 24, 35, 74, 80, 83, 85, 89, 90, 91, 94, 96, 247, 257, 258, 259, 264, 266, 269, 270, 271, 283, 287, 288, 290, 292, 293], #[12, 22, 34, 42, 50, 53, 54, 60, 63, 64, 65, 67, 116, 126, 127, 129, 130, 132, 133, 138, 139, 142, 146, 148, 149, 151, 152], #[10, 34, 35, 41, 50, 51, 52, 60, 62, 65, 67, 68, 71, 79, 80, 82, 88, 89, 94, 95, 96, 99, 101, 102, 107, 108, 109], #[2, 10, 12, 14, 22, 34, 41, 42, 50, 52, 54, 60, 64, 67, 71, 79, 82, 88, 95, 99, 102, 108, 113, 116, 119, 126, 129, 130, 133, 139, 153, 155, 160, 244, 246, 248, 263, 268, 273, 275, 277, 282, 291, 296, 299, 302, 308, 316]]
def sel1 : Array (Array Nat) := #[#[2, 10, 13, 14, 24, 35, 41, 51, 52, 62, 68, 71, 74, 80, 82, 85, 89, 91, 96, 101, 102, 109, 113, 118, 119, 131, 134, 141, 150, 154, 155, 157, 163, 244, 247, 248, 257, 259, 264, 269, 271, 274, 275, 279, 300, 302, 309, 313], #[2, 12, 13, 14, 22, 24, 42, 53, 54, 63, 64, 74, 83, 85, 90, 91, 103, 110, 116, 118, 119, 127, 129, 132, 133, 134, 142, 148, 151, 156, 157, 161, 164, 246, 247, 248, 258, 259, 266, 268, 269, 276, 277, 280, 283, 288, 292, 297], #[10, 12, 13, 14, 34, 35, 50, 51, 52, 53, 54, 65, 67, 68, 79, 80, 82, 83, 85, 94, 95, 96, 126, 127, 129, 138, 139, 146, 148, 152, 159, 160, 161, 257, 258, 259, 270, 271, 278, 279, 280, 287, 288, 293, 306, 310, 314, 318], #[22, 24, 34, 35, 60, 62, 63, 64, 65, 67, 68, 88, 89, 90, 91, 94, 95, 96, 107, 108, 109, 110, 130, 131, 132, 133, 134, 138, 139, 149, 150, 151, 152, 263, 264, 266, 268, 269, 270, 271, 290, 291, 292, 293, 307, 308, 309, 310], #[41, 42, 50, 51, 52, 53, 54, 60, 62, 63, 64, 65, 67, 68, 99, 101, 102, 103, 107, 108, 109, 110, 141, 142, 146, 148, 149, 150, 151, 152, 162, 163, 164, 273, 274, 275, 276, 277, 278, 279, 280, 294, 296, 297, 311, 313, 314, 319], #[71, 74, 79, 80, 82, 83, 85, 88, 89, 90, 91, 94, 95, 96, 99, 101, 102, 103, 107, 108, 109, 110, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 282, 283, 287, 288, 290, 291, 292, 293, 294, 296, 297, 315, 316, 318, 319], #[113, 116, 118, 119, 126, 127, 129, 130, 131, 132, 133, 134, 138, 139, 141, 142, 146, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 299, 300, 302, 306, 307, 308, 309, 310, 311, 313, 314, 315, 316, 318, 319], #[244, 246, 247, 248, 257, 258, 259, 263, 264, 266, 268, 269, 270, 271, 273, 274, 275, 276, 277, 278, 279, 280, 282, 283, 287, 288, 290, 291, 292, 293, 294, 296, 297, 299, 300, 302, 306, 307, 308, 309, 310, 311, 313, 314, 315, 316, 318, 319], #[48, 103, 104, 123, 142, 143, 145, 156, 158, 162, 164, 165, 178, 197, 198, 200, 211, 213, 221, 223, 224, 229, 232, 233, 239, 240, 241], #[92, 135, 158, 192, 213, 218, 220, 232, 236, 238, 239, 241, 366, 392, 394, 396, 402, 407, 408, 415, 418, 427, 432, 435, 436, 439, 440], #[62, 131, 141, 149, 150, 190, 196, 205, 207, 227, 236, 237, 374, 381, 400, 407, 410, 412, 414, 420, 427, 428, 429, 431, 436, 437, 439], #[63, 90, 103, 107, 110, 197, 205, 211, 218, 221, 223, 225, 364, 375, 381, 383, 389, 394, 395, 421, 427, 428, 430, 431, 432, 434, 435], #[46, 76, 101, 104, 106, 141, 143, 154, 158, 162, 163, 165, 349, 374, 377, 379, 387, 392, 393, 400, 402, 410, 412, 413, 415, 417, 418]]
def sel2 : Array (Array Nat) := #[#[74, 118, 154, 156, 157, 173, 211, 227, 229, 231, 239, 240, 347, 387, 389, 391, 400, 415, 417, 420, 421, 423, 432, 434, 436, 437, 440], #[8, 24, 28, 30, 32, 118, 123, 131, 132, 134, 135, 137, 173, 176, 178, 179, 190, 192, 194, 227, 229, 231, 232, 233, 236, 237, 238], #[8, 46, 48, 173, 176, 178, 179, 196, 197, 198, 199, 200, 347, 349, 350, 351, 374, 375, 377, 379, 380, 420, 421, 423, 428, 429, 430], #[8, 24, 28, 30, 32, 74, 76, 89, 90, 91, 92, 93, 347, 349, 350, 351, 364, 366, 367, 387, 389, 391, 392, 393, 394, 395, 396], #[30, 48, 63, 123, 132, 135, 137, 142, 143, 145, 149, 151, 350, 364, 366, 367, 375, 377, 380, 381, 383, 402, 407, 408, 410, 413, 414], #[28, 46, 62, 76, 89, 92, 93, 101, 104, 106, 107, 109, 176, 190, 192, 194, 196, 198, 199, 205, 207, 213, 218, 220, 221, 224, 225], #[8, 24, 28, 32, 46, 62, 74, 76, 89, 91, 93, 101, 106, 109, 118, 131, 134, 141, 150, 154, 157, 163, 173, 176, 179, 190, 194, 196, 199, 207, 227, 231, 237, 347, 349, 351, 374, 379, 387, 391, 393, 400, 412, 417, 420, 423, 429, 437], #[8, 24, 30, 32, 48, 63, 74, 90, 91, 103, 110, 118, 123, 132, 134, 137, 142, 145, 151, 156, 157, 164, 173, 178, 179, 197, 200, 211, 223, 229, 231, 233, 240, 347, 350, 351, 364, 367, 375, 380, 383, 389, 391, 395, 421, 423, 430, 434], #[8, 28, 30, 32, 46, 48, 76, 92, 93, 104, 106, 123, 135, 137, 143, 145, 158, 165, 176, 178, 179, 192, 194, 198, 199, 200, 213, 220, 224, 232, 233, 238, 241, 349, 350, 351, 366, 367, 377, 379, 380, 392, 393, 396, 402, 408, 413, 418], #[24, 28, 30, 32, 62, 63, 89, 90, 91, 92, 93, 107, 109, 110, 131, 132, 134, 135, 137, 149, 150, 151, 190, 192, 194, 205, 207, 218, 220, 225, 236, 237, 238, 364, 366, 367, 381, 383, 394, 395, 396, 407, 408, 414, 427, 431, 435, 439], #[46, 48, 62, 63, 101, 103, 104, 106, 107, 109, 110, 141, 142, 143, 145, 149, 150, 151, 162, 163, 164, 165, 196, 197, 198, 199, 200, 205, 207, 221, 223, 224, 225, 374, 375, 377, 379, 380, 381, 383, 410, 412, 413, 414, 428, 429, 430, 431], #[74, 76, 89, 90, 91, 92, 93, 101, 103, 104, 106, 107, 109, 110, 154, 156, 157, 158, 162, 163, 164, 165, 211, 213, 218, 220, 221, 223, 224, 225, 239, 240, 241, 387, 389, 391, 392, 393, 394, 395, 396, 415, 417, 418, 432, 434, 435, 440], #[118, 123, 131, 132, 134, 135, 137, 141, 142, 143, 145, 149, 150, 151, 154, 156, 157, 158, 162, 163, 164, 165, 227, 229, 231, 232, 233, 236, 237, 238, 239, 240, 241, 400, 402, 407, 408, 410, 412, 413, 414, 415, 417, 418, 436, 437, 439, 440]]
def sel3 : Array (Array Nat) := #[#[173, 176, 178, 179, 190, 192, 194, 196, 197, 198, 199, 200, 205, 207, 211, 213, 218, 220, 221, 223, 224, 225, 227, 229, 231, 232, 233, 236, 237, 238, 239, 240, 241, 420, 421, 423, 427, 428, 429, 430, 431, 432, 434, 435, 436, 437, 439, 440], #[347, 349, 350, 351, 364, 366, 367, 374, 375, 377, 379, 380, 381, 383, 387, 389, 391, 392, 393, 394, 395, 396, 400, 402, 407, 408, 410, 412, 413, 414, 415, 417, 418, 420, 421, 423, 427, 428, 429, 430, 431, 432, 434, 435, 436, 437, 439, 440], #[86, 158, 159, 185, 213, 214, 217, 232, 234, 239, 241, 242, 260, 285, 287, 289, 303, 306, 315, 317, 318, 325, 328, 329, 337, 339, 340], #[49, 125, 140, 146, 147, 180, 195, 201, 202, 226, 234, 235, 272, 278, 298, 306, 311, 312, 314, 320, 328, 333, 334, 336, 337, 338, 340], #[73, 98, 103, 170, 195, 197, 208, 211, 212, 221, 222, 223, 245, 272, 276, 281, 283, 284, 294, 295, 297, 320, 322, 323, 333, 334, 335], #[43, 75, 98, 104, 105, 120, 140, 143, 144, 158, 162, 165, 249, 272, 281, 285, 286, 294, 295, 298, 303, 304, 311, 312, 315, 317, 319], #[11, 73, 78, 83, 84, 115, 125, 127, 128, 156, 159, 161, 170, 180, 208, 211, 212, 214, 215, 226, 229, 230, 234, 235, 239, 240, 242], #[7, 115, 120, 123, 124, 170, 178, 226, 229, 230, 232, 233, 245, 249, 254, 255, 298, 303, 304, 320, 322, 323, 325, 327, 337, 338, 339], #[17, 48, 53, 55, 58, 178, 185, 197, 198, 200, 201, 204, 254, 258, 260, 261, 276, 278, 280, 322, 325, 327, 328, 329, 333, 335, 336], #[7, 11, 15, 17, 18, 73, 75, 78, 83, 84, 86, 87, 245, 249, 254, 255, 258, 260, 261, 281, 283, 284, 285, 286, 287, 288, 289], #[7, 11, 15, 17, 18, 43, 48, 49, 53, 55, 56, 58, 115, 120, 123, 124, 125, 127, 128, 140, 142, 143, 144, 145, 146, 147, 148], #[15, 43, 49, 55, 56, 75, 78, 86, 87, 98, 104, 105, 180, 185, 195, 198, 201, 202, 204, 208, 213, 214, 215, 217, 221, 222, 224], #[7, 11, 15, 18, 43, 49, 56, 73, 75, 78, 84, 87, 98, 105, 115, 120, 124, 125, 128, 140, 144, 147, 170, 180, 195, 202, 208, 212, 215, 222, 226, 230, 235, 245, 249, 255, 272, 281, 284, 286, 295, 298, 304, 312, 320, 323, 334, 338]]
def sel4 : Array (Array Nat) := #[#[7, 11, 17, 18, 48, 53, 58, 73, 83, 84, 103, 115, 123, 124, 127, 128, 142, 145, 148, 156, 161, 164, 170, 178, 197, 200, 211, 212, 223, 229, 230, 233, 240, 245, 254, 255, 258, 261, 276, 280, 283, 284, 288, 297, 322, 323, 327, 335], #[7, 15, 17, 18, 43, 48, 55, 56, 58, 75, 86, 87, 104, 105, 120, 123, 124, 143, 144, 145, 158, 165, 178, 185, 198, 200, 204, 213, 217, 224, 232, 233, 241, 249, 254, 255, 260, 261, 285, 286, 289, 303, 304, 317, 325, 327, 329, 339], #[11, 15, 17, 18, 49, 53, 55, 56, 58, 78, 83, 84, 86, 87, 125, 127, 128, 146, 147, 148, 159, 161, 180, 185, 201, 202, 204, 214, 215, 217, 234, 235, 242, 258, 260, 261, 278, 280, 287, 288, 289, 306, 314, 318, 328, 329, 336, 340], #[43, 48, 49, 53, 55, 56, 58, 98, 103, 104, 105, 140, 142, 143, 144, 145, 146, 147, 148, 162, 164, 165, 195, 197, 198, 200, 201, 202, 204, 221, 222, 223, 224, 272, 276, 278, 280, 294, 295, 297, 311, 312, 314, 319, 333, 334, 335, 336], #[73, 75, 78, 83, 84, 86, 87, 98, 103, 104, 105, 156, 158, 159, 161, 162, 164, 165, 208, 211, 212, 213, 214, 215, 217, 221, 222, 223, 224, 239, 240, 241, 242, 281, 283, 284, 285, 286, 287, 288, 289, 294, 295, 297, 315, 317, 318, 319], #[115, 120, 123, 124, 125, 127, 128, 140, 142, 143, 144, 145, 146, 147, 148, 156, 158, 159, 161, 162, 164, 165, 226, 229, 230, 232, 233, 234, 235, 239, 240, 241, 242, 298, 303, 304, 306, 311, 312, 314, 315, 317, 318, 319, 337, 338, 339, 340], #[170, 178, 180, 185, 195, 197, 198, 200, 201, 202, 204, 208, 211, 212, 213, 214, 215, 217, 221, 222, 223, 224, 226, 229, 230, 232, 233, 234, 235, 239, 240, 241, 242, 320, 322, 323, 325, 327, 328, 329, 333, 334, 335, 336, 337, 338, 339, 340], #[245, 249, 254, 255, 258, 260, 261, 272, 276, 278, 280, 281, 283, 284, 285, 286, 287, 288, 289, 294, 295, 297, 298, 303, 304, 306, 311, 312, 314, 315, 317, 318, 319, 320, 322, 323, 325, 327, 328, 329, 333, 334, 335, 336, 337, 338, 339, 340], #[138, 234, 236, 270, 306, 307, 310, 328, 330, 337, 340, 341, 368, 404, 407, 409, 424, 427, 436, 438, 439, 448, 451, 453, 463, 465, 466], #[88, 188, 209, 218, 219, 263, 282, 290, 291, 321, 330, 332, 385, 394, 419, 427, 432, 433, 435, 442, 451, 458, 460, 462, 463, 464, 466], #[121, 153, 158, 250, 282, 285, 299, 303, 305, 315, 316, 317, 348, 385, 392, 398, 402, 403, 415, 416, 418, 442, 445, 446, 458, 460, 461], #[79, 126, 153, 159, 160, 181, 209, 214, 216, 234, 239, 242, 353, 385, 398, 404, 406, 415, 416, 419, 424, 425, 432, 433, 436, 438, 440], #[26, 121, 130, 135, 136, 175, 188, 192, 193, 232, 236, 238, 250, 263, 299, 303, 305, 307, 308, 321, 325, 326, 330, 332, 337, 339, 341]]
def sel5 : Array (Array Nat) := #[#[16, 175, 181, 185, 186, 250, 260, 321, 325, 326, 328, 329, 348, 353, 360, 361, 419, 424, 425, 442, 445, 446, 448, 450, 463, 464, 465], #[37, 86, 92, 94, 97, 260, 270, 285, 287, 289, 290, 293, 360, 366, 368, 370, 392, 394, 396, 445, 448, 450, 451, 453, 458, 461, 462], #[16, 26, 34, 37, 39, 121, 126, 130, 135, 136, 138, 139, 348, 353, 360, 361, 366, 368, 370, 398, 402, 403, 404, 406, 407, 408, 409], #[16, 26, 34, 37, 39, 79, 86, 88, 92, 94, 95, 97, 175, 181, 185, 186, 188, 192, 193, 209, 213, 214, 216, 217, 218, 219, 220], #[16, 26, 34, 39, 79, 88, 95, 121, 126, 130, 136, 139, 153, 160, 175, 181, 186, 188, 193, 209, 216, 219, 250, 263, 282, 291, 299, 305, 308, 316, 321, 326, 332, 348, 353, 361, 385, 398, 403, 406, 416, 419, 425, 433, 442, 446, 460, 464], #[16, 26, 37, 39, 86, 92, 97, 121, 135, 136, 158, 175, 185, 186, 192, 193, 213, 217, 220, 232, 238, 241, 250, 260, 285, 289, 303, 305, 317, 325, 326, 329, 339, 348, 360, 361, 366, 370, 392, 396, 402, 403, 408, 418, 445, 446, 450, 461], #[16, 34, 37, 39, 79, 86, 94, 95, 97, 126, 138, 139, 159, 160, 181, 185, 186, 214, 216, 217, 234, 242, 260, 270, 287, 289, 293, 306, 310, 318, 328, 329, 340, 353, 360, 361, 368, 370, 404, 406, 409, 424, 425, 438, 448, 450, 453, 465], #[26, 34, 37, 39, 88, 92, 94, 95, 97, 130, 135, 136, 138, 139, 188, 192, 193, 218, 219, 220, 236, 238, 263, 270, 290, 291, 293, 307, 308, 310, 330, 332, 341, 366, 368, 370, 394, 396, 407, 408, 409, 427, 435, 439, 451, 453, 462, 466], #[79, 86, 88, 92, 94, 95, 97, 153, 158, 159, 160, 209, 213, 214, 216, 217, 218, 219, 220, 239, 241, 242, 282, 285, 287, 289, 290, 291, 293, 315, 316, 317, 318, 385, 392, 394, 396, 415, 416, 418, 432, 433, 435, 440, 458, 460, 461, 462], #[121, 126, 130, 135, 136, 138, 139, 153, 158, 159, 160, 232, 234, 236, 238, 239, 241, 242, 299, 303, 305, 306, 307, 308, 310, 315, 316, 317, 318, 337, 339, 340, 341, 398, 402, 403, 404, 406, 407, 408, 409, 415, 416, 418, 436, 438, 439, 440], #[175, 181, 185, 186, 188, 192, 193, 209, 213, 214, 216, 217, 218, 219, 220, 232, 234, 236, 238, 239, 241, 242, 321, 325, 326, 328, 329, 330, 332, 337, 339, 340, 341, 419, 424, 425, 427, 432, 433, 435, 436, 438, 439, 440, 463, 464, 465, 466], #[250, 260, 263, 270, 282, 285, 287, 289, 290, 291, 293, 299, 303, 305, 306, 307, 308, 310, 315, 316, 317, 318, 321, 325, 326, 328, 329, 330, 332, 337, 339, 340, 341, 442, 445, 446, 448, 450, 451, 453, 458, 460, 461, 462, 463, 464, 465, 466], #[348, 353, 360, 361, 366, 368, 370, 385, 392, 394, 396, 398, 402, 403, 404, 406, 407, 408, 409, 415, 416, 418, 419, 424, 425, 427, 432, 433, 435, 436, 438, 439, 440, 442, 445, 446, 448, 450, 451, 453, 458, 460, 461, 462, 463, 464, 465, 466]]
def sel6 : Array (Array Nat) := #[#[59, 187, 195, 205, 206, 262, 272, 320, 330, 331, 333, 334, 363, 371, 381, 382, 427, 428, 431, 441, 451, 452, 454, 455, 463, 466, 467], #[112, 140, 141, 243, 272, 274, 298, 300, 301, 311, 312, 313, 343, 371, 374, 397, 400, 401, 410, 411, 412, 441, 443, 444, 454, 455, 457], #[9, 112, 125, 167, 180, 182, 183, 226, 227, 228, 234, 235, 343, 352, 354, 355, 397, 400, 401, 404, 405, 420, 424, 426, 436, 437, 438], #[20, 112, 131, 167, 187, 190, 191, 226, 227, 228, 236, 237, 243, 262, 264, 265, 298, 300, 301, 307, 309, 320, 330, 331, 337, 338, 341], #[51, 182, 196, 201, 203, 257, 274, 278, 279, 328, 333, 336, 354, 374, 420, 424, 426, 428, 429, 443, 448, 449, 454, 457, 463, 465, 467], #[9, 20, 33, 35, 36, 243, 257, 262, 264, 265, 270, 271, 343, 352, 354, 355, 363, 368, 369, 441, 443, 444, 448, 449, 451, 452, 453], #[33, 49, 59, 65, 66, 125, 138, 140, 146, 147, 149, 152, 352, 363, 368, 369, 371, 381, 382, 397, 404, 405, 407, 409, 410, 411, 414], #[9, 20, 33, 35, 36, 49, 51, 59, 62, 65, 66, 68, 167, 180, 182, 183, 187, 190, 191, 195, 196, 201, 202, 203, 205, 206, 207], #[9, 20, 33, 36, 49, 59, 66, 112, 125, 140, 147, 167, 180, 183, 187, 191, 195, 202, 206, 226, 228, 235, 243, 262, 265, 272, 298, 301, 312, 320, 331, 334, 338, 343, 352, 355, 363, 369, 371, 382, 397, 401, 405, 411, 441, 444, 452, 455], #[9, 20, 35, 36, 51, 62, 68, 112, 131, 141, 150, 167, 182, 183, 190, 191, 196, 203, 207, 227, 228, 237, 243, 257, 264, 265, 271, 274, 279, 300, 301, 309, 313, 343, 354, 355, 374, 400, 401, 412, 420, 426, 429, 437, 443, 444, 449, 457], #[9, 33, 35, 36, 49, 51, 65, 66, 68, 125, 138, 146, 147, 152, 180, 182, 183, 201, 202, 203, 234, 235, 257, 270, 271, 278, 279, 306, 310, 314, 328, 336, 340, 352, 354, 355, 368, 369, 404, 405, 409, 424, 426, 438, 448, 449, 453, 465], #[20, 33, 35, 36, 59, 62, 65, 66, 68, 131, 138, 149, 150, 152, 187, 190, 191, 205, 206, 207, 236, 237, 262, 264, 265, 270, 271, 307, 309, 310, 330, 331, 341, 363, 368, 369, 381, 382, 407, 409, 414, 427, 431, 439, 451, 452, 453, 466], #[49, 51, 59, 62, 65, 66, 68, 140, 141, 146, 147, 149, 150, 152, 195, 196, 201, 202, 203, 205, 206, 207, 272, 274, 278, 279, 311, 312, 313, 314, 333, 334, 336, 371, 374, 381, 382, 410, 411, 412, 414, 428, 429, 431, 454, 455, 457, 467]]
def sel7 : Array (Array Nat) := #[#[112, 125, 131, 138, 140, 141, 146, 147, 149, 150, 152, 226, 227, 228, 234, 235, 236, 237, 298, 300, 301, 306, 307, 309, 310, 311, 312, 313, 314, 337, 338, 340, 341, 397, 400, 401, 404, 405, 407, 409, 410, 411, 412, 414, 436, 437, 438, 439], #[167, 180, 182, 183, 187, 190, 191, 195, 196, 201, 202, 203, 205, 206, 207, 226, 227, 228, 234, 235, 236, 237, 320, 328, 330, 331, 333, 334, 336, 337, 338, 340, 341, 420, 424, 426, 427, 428, 429, 431, 436, 437, 438, 439, 463, 465, 466, 467], #[243, 257, 262, 264, 265, 270, 271, 272, 274, 278, 279, 298, 300, 301, 306, 307, 309, 310, 311, 312, 313, 314, 320, 328, 330, 331, 333, 334, 336, 337, 338, 340, 341, 441, 443, 444, 448, 449, 451, 452, 453, 454, 455, 457, 463, 465, 466, 467], #[343, 352, 354, 355, 363, 368, 369, 371, 374, 381, 382, 397, 400, 401, 404, 405, 407, 409, 410, 411, 412, 414, 420, 424, 426, 427, 428, 429, 431, 436, 437, 438, 439, 441, 443, 444, 448, 449, 451, 452, 453, 454, 455, 457, 463, 465, 466, 467], #[40, 69, 98, 99, 100, 272, 273, 281, 282, 294, 295, 296, 342, 371, 372, 373, 384, 385, 386, 441, 442, 454, 455, 456, 458, 459, 460], #[1, 69, 73, 166, 170, 171, 172, 208, 209, 210, 211, 212, 342, 344, 345, 346, 384, 385, 386, 389, 390, 419, 421, 422, 432, 433, 434], #[1, 19, 21, 22, 23, 166, 170, 171, 172, 187, 188, 189, 245, 246, 262, 263, 266, 267, 268, 320, 321, 322, 323, 324, 330, 331, 332], #[42, 171, 197, 246, 273, 276, 277, 321, 322, 324, 333, 335, 345, 372, 375, 376, 419, 421, 422, 428, 430, 442, 454, 456, 463, 464, 467], #[21, 73, 90, 245, 262, 266, 267, 281, 283, 284, 290, 292, 344, 363, 364, 365, 384, 389, 390, 394, 395, 441, 451, 452, 458, 459, 462], #[1, 19, 21, 22, 23, 40, 42, 59, 60, 61, 63, 64, 342, 344, 345, 346, 363, 364, 365, 371, 372, 373, 375, 376, 381, 382, 383], #[19, 40, 59, 60, 61, 69, 88, 98, 99, 100, 107, 108, 166, 187, 188, 189, 195, 205, 206, 208, 209, 210, 218, 219, 221, 222, 225], #[1, 19, 21, 23, 40, 59, 61, 69, 73, 98, 100, 166, 170, 172, 187, 189, 195, 206, 208, 210, 212, 222, 245, 262, 267, 272, 281, 284, 295, 320, 323, 331, 334, 342, 344, 346, 363, 365, 371, 373, 382, 384, 386, 390, 441, 452, 455, 459], #[1, 19, 22, 23, 40, 42, 60, 61, 64, 69, 88, 99, 100, 108, 166, 171, 172, 188, 189, 209, 210, 219, 246, 263, 268, 273, 277, 282, 291, 296, 321, 324, 332, 342, 345, 346, 372, 373, 376, 385, 386, 419, 422, 433, 442, 456, 460, 464]]
def sel8 : Array (Array Nat) := #[#[1, 21, 22, 23, 42, 63, 64, 73, 90, 103, 110, 170, 171, 172, 197, 211, 212, 223, 245, 246, 266, 267, 268, 276, 277, 283, 284, 292, 297, 322, 323, 324, 335, 344, 345, 346, 364, 365, 375, 376, 383, 389, 390, 395, 421, 422, 430, 434], #[19, 21, 22, 23, 59, 60, 61, 63, 64, 88, 90, 107, 108, 110, 187, 188, 189, 205, 206, 218, 219, 225, 262, 263, 266, 267, 268, 290, 291, 292, 330, 331, 332, 363, 364, 365, 381, 382, 383, 394, 395, 427, 431, 435, 451, 452, 462, 466], #[40, 42, 59, 60, 61, 63, 64, 98, 99, 100, 103, 107, 108, 110, 195, 197, 205, 206, 221, 222, 223, 225, 272, 273, 276, 277, 294, 295, 296, 297, 333, 334, 335, 371, 372, 373, 375, 376, 381, 382, 383, 428, 430, 431, 454, 455, 456, 467], #[69, 73, 88, 90, 98, 99, 100, 103, 107, 108, 110, 208, 209, 210, 211, 212, 218, 219, 221, 222, 223, 225, 281, 282, 283, 284, 290, 291, 292, 294, 295, 296, 297, 384, 385, 386, 389, 390, 394, 395, 432, 433, 434, 435, 458, 459, 460, 462], #[166, 170, 171, 172, 187, 188, 189, 195, 197, 205, 206, 208, 209, 210, 211, 212, 218, 219, 221, 222, 223, 225, 320, 321, 322, 323, 324, 330, 331, 332, 333, 334, 335, 419, 421, 422, 427, 428, 430, 431, 432, 433, 434, 435, 463, 464, 466, 467], #[245, 246, 262, 263, 266, 267, 268, 272, 273, 276, 277, 281, 282, 283, 284, 290, 291, 292, 294, 295, 296, 297, 320, 321, 322, 323, 324, 330, 331, 332, 333, 334, 335, 441, 442, 451, 452, 454, 455, 456, 458, 459, 460, 462, 463, 464, 466, 467], #[342, 344, 345, 346, 363, 364, 365, 371, 372, 373, 375, 376, 381, 382, 383, 384, 385, 386, 389, 390, 394, 395, 419, 421, 422, 427, 428, 430, 431, 432, 433, 434, 435, 441, 442, 451, 452, 454, 455, 456, 458, 459, 460, 462, 463, 464, 466, 467], #[0, 69, 70, 71, 72, 111, 112, 113, 114, 153, 154, 155, 342, 343, 384, 385, 386, 387, 388, 397, 398, 399, 400, 401, 415, 416, 417], #[0, 3, 4, 5, 6, 111, 112, 113, 114, 120, 121, 122, 243, 244, 249, 250, 251, 252, 253, 298, 299, 300, 301, 302, 303, 304, 305], #[5, 41, 44, 46, 47, 244, 250, 251, 253, 273, 274, 275, 348, 349, 372, 374, 377, 378, 379, 442, 443, 445, 446, 447, 454, 456, 457], #[4, 70, 75, 76, 77, 243, 249, 251, 252, 281, 285, 286, 343, 349, 384, 387, 388, 392, 393, 441, 443, 444, 445, 447, 458, 459, 461], #[3, 40, 43, 44, 45, 111, 120, 121, 122, 140, 143, 144, 342, 348, 371, 372, 373, 377, 378, 397, 398, 399, 402, 403, 410, 411, 413], #[0, 3, 4, 5, 6, 40, 41, 43, 44, 45, 46, 47, 69, 70, 71, 72, 75, 76, 77, 98, 99, 100, 101, 102, 104, 105, 106]]
def sel9 : Array (Array Nat) := #[#[0, 3, 4, 6, 40, 43, 45, 69, 70, 72, 75, 77, 98, 100, 105, 111, 112, 114, 120, 122, 140, 144, 243, 249, 252, 272, 281, 286, 295, 298, 301, 304, 312, 342, 343, 371, 373, 384, 386, 388, 397, 399, 401, 411, 441, 444, 455, 459], #[0, 3, 5, 6, 40, 41, 44, 45, 47, 69, 71, 72, 99, 100, 102, 111, 113, 114, 121, 122, 153, 155, 244, 250, 253, 273, 275, 282, 296, 299, 302, 305, 316, 342, 348, 372, 373, 378, 385, 386, 398, 399, 403, 416, 442, 446, 456, 460], #[0, 4, 5, 6, 41, 46, 47, 70, 71, 72, 76, 77, 101, 102, 106, 112, 113, 114, 141, 154, 155, 163, 243, 244, 251, 252, 253, 274, 275, 300, 301, 302, 313, 343, 349, 374, 379, 387, 388, 393, 400, 401, 412, 417, 443, 444, 447, 457], #[3, 4, 5, 6, 43, 44, 45, 46, 47, 75, 76, 77, 104, 105, 106, 120, 121, 122, 143, 144, 158, 165, 249, 250, 251, 252, 253, 285, 286, 303, 304, 305, 317, 348, 349, 377, 378, 379, 392, 393, 402, 403, 413, 418, 445, 446, 447, 461], #[40, 41, 43, 44, 45, 46, 47, 98, 99, 100, 101, 102, 104, 105, 106, 140, 141, 143, 144, 162, 163, 165, 272, 273, 274, 275, 294, 295, 296, 311, 312, 313, 319, 371, 372, 373, 374, 377, 378, 379, 410, 411, 412, 413, 454, 455, 456, 457], #[69, 70, 71, 72, 75, 76, 77, 98, 99, 100, 101, 102, 104, 105, 106, 153, 154, 155, 158, 162, 163, 165, 281, 282, 285, 286, 294, 295, 296, 315, 316, 317, 319, 384, 385, 386, 387, 388, 392, 393, 415, 416, 417, 418, 458, 459, 460, 461], #[111, 112, 113, 114, 120, 121, 122, 140, 141, 143, 144, 153, 154, 155, 158, 162, 163, 165, 298, 299, 300, 301, 302, 303, 304, 305, 311, 312, 313, 315, 316, 317, 319, 397, 398, 399, 400, 401, 402, 403, 410, 411, 412, 413, 415, 416, 417, 418], #[243, 244, 249, 250, 251, 252, 253, 272, 273, 274, 275, 281, 282, 285, 286, 294, 295, 296, 298, 299, 300, 301, 302, 303, 304, 305, 311, 312, 313, 315, 316, 317, 319, 441, 442, 443, 444, 445, 446, 447, 454, 455, 456, 457, 458, 459, 460, 461], #[342, 343, 348, 349, 371, 372, 373, 374, 377, 378, 379, 384, 385, 386, 387, 388, 392, 393, 397, 398, 399, 400, 401, 402, 403, 410, 411, 412, 413, 415, 416, 417, 418, 441, 442, 443, 444, 445, 446, 447, 454, 455, 456, 457, 458, 459, 460, 461], #[0, 1, 2, 111, 112, 113, 114, 115, 116, 117, 118, 119, 166, 167, 168, 169, 170, 171, 172, 173, 174, 226, 227, 228, 229, 230, 231], #[2, 10, 12, 13, 14, 168, 171, 173, 174, 181, 182, 184, 345, 347, 353, 354, 356, 358, 359, 419, 420, 421, 422, 423, 424, 425, 426], #[9, 11, 13, 70, 73, 74, 78, 80, 81, 83, 84, 85, 343, 344, 347, 352, 354, 355, 356, 357, 359, 384, 387, 388, 389, 390, 391], #[1, 11, 12, 111, 115, 116, 117, 125, 126, 127, 128, 129, 342, 344, 345, 346, 352, 353, 356, 357, 358, 397, 398, 399, 404, 405, 406]]
def sel10 : Array (Array Nat) := #[#[0, 9, 10, 69, 70, 71, 72, 78, 79, 80, 81, 82, 166, 167, 168, 169, 180, 181, 182, 183, 184, 208, 209, 210, 214, 215, 216], #[0, 1, 9, 11, 69, 70, 72, 73, 78, 81, 84, 111, 112, 114, 115, 117, 125, 128, 166, 167, 169, 170, 172, 180, 183, 208, 210, 212, 215, 226, 228, 230, 235, 342, 343, 344, 346, 352, 355, 357, 384, 386, 388, 390, 397, 399, 401, 405], #[0, 1, 2, 10, 12, 14, 69, 71, 72, 79, 82, 111, 113, 114, 116, 117, 119, 126, 129, 153, 155, 160, 166, 168, 169, 171, 172, 174, 181, 184, 209, 210, 216, 342, 345, 346, 353, 358, 385, 386, 398, 399, 406, 416, 419, 422, 425, 433], #[0, 2, 9, 10, 13, 14, 70, 71, 72, 74, 80, 81, 82, 85, 112, 113, 114, 118, 119, 154, 155, 157, 167, 168, 169, 173, 174, 182, 183, 184, 227, 228, 231, 343, 347, 354, 355, 359, 387, 388, 391, 400, 401, 417, 420, 423, 426, 437], #[1, 2, 11, 12, 13, 14, 73, 74, 83, 84, 85, 115, 116, 117, 118, 119, 127, 128, 129, 156, 157, 161, 170, 171, 172, 173, 174, 211, 212, 229, 230, 231, 240, 344, 345, 346, 347, 356, 357, 358, 359, 389, 390, 391, 421, 422, 423, 434], #[9, 10, 11, 12, 13, 14, 78, 79, 80, 81, 82, 83, 84, 85, 125, 126, 127, 128, 129, 159, 160, 161, 180, 181, 182, 183, 184, 214, 215, 216, 234, 235, 242, 352, 353, 354, 355, 356, 357, 358, 359, 404, 405, 406, 424, 425, 426, 438], #[69, 70, 71, 72, 73, 74, 78, 79, 80, 81, 82, 83, 84, 85, 153, 154, 155, 156, 157, 159, 160, 161, 208, 209, 210, 211, 212, 214, 215, 216, 239, 240, 242, 384, 385, 386, 387, 388, 389, 390, 391, 415, 416, 417, 432, 433, 434, 440], #[111, 112, 113, 114, 115, 116, 117, 118, 119, 125, 126, 127, 128, 129, 153, 154, 155, 156, 157, 159, 160, 161, 226, 227, 228, 229, 230, 231, 234, 235, 239, 240, 242, 397, 398, 399, 400, 401, 404, 405, 406, 415, 416, 417, 436, 437, 438, 440], #[166, 167, 168, 169, 170, 171, 172, 173, 174, 180, 181, 182, 183, 184, 208, 209, 210, 211, 212, 214, 215, 216, 226, 227, 228, 229, 230, 231, 234, 235, 239, 240, 242, 419, 420, 421, 422, 423, 424, 425, 426, 432, 433, 434, 436, 437, 438, 440], #[342, 343, 344, 345, 346, 347, 352, 353, 354, 355, 356, 357, 358, 359, 384, 385, 386, 387, 388, 389, 390, 391, 397, 398, 399, 400, 401, 404, 405, 406, 415, 416, 417, 419, 420, 421, 422, 423, 424, 425, 426, 432, 433, 434, 436, 437, 438, 440], #[2, 5, 8, 168, 171, 173, 174, 175, 176, 177, 178, 179, 244, 246, 247, 248, 250, 251, 253, 254, 256, 321, 322, 324, 325, 326, 327], #[4, 7, 8, 20, 21, 24, 25, 28, 29, 30, 31, 32, 243, 245, 247, 249, 251, 252, 254, 255, 256, 262, 264, 265, 266, 267, 269], #[1, 3, 7, 19, 21, 22, 23, 25, 26, 27, 30, 31, 111, 115, 116, 117, 120, 121, 122, 123, 124, 130, 132, 133, 135, 136, 137]]
def sel11 : Array (Array Nat) := #[#[0, 3, 4, 5, 6, 19, 20, 25, 26, 27, 28, 29, 166, 167, 168, 169, 175, 176, 177, 187, 188, 189, 190, 191, 192, 193, 194], #[0, 1, 3, 4, 6, 7, 19, 20, 21, 23, 25, 27, 29, 31, 111, 112, 114, 115, 117, 120, 122, 124, 166, 167, 169, 170, 172, 187, 189, 191, 226, 228, 230, 243, 245, 249, 252, 255, 262, 265, 267, 298, 301, 304, 320, 323, 331, 338], #[0, 1, 2, 3, 5, 6, 19, 22, 23, 26, 27, 111, 113, 114, 116, 117, 119, 121, 122, 130, 133, 136, 166, 168, 169, 171, 172, 174, 175, 177, 188, 189, 193, 244, 246, 248, 250, 253, 263, 268, 299, 302, 305, 308, 321, 324, 326, 332], #[0, 2, 4, 5, 6, 8, 20, 24, 28, 29, 32, 112, 113, 114, 118, 119, 131, 134, 167, 168, 169, 173, 174, 176, 177, 179, 190, 191, 194, 227, 228, 231, 237, 243, 244, 247, 248, 251, 252, 253, 256, 264, 265, 269, 300, 301, 302, 309], #[1, 2, 7, 8, 21, 22, 23, 24, 30, 31, 32, 115, 116, 117, 118, 119, 123, 124, 132, 133, 134, 137, 170, 171, 172, 173, 174, 178, 179, 229, 230, 231, 233, 245, 246, 247, 248, 254, 255, 256, 266, 267, 268, 269, 322, 323, 324, 327], #[3, 4, 5, 6, 7, 8, 25, 26, 27, 28, 29, 30, 31, 32, 120, 121, 122, 123, 124, 135, 136, 137, 175, 176, 177, 178, 179, 192, 193, 194, 232, 233, 238, 249, 250, 251, 252, 253, 254, 255, 256, 303, 304, 305, 325, 326, 327, 339], #[19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 130, 131, 132, 133, 134, 135, 136, 137, 187, 188, 189, 190, 191, 192, 193, 194, 236, 237, 238, 262, 263, 264, 265, 266, 267, 268, 269, 307, 308, 309, 330, 331, 332, 341], #[111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 130, 131, 132, 133, 134, 135, 136, 137, 226, 227, 228, 229, 230, 231, 232, 233, 236, 237, 238, 298, 299, 300, 301, 302, 303, 304, 305, 307, 308, 309, 337, 338, 339, 341], #[166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 187, 188, 189, 190, 191, 192, 193, 194, 226, 227, 228, 229, 230, 231, 232, 233, 236, 237, 238, 320, 321, 322, 323, 324, 325, 326, 327, 330, 331, 332, 337, 338, 339, 341], #[243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 262, 263, 264, 265, 266, 267, 268, 269, 298, 299, 300, 301, 302, 303, 304, 305, 307, 308, 309, 320, 321, 322, 323, 324, 325, 326, 327, 330, 331, 332, 337, 338, 339, 341], #[8, 13, 17, 247, 251, 254, 256, 257, 258, 259, 260, 261, 347, 349, 350, 351, 354, 356, 359, 360, 362, 443, 445, 447, 448, 449, 450], #[12, 16, 17, 42, 44, 48, 50, 53, 54, 55, 57, 58, 345, 348, 350, 353, 356, 358, 360, 361, 362, 372, 375, 376, 377, 378, 380], #[5, 10, 16, 41, 44, 46, 47, 50, 51, 52, 55, 57, 168, 175, 176, 177, 181, 182, 184, 185, 186, 196, 198, 199, 201, 203, 204]]
def sel12 : Array (Array Nat) := #[#[2, 5, 10, 12, 14, 16, 41, 42, 44, 47, 50, 52, 54, 57, 168, 171, 174, 175, 177, 181, 184, 186, 244, 246, 248, 250, 253, 273, 275, 277, 321, 324, 326, 345, 348, 353, 358, 361, 372, 376, 378, 419, 422, 425, 442, 446, 456, 464], #[2, 5, 8, 10, 13, 14, 41, 46, 47, 51, 52, 168, 173, 174, 176, 177, 179, 182, 184, 196, 199, 203, 244, 247, 248, 251, 253, 256, 257, 259, 274, 275, 279, 347, 349, 351, 354, 359, 374, 379, 420, 423, 426, 429, 443, 447, 449, 457], #[2, 8, 12, 13, 14, 17, 42, 48, 53, 54, 58, 171, 173, 174, 178, 179, 197, 200, 246, 247, 248, 254, 256, 258, 259, 261, 276, 277, 280, 322, 324, 327, 335, 345, 347, 350, 351, 356, 358, 359, 362, 375, 376, 380, 421, 422, 423, 430], #[5, 8, 16, 17, 44, 46, 47, 48, 55, 57, 58, 175, 176, 177, 178, 179, 185, 186, 198, 199, 200, 204, 250, 251, 253, 254, 256, 260, 261, 325, 326, 327, 329, 348, 349, 350, 351, 360, 361, 362, 377, 378, 379, 380, 445, 446, 447, 450], #[10, 12, 13, 14, 16, 17, 50, 51, 52, 53, 54, 55, 57, 58, 181, 182, 184, 185, 186, 201, 203, 204, 257, 258, 259, 260, 261, 278, 279, 280, 328, 329, 336, 353, 354, 356, 358, 359, 360, 361, 362, 424, 425, 426, 448, 449, 450, 465], #[41, 42, 44, 46, 47, 48, 50, 51, 52, 53, 54, 55, 57, 58, 196, 197, 198, 199, 200, 201, 203, 204, 273, 274, 275, 276, 277, 278, 279, 280, 333, 335, 336, 372, 374, 375, 376, 377, 378, 379, 380, 428, 429, 430, 454, 456, 457, 467], #[168, 171, 173, 174, 175, 176, 177, 178, 179, 181, 182, 184, 185, 186, 196, 197, 198, 199, 200, 201, 203, 204, 321, 322, 324, 325, 326, 327, 328, 329, 333, 335, 336, 419, 420, 421, 422, 423, 424, 425, 426, 428, 429, 430, 463, 464, 465, 467], #[244, 246, 247, 248, 250, 251, 253, 254, 256, 257, 258, 259, 260, 261, 273, 274, 275, 276, 277, 278, 279, 280, 321, 322, 324, 325, 326, 327, 328, 329, 333, 335, 336, 442, 443, 445, 446, 447, 448, 449, 450, 454, 456, 457, 463, 464, 465, 467], #[345, 347, 348, 349, 350, 351, 353, 354, 356, 358, 359, 360, 361, 362, 372, 374, 375, 376, 377, 378, 379, 380, 419, 420, 421, 422, 423, 424, 425, 426, 428, 429, 430, 442, 443, 445, 446, 447, 448, 449, 450, 454, 456, 457, 463, 464, 465, 467], #[7, 11, 15, 17, 18, 21, 25, 30, 31, 33, 37, 38, 344, 350, 352, 356, 357, 360, 362, 363, 364, 365, 366, 367, 368, 369, 370], #[4, 9, 15, 20, 25, 28, 29, 33, 35, 36, 37, 38, 70, 75, 76, 77, 78, 80, 81, 86, 87, 89, 92, 93, 94, 96, 97], #[4, 7, 9, 11, 15, 18, 20, 21, 25, 29, 31, 33, 36, 38, 70, 73, 75, 77, 78, 81, 84, 87, 243, 245, 249, 252, 255, 262, 265, 267, 281, 284, 286, 343, 344, 352, 355, 357, 363, 365, 369, 384, 388, 390, 441, 444, 452, 459], #[4, 8, 9, 13, 20, 24, 28, 29, 32, 35, 36, 70, 74, 76, 77, 80, 81, 85, 89, 91, 93, 96, 243, 247, 251, 252, 256, 257, 259, 264, 265, 269, 271, 343, 347, 349, 351, 354, 355, 359, 387, 388, 391, 393, 443, 444, 447, 449]]
def sel13 : Array (Array Nat) := #[#[7, 8, 11, 13, 17, 18, 21, 24, 30, 31, 32, 73, 74, 83, 84, 85, 90, 91, 245, 247, 254, 255, 256, 258, 259, 261, 266, 267, 269, 283, 284, 288, 292, 344, 347, 350, 351, 356, 357, 359, 362, 364, 365, 367, 389, 390, 391, 395], #[4, 7, 8, 15, 17, 18, 25, 28, 29, 30, 31, 32, 37, 38, 75, 76, 77, 86, 87, 92, 93, 97, 249, 251, 252, 254, 255, 256, 260, 261, 285, 286, 289, 349, 350, 351, 360, 362, 366, 367, 370, 392, 393, 396, 445, 447, 450, 461], #[9, 11, 13, 15, 17, 18, 33, 35, 36, 37, 38, 78, 80, 81, 83, 84, 85, 86, 87, 94, 96, 97, 257, 258, 259, 260, 261, 270, 271, 287, 288, 289, 293, 352, 354, 355, 356, 357, 359, 360, 362, 368, 369, 370, 448, 449, 450, 453], #[20, 21, 24, 25, 28, 29, 30, 31, 32, 33, 35, 36, 37, 38, 89, 90, 91, 92, 93, 94, 96, 97, 262, 264, 265, 266, 267, 269, 270, 271, 290, 292, 293, 363, 364, 365, 366, 367, 368, 369, 370, 394, 395, 396, 451, 452, 453, 462], #[70, 73, 74, 75, 76, 77, 78, 80, 81, 83, 84, 85, 86, 87, 89, 90, 91, 92, 93, 94, 96, 97, 281, 283, 284, 285, 286, 287, 288, 289, 290, 292, 293, 384, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 458, 459, 461, 462], #[243, 245, 247, 249, 251, 252, 254, 255, 256, 257, 258, 259, 260, 261, 262, 264, 265, 266, 267, 269, 270, 271, 281, 283, 284, 285, 286, 287, 288, 289, 290, 292, 293, 441, 443, 444, 445, 447, 448, 449, 450, 451, 452, 453, 458, 459, 461, 462], #[343, 344, 347, 349, 350, 351, 352, 354, 355, 356, 357, 359, 360, 362, 363, 364, 365, 366, 367, 368, 369, 370, 384, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 441, 443, 444, 445, 447, 448, 449, 450, 451, 452, 453, 458, 459, 461, 462], #[3, 15, 16, 19, 25, 26, 27, 33, 34, 37, 38, 39, 40, 43, 44, 45, 49, 50, 55, 56, 57, 59, 60, 61, 65, 66, 67], #[1, 3, 7, 11, 15, 18, 19, 21, 23, 25, 27, 31, 33, 38, 40, 43, 45, 49, 56, 59, 61, 66, 111, 115, 117, 120, 122, 124, 125, 128, 140, 144, 147, 342, 344, 346, 352, 357, 363, 365, 369, 371, 373, 382, 397, 399, 405, 411], #[1, 3, 12, 16, 19, 22, 23, 26, 27, 34, 39, 40, 42, 44, 45, 50, 54, 57, 60, 61, 64, 67, 111, 116, 117, 121, 122, 126, 129, 130, 133, 136, 139, 342, 345, 346, 348, 353, 358, 361, 372, 373, 376, 378, 398, 399, 403, 406], #[1, 7, 11, 12, 17, 18, 21, 22, 23, 30, 31, 42, 48, 53, 54, 58, 63, 64, 115, 116, 117, 123, 124, 127, 128, 129, 132, 133, 137, 142, 145, 148, 151, 344, 345, 346, 350, 356, 357, 358, 362, 364, 365, 367, 375, 376, 380, 383], #[3, 7, 15, 16, 17, 18, 25, 26, 27, 30, 31, 37, 38, 39, 43, 44, 45, 48, 55, 56, 57, 58, 120, 121, 122, 123, 124, 135, 136, 137, 143, 144, 145, 348, 350, 360, 361, 362, 366, 367, 370, 377, 378, 380, 402, 403, 408, 413], #[11, 12, 15, 16, 17, 18, 33, 34, 37, 38, 39, 49, 50, 53, 54, 55, 56, 57, 58, 65, 66, 67, 125, 126, 127, 128, 129, 138, 139, 146, 147, 148, 152, 352, 353, 356, 357, 358, 360, 361, 362, 368, 369, 370, 404, 405, 406, 409]]
def sel14 : Array (Array Nat) := #[#[19, 21, 22, 23, 25, 26, 27, 30, 31, 33, 34, 37, 38, 39, 59, 60, 61, 63, 64, 65, 66, 67, 130, 132, 133, 135, 136, 137, 138, 139, 149, 151, 152, 363, 364, 365, 366, 367, 368, 369, 370, 381, 382, 383, 407, 408, 409, 414], #[40, 42, 43, 44, 45, 48, 49, 50, 53, 54, 55, 56, 57, 58, 59, 60, 61, 63, 64, 65, 66, 67, 140, 142, 143, 144, 145, 146, 147, 148, 149, 151, 152, 371, 372, 373, 375, 376, 377, 378, 380, 381, 382, 383, 410, 411, 413, 414], #[111, 115, 116, 117, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 132, 133, 135, 136, 137, 138, 139, 140, 142, 143, 144, 145, 146, 147, 148, 149, 151, 152, 397, 398, 399, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 413, 414], #[342, 344, 345, 346, 348, 350, 352, 353, 356, 357, 358, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 375, 376, 377, 378, 380, 381, 382, 383, 397, 398, 399, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 413, 414], #[0, 3, 4, 6, 9, 15, 19, 20, 25, 27, 29, 33, 36, 38, 40, 43, 45, 49, 56, 59, 61, 66, 69, 70, 72, 75, 77, 78, 81, 87, 98, 100, 105, 166, 167, 169, 180, 183, 187, 189, 191, 195, 202, 206, 208, 210, 215, 222], #[0, 3, 5, 6, 10, 16, 19, 26, 27, 34, 39, 40, 41, 44, 45, 47, 50, 52, 57, 60, 61, 67, 69, 71, 72, 79, 82, 88, 95, 99, 100, 102, 108, 166, 168, 169, 175, 177, 181, 184, 186, 188, 189, 193, 209, 210, 216, 219], #[0, 4, 5, 6, 9, 10, 20, 28, 29, 35, 36, 41, 46, 47, 51, 52, 62, 68, 70, 71, 72, 76, 77, 80, 81, 82, 89, 93, 96, 101, 102, 106, 109, 167, 168, 169, 176, 177, 182, 183, 184, 190, 191, 194, 196, 199, 203, 207], #[3, 4, 5, 6, 15, 16, 25, 26, 27, 28, 29, 37, 38, 39, 43, 44, 45, 46, 47, 55, 56, 57, 75, 76, 77, 86, 87, 92, 93, 97, 104, 105, 106, 175, 176, 177, 185, 186, 192, 193, 194, 198, 199, 204, 213, 217, 220, 224], #[9, 10, 15, 16, 33, 34, 35, 36, 37, 38, 39, 49, 50, 51, 52, 55, 56, 57, 65, 66, 67, 68, 78, 79, 80, 81, 82, 86, 87, 94, 95, 96, 97, 180, 181, 182, 183, 184, 185, 186, 201, 202, 203, 204, 214, 215, 216, 217], #[19, 20, 25, 26, 27, 28, 29, 33, 34, 35, 36, 37, 38, 39, 59, 60, 61, 62, 65, 66, 67, 68, 88, 89, 92, 93, 94, 95, 96, 97, 107, 108, 109, 187, 188, 189, 190, 191, 192, 193, 194, 205, 206, 207, 218, 219, 220, 225], #[40, 41, 43, 44, 45, 46, 47, 49, 50, 51, 52, 55, 56, 57, 59, 60, 61, 62, 65, 66, 67, 68, 98, 99, 100, 101, 102, 104, 105, 106, 107, 108, 109, 195, 196, 198, 199, 201, 202, 203, 204, 205, 206, 207, 221, 222, 224, 225], #[69, 70, 71, 72, 75, 76, 77, 78, 79, 80, 81, 82, 86, 87, 88, 89, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 104, 105, 106, 107, 108, 109, 208, 209, 210, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 224, 225], #[166, 167, 168, 169, 175, 176, 177, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 198, 199, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 224, 225]]
def sel15 : Array (Array Nat) := #[#[0, 1, 3, 6, 19, 23, 27, 40, 45, 61, 69, 72, 100, 111, 114, 117, 122, 166, 169, 172, 189, 210, 342, 346, 373, 386, 399], #[0, 4, 6, 9, 20, 29, 36, 70, 72, 77, 81, 112, 114, 167, 169, 183, 191, 228, 243, 252, 265, 301, 343, 355, 388, 401, 444], #[1, 7, 11, 18, 21, 23, 31, 73, 84, 115, 117, 124, 128, 170, 172, 212, 230, 245, 255, 267, 284, 323, 344, 346, 357, 365, 390], #[3, 4, 6, 7, 15, 18, 25, 27, 29, 31, 38, 43, 45, 56, 75, 77, 87, 105, 120, 122, 124, 144, 249, 252, 255, 286, 304], #[9, 11, 15, 18, 33, 36, 38, 49, 56, 66, 78, 81, 84, 87, 125, 128, 147, 180, 183, 202, 215, 235, 352, 355, 357, 369, 405], #[19, 20, 21, 23, 25, 27, 29, 31, 33, 36, 38, 59, 61, 66, 187, 189, 191, 206, 262, 265, 267, 331, 363, 365, 369, 382, 452], #[40, 43, 45, 49, 56, 59, 61, 66, 98, 100, 105, 140, 144, 147, 195, 202, 206, 222, 272, 295, 312, 334, 371, 373, 382, 411, 455], #[69, 70, 72, 73, 75, 77, 78, 81, 84, 87, 98, 100, 105, 208, 210, 212, 215, 222, 281, 284, 286, 295, 384, 386, 388, 390, 459], #[111, 112, 114, 115, 117, 120, 122, 124, 125, 128, 140, 144, 147, 226, 228, 230, 235, 298, 301, 304, 312, 338, 397, 399, 401, 405, 411], #[166, 167, 169, 170, 172, 180, 183, 187, 189, 191, 195, 202, 206, 208, 210, 212, 215, 222, 226, 228, 230, 235, 320, 323, 331, 334, 338], #[243, 245, 249, 252, 255, 262, 265, 267, 272, 281, 284, 286, 295, 298, 301, 304, 312, 320, 323, 331, 334, 338, 441, 444, 452, 455, 459], #[342, 343, 344, 346, 352, 355, 357, 363, 365, 369, 371, 373, 382, 384, 386, 388, 390, 397, 399, 401, 405, 411, 441, 444, 452, 455, 459], #[0, 2, 5, 6, 10, 14, 41, 47, 52, 71, 72, 82, 102, 113, 114, 119, 155, 168, 169, 174, 177, 184, 244, 248, 253, 275, 302]]
def sel16 : Array (Array Nat) := #[#[1, 2, 12, 14, 22, 23, 42, 54, 64, 116, 117, 119, 129, 133, 171, 172, 174, 246, 248, 268, 277, 324, 345, 346, 358, 376, 422], #[3, 5, 6, 16, 26, 27, 39, 44, 45, 47, 57, 121, 122, 136, 175, 177, 186, 193, 250, 253, 305, 326, 348, 361, 378, 403, 446], #[10, 12, 14, 16, 34, 39, 50, 52, 54, 57, 67, 79, 82, 95, 126, 129, 139, 160, 181, 184, 186, 216, 353, 358, 361, 406, 425], #[19, 22, 23, 26, 27, 34, 39, 60, 61, 64, 67, 88, 95, 108, 130, 133, 136, 139, 188, 189, 193, 219, 263, 268, 291, 308, 332], #[40, 41, 42, 44, 45, 47, 50, 52, 54, 57, 60, 61, 64, 67, 99, 100, 102, 108, 273, 275, 277, 296, 372, 373, 376, 378, 456], #[69, 71, 72, 79, 82, 88, 95, 99, 100, 102, 108, 153, 155, 160, 209, 210, 216, 219, 282, 291, 296, 316, 385, 386, 416, 433, 460], #[111, 113, 114, 116, 117, 119, 121, 122, 126, 129, 130, 133, 136, 139, 153, 155, 160, 299, 302, 305, 308, 316, 398, 399, 403, 406, 416], #[166, 168, 169, 171, 172, 174, 175, 177, 181, 184, 186, 188, 189, 193, 209, 210, 216, 219, 321, 324, 326, 332, 419, 422, 425, 433, 464], #[244, 246, 248, 250, 253, 263, 268, 273, 275, 277, 282, 291, 296, 299, 302, 305, 308, 316, 321, 324, 326, 332, 442, 446, 456, 460, 464], #[342, 345, 346, 348, 353, 358, 361, 372, 373, 376, 378, 385, 386, 398, 399, 403, 406, 416, 419, 422, 425, 433, 442, 446, 456, 460, 464], #[2, 8, 13, 14, 24, 32, 74, 85, 91, 118, 119, 134, 157, 173, 174, 179, 231, 247, 248, 256, 259, 269, 347, 351, 359, 391, 423], #[4, 5, 6, 8, 28, 29, 32, 46, 47, 76, 77, 93, 106, 176, 177, 179, 194, 199, 251, 252, 253, 256, 349, 351, 379, 393, 447], #[9, 10, 13, 14, 35, 36, 51, 52, 68, 80, 81, 82, 85, 96, 182, 183, 184, 203, 257, 259, 271, 279, 354, 355, 359, 426, 449]]
def sel17 : Array (Array Nat) := #[#[20, 24, 28, 29, 32, 35, 36, 62, 68, 89, 91, 93, 96, 109, 131, 134, 150, 190, 191, 194, 207, 237, 264, 265, 269, 271, 309], #[41, 46, 47, 51, 52, 62, 68, 101, 102, 106, 109, 141, 150, 163, 196, 199, 203, 207, 274, 275, 279, 313, 374, 379, 412, 429, 457], #[70, 71, 72, 74, 76, 77, 80, 81, 82, 85, 89, 91, 93, 96, 101, 102, 106, 109, 154, 155, 157, 163, 387, 388, 391, 393, 417], #[112, 113, 114, 118, 119, 131, 134, 141, 150, 154, 155, 157, 163, 227, 228, 231, 237, 300, 301, 302, 309, 313, 400, 401, 412, 417, 437], #[167, 168, 169, 173, 174, 176, 177, 179, 182, 183, 184, 190, 191, 194, 196, 199, 203, 207, 227, 228, 231, 237, 420, 423, 426, 429, 437], #[243, 244, 247, 248, 251, 252, 253, 256, 257, 259, 264, 265, 269, 271, 274, 275, 279, 300, 301, 302, 309, 313, 443, 444, 447, 449, 457], #[343, 347, 349, 351, 354, 355, 359, 374, 379, 387, 388, 391, 393, 400, 401, 412, 417, 420, 423, 426, 429, 437, 443, 444, 447, 449, 457], #[7, 8, 17, 18, 30, 31, 32, 48, 58, 123, 124, 137, 145, 178, 179, 200, 233, 254, 255, 256, 261, 327, 350, 351, 362, 367, 380], #[11, 12, 13, 14, 17, 18, 53, 54, 58, 83, 84, 85, 127, 128, 129, 148, 161, 258, 259, 261, 280, 288, 356, 357, 358, 359, 362], #[21, 22, 23, 24, 30, 31, 32, 63, 64, 90, 91, 110, 132, 133, 134, 137, 151, 266, 267, 268, 269, 292, 364, 365, 367, 383, 395], #[42, 48, 53, 54, 58, 63, 64, 103, 110, 142, 145, 148, 151, 164, 197, 200, 223, 276, 277, 280, 297, 335, 375, 376, 380, 383, 430], #[73, 74, 83, 84, 85, 90, 91, 103, 110, 156, 157, 161, 164, 211, 212, 223, 240, 283, 284, 288, 292, 297, 389, 390, 391, 395, 434], #[115, 116, 117, 118, 119, 123, 124, 127, 128, 129, 132, 133, 134, 137, 142, 145, 148, 151, 156, 157, 161, 164, 229, 230, 231, 233, 240]]
def sel18 : Array (Array Nat) := #[#[170, 171, 172, 173, 174, 178, 179, 197, 200, 211, 212, 223, 229, 230, 231, 233, 240, 322, 323, 324, 327, 335, 421, 422, 423, 430, 434], #[245, 246, 247, 248, 254, 255, 256, 258, 259, 261, 266, 267, 268, 269, 276, 277, 280, 283, 284, 288, 292, 297, 322, 323, 324, 327, 335], #[344, 345, 346, 347, 350, 351, 356, 357, 358, 359, 362, 364, 365, 367, 375, 376, 380, 383, 389, 390, 391, 395, 421, 422, 423, 430, 434], #[15, 16, 17, 18, 37, 38, 39, 55, 56, 57, 58, 86, 87, 97, 185, 186, 204, 217, 260, 261, 289, 329, 360, 361, 362, 370, 450], #[25, 26, 27, 28, 29, 30, 31, 32, 37, 38, 39, 92, 93, 97, 135, 136, 137, 192, 193, 194, 220, 238, 366, 367, 370, 396, 408], #[43, 44, 45, 46, 47, 48, 55, 56, 57, 58, 104, 105, 106, 143, 144, 145, 165, 198, 199, 200, 204, 224, 377, 378, 379, 380, 413], #[75, 76, 77, 86, 87, 92, 93, 97, 104, 105, 106, 158, 165, 213, 217, 220, 224, 241, 285, 286, 289, 317, 392, 393, 396, 418, 461], #[120, 121, 122, 123, 124, 135, 136, 137, 143, 144, 145, 158, 165, 232, 233, 238, 241, 303, 304, 305, 317, 339, 402, 403, 408, 413, 418], #[175, 176, 177, 178, 179, 185, 186, 192, 193, 194, 198, 199, 200, 204, 213, 217, 220, 224, 232, 233, 238, 241, 325, 326, 327, 329, 339], #[249, 250, 251, 252, 253, 254, 255, 256, 260, 261, 285, 286, 289, 303, 304, 305, 317, 325, 326, 327, 329, 339, 445, 446, 447, 450, 461], #[348, 349, 350, 351, 360, 361, 362, 366, 367, 370, 377, 378, 379, 380, 392, 393, 396, 402, 403, 408, 413, 418, 445, 446, 447, 450, 461], #[33, 34, 35, 36, 37, 38, 39, 65, 66, 67, 68, 94, 95, 96, 97, 138, 139, 152, 270, 271, 293, 310, 368, 369, 370, 409, 453], #[49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 65, 66, 67, 68, 146, 147, 148, 152, 201, 202, 203, 204, 278, 279, 280, 314, 336]]
def sel19 : Array (Array Nat) := #[#[78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 94, 95, 96, 97, 159, 160, 161, 214, 215, 216, 217, 242, 287, 288, 289, 293, 318], #[125, 126, 127, 128, 129, 138, 139, 146, 147, 148, 152, 159, 160, 161, 234, 235, 242, 306, 310, 314, 318, 340, 404, 405, 406, 409, 438], #[180, 181, 182, 183, 184, 185, 186, 201, 202, 203, 204, 214, 215, 216, 217, 234, 235, 242, 328, 329, 336, 340, 424, 425, 426, 438, 465], #[257, 258, 259, 260, 261, 270, 271, 278, 279, 280, 287, 288, 289, 293, 306, 310, 314, 318, 328, 329, 336, 340, 448, 449, 450, 453, 465], #[352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 368, 369, 370, 404, 405, 406, 409, 424, 425, 426, 438, 448, 449, 450, 453, 465], #[59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 107, 108, 109, 110, 149, 150, 151, 152, 205, 206, 207, 225, 381, 382, 383, 414, 431], #[88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 107, 108, 109, 110, 218, 219, 220, 225, 290, 291, 292, 293, 394, 395, 396, 435, 462], #[130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 149, 150, 151, 152, 236, 237, 238, 307, 308, 309, 310, 341, 407, 408, 409, 414, 439], #[187, 188, 189, 190, 191, 192, 193, 194, 205, 206, 207, 218, 219, 220, 225, 236, 237, 238, 330, 331, 332, 341, 427, 431, 435, 439, 466], #[262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 290, 291, 292, 293, 307, 308, 309, 310, 330, 331, 332, 341, 451, 452, 453, 462, 466], #[363, 364, 365, 366, 367, 368, 369, 370, 381, 382, 383, 394, 395, 396, 407, 408, 409, 414, 427, 431, 435, 439, 451, 452, 453, 462, 466], #[98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 162, 163, 164, 165, 221, 222, 223, 224, 225, 294, 295, 296, 297, 319], #[140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 162, 163, 164, 165, 311, 312, 313, 314, 319, 410, 411, 412, 413, 414]]
def sel20 : Array (Array Nat) := #[#[195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 221, 222, 223, 224, 225, 333, 334, 335, 336, 428, 429, 430, 431, 467], #[272, 273, 274, 275, 276, 277, 278, 279, 280, 294, 295, 296, 297, 311, 312, 313, 314, 319, 333, 334, 335, 336, 454, 455, 456, 457, 467], #[371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 410, 411, 412, 413, 414, 428, 429, 430, 431, 454, 455, 456, 457, 467], #[153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 239, 240, 241, 242, 315, 316, 317, 318, 319, 415, 416, 417, 418, 440], #[208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 239, 240, 241, 242, 432, 433, 434, 435, 440], #[281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 315, 316, 317, 318, 319, 458, 459, 460, 461, 462], #[384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 415, 416, 417, 418, 432, 433, 434, 435, 440, 458, 459, 460, 461, 462], #[226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 337, 338, 339, 340, 341, 436, 437, 438, 439, 440], #[298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 337, 338, 339, 340, 341], #[397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417, 418, 436, 437, 438, 439, 440], #[320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 463, 464, 465, 466, 467], #[419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 463, 464, 465, 466, 467], #[441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467]]
def sels : Array (Array (Array Nat)) := #[sel0, sel1, sel2, sel3, sel4, sel5, sel6, sel7, sel8, sel9, sel10, sel11, sel12, sel13, sel14, sel15, sel16, sel17, sel18, sel19, sel20]
def idx (j : Fin 273) (k : ℕ) : ℕ := ((sels[j.val/13]!)[j.val%13]!)[k]!
def select (j : Fin 273) (k : Fin (fan j)) : Fin 468 := Fin.ofNat 468 (idx j k.val)

end PlanePairClean

namespace PlanePairClean
open PlanePairRows
theorem maximal_table : ∀ i : Fin 468, maximalConfig (config i) := by
  unfold maximalConfig
  decide +kernel

theorem keys_sorted : ∀ i : Fin 467, key (config i.castSucc) < key (config i.succ) := by decide +kernel
theorem config_injective : Function.Injective config := by
  have h : StrictMono (fun i => key (config i)) := Fin.strictMono_iff_lt_succ.mpr keys_sorted
  exact fun _ _ eq => h.injective (congrArg key eq)

theorem sorted_check : ∀ (j : Fin 273) (a : Fin 48), a.val+1 < fan j →
    (idx j a.val)%468 < (idx j (a.val+1))%468 := by decide +kernel
theorem next_injective {m : Nat} (f : Fin m → Fin 468)
    (h : ∀ a b, b.val=a.val+1 → f a<f b) : Function.Injective f := by
  cases m with
  | zero => intro a; exact Fin.elim0 a
  | succ m => exact (Fin.strictMono_iff_lt_succ.mpr (fun a => h a.castSucc a.succ rfl)).injective
theorem selector_injective (j : Fin 273) : Function.Injective (select j) := by
  apply next_injective
  intro a b hab
  have bound : fan j ≤ 48 := by unfold fan; split <;> decide
  have ha : a.val<48 := by omega
  have next := sorted_check j ⟨a.val,ha⟩ (by change a.val+1<fan j; omega)
  change idx j a.val % 468 < idx j b.val % 468
  rw [hab]
  exact next

theorem extends_pair : ∀ (j : Fin 273) (k : Fin (fan j)), ptSet j ⊆ (config (select j k)).1 ∧
    lnSet j ⊆ (config (select j k)).2 := by decide +kernel
end PlanePairClean

namespace PlanePairClean
open PlanePairRows PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem persistent_mixed_gate (C : Circuit) (hm : Monotone2 C) (small : C.size ≤ 63)
    (p : Positives C) (n : Negatives C) :
    ∃ pre g post, C.gates = pre ++ g :: post ∧ g.op=.and ∧ g.inputs.length=2 ∧
      (∃ e f : E, e≠f ∧ probe pre g (edgeInput (point e) (line e))=true ∧
        probe pre g (edgeInput (point f) (line f))=true) ∧
      ∃ j : Fin 273, 27 ≤ fan j ∧ ∃ family : Fin (fan j) → Config, Function.Injective family ∧
        ∀ k, maximalConfig (family k) ∧ ptSet j ⊆ (family k).1 ∧ lnSet j ⊆ (family k).2 ∧
          probe pre g (setInput (family k).1 (family k).2)=true ∧
          circuitFun 26 C (setInput (family k).1 (family k).2)=false := by
  obtain ⟨pre,g,post,heq,op,ins,pos,j,hit⟩ := physical_obstruction C hm small p n
  refine ⟨pre,g,post,heq,op,ins,pos,j,by unfold fan; split <;> decide,
    fun k => config (select j k),config_injective.comp (selector_injective j),?_⟩
  intro k
  have maxed := maximal_table (select j k)
  obtain ⟨hp,hl⟩ := extends_pair j k
  exact ⟨maxed,hp,hl,hit _ _ hp hl,n _ _ maxed.1 maxed.2.1 maxed.2.2.1⟩

end PlanePairClean
