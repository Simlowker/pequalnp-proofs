import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_7398
import PEqualNP.Outside.L_meta_3049

/-!
# Partial bounds for the 24-vertex graph in L-meta-9796

On an input specifying a subset of vertices, the output is true when that subset
contains both endpoints of at least one of the 44 listed edges.

* A concrete two-input monotone circuit of 55 gates computes the function.
* Every two-input monotone circuit requires at least 35 gates. Applying the
  published vertex-cover bound from L-meta-3049 uses a perfect matching of
  size twelve and the explicit adjacency certificates below.
* Every two-input AND/OR/NOT circuit computing it has at least 29 gates.
  The proof replays 132 cofactor or support bounds using the published
  restriction lemmas from L-meta-7398.
* Every monotone formula requires at least 53 leaves. A signed rectangle
  certificate on 44 positive and 454 negative inputs has total weight 52,888.
  The weight of each single-variable rectangle is at most 1,002.
  Unrolling a shared circuit counts repeated uses of a gate separately.
* For the class defined by GraphClean9796.permit, the minimum is exactly 55.
  Every correct monotone circuit using at most 54 gates must therefore use
  a strict binary AND accepting two distinct edges and at least one nonedge
  pair. A path of actual input wires must lead from such a gate to another
  binary AND that accepts some edge and rejects all 232 nonedge pairs.
  The nonedge accepted along the path may vary from one wire to the next.

The 55-gate lower bound for all monotone circuits remains open here.
The clean-gate counting argument adapts the earlier Heawood certificate by
Simlowker (HeawoodCircuitBound.lean, commit f3d2ec3a81c75492c0a63acfef41afb95c31f3a2)
and the later PlaneMixedGate.lean certificate (commit 2dc247ce52d662a940ce7d8154f6aa6e6cbb6ccd).
All finite checks in this file are replayed by Lean's kernel.
-/

set_option exponentiation.threshold 512

namespace GraphRows9796
abbrev Word := BitVec 276
abbrev V := Fin 24
abbrev E := Fin 44
def words : List Word := [18446726481523507207, 9671388110190551874142264, 1267640928840119263721387197376, 166152231832185699334049935392775168, 5444351718503212244045011095621581529088, 89197536442407792363728173470555611919679488, 730661621129507519413917690327791997438635540480, 2992424691648894219510146543963148055501081732448256, 6126989739039548150697342267604203262137722093600505856, 12548076483227109718740202810064349737368434229742634270720, 6415204109536585627688614338609858914777138135794249138962432, 1639089371619583650188425880863015517580520320112456062900109312, 3368354281721612686147769304123204058498835168558649500507517747265, 3447504838421998802846949183915459006059099026020505095468518379364488, 1763399564889381871103501514484037066819444732045902434692027594009871616, 450549459138255895981170566672293976197857408980452926864381677969856284672, 57445505532379145491616610862570832811557255279442935300063326843332953669634, 3647906671348652050567267854033834737748064014312574789336420974456001475903504, 114924560288782707747342197380958973955022716420325153686059507253874914976858624, 1782389453071500963732318792223332548040320121493731755514256155930510124998725632, 13406180154600980008083634263138230180622594263201251531305355607821723582408491008, 47680873799908034021004464131820562677129963274422277735654784163000739318413131776, 80184646879302559673805130697812045181948427266559877632600583590438957017339002884, 99660890876551085881380290683474649721894880380474325955661207616637674176001343520]
def varWord (v : V) : Word := words.getD v.val 0
def goal : Word := 17592186044415
def rneg (r : Fin 232) := 44 + r.val
def adjMasks : List (BitVec 24) := [4263936, 8527872, 290816, 573440, 1155072, 2310144, 4620288, 9240576, 1708032, 3407872, 6823936, 13647872, 261, 1046, 2092, 88, 177, 354, 708, 1416, 2832, 1568, 3137, 2178]
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

end GraphRows9796

namespace GraphUnion9796
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
end GraphUnion9796

namespace GraphClean9796
open GraphRows9796
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

def negPart (v : V) : BitVec 232 := (varWord v).extractLsb' 44 232

theorem negPart_bit (v : V) (k : Fin 232) : (negPart v).getLsbD k.val = onRow (rneg k) v := by
  simp only [negPart,onRow,rneg,BitVec.getLsbD_extractLsb',k.isLt,decide_true,Bool.true_and]

set_option maxHeartbeats 4000000 in
theorem adjacent_certificate : ∀ u v : V,
    adjacent u v = true ↔ negPart u &&& negPart v = 0 := by decide +kernel

theorem adj_iff_neg (u v : V) :
    adjacent u v=true ↔ ∀ k : Fin 232, ¬ (onRow (rneg k) u=true ∧ onRow (rneg k) v=true) := by
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

def matched : Fin 12 → E := ![0, 3, 8, 11, 15, 19, 23, 27, 32, 35, 39, 43]
set_option maxHeartbeats 4000000 in
theorem disjoint_matching : ∀ i j : Fin 12, ∀ v : V,
    onRow (matched i).val v=true → onRow (matched j).val v=true → i=j := by decide +kernel
theorem matching_cover (X : R) (h : ∀ e : E, Hits X e.val) : 12≤X.card := by
  classical
  have representatives (i : Fin 12) : ∃ v : X, onRow (matched i).val v.val=true := by
    obtain ⟨v,hv,hon⟩ := h (matched i)
    exact ⟨⟨v,hv⟩,hon⟩
  choose f hf using representatives
  have inj : Function.Injective f := by
    intro i j eq
    exact disjoint_matching i j (f i).val (hf i) (eq.symm ▸ hf j)
  simpa using Fintype.card_le_of_injective _ inj

theorem raw_alive : ∀ v : V, ∃ r : Fin 232, onRow (rneg r) v=true := by decide +kernel
theorem target_pos : ∀ e : E, goal.getLsbD e.val=true := by decide +kernel
theorem target_neg : ∀ r : Fin 232, goal.getLsbD (rneg r)=false := by decide +kernel
end GraphClean9796

namespace GraphClean9796
open GraphRows9796 GraphUnion9796
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
end GraphClean9796

namespace GraphClean9796
open GraphRows9796 GraphUnion9796

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

def clean (w : Word) : Prop := ∀ k : Fin 232, w.getLsbD (rneg k)=false

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
end GraphClean9796


namespace GraphClean9796
open GraphRows9796 GraphUnion9796
theorem output_lower {s r l t} (B : Budget s r l t) (h : Ready s goal) : 55 ≤ r+l+t := by
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


end GraphClean9796

namespace GraphClean9796
open GraphRows9796 GraphUnion9796 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ones : Word := BitVec.allOnes 276
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
    (hit : (C.gates.foldl tick words).getD C.output 0 = goal) : 55 ≤ C.size := by
  obtain ⟨s,r,l,t,B,sz,ready⟩ := word_program C.gates words startBudget
    (fun g hg => by simpa using hm g hg) (by
      intro x hx
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hx
      have len : words.length=24 := rfl
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
  change 55 ≤ C.gates.length
  omega
end GraphClean9796

namespace GraphClean9796
open GraphRows9796 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def bitAt (k : Nat) (a : Word) := a.getLsbD k
theorem map_lookup (k i : Nat) (w : List Word) :
    (w.map (bitAt k)).getD i false = bitAt k (w.getD i 0) := by
  by_cases h : i<w.length <;> simp [List.getD_eq_getElem?_getD,h,bitAt]

theorem read_and (k : Fin 276) (xs : List Word) :
    bitAt k.val (xs.foldr (· &&& ·) ones) = (xs.map (bitAt k.val)).all id := by
  induction xs with
  | nil => exact (BitVec.getLsbD_allOnes.trans (decide_eq_true k.isLt))
  | cons a xs ih => simp [bitAt] at ih ⊢; rw [ih]

theorem read_or (k : Fin 276) (xs : List Word) :
    bitAt k.val (xs.foldr (· ||| ·) 0) = (xs.map (bitAt k.val)).any id := by
  induction xs with
  | nil => simp [bitAt]
  | cons a xs ih => simp [bitAt] at ih ⊢; rw [ih]

theorem eval_step (k : Fin 276) (g : Gate) (w : List Word) (h : g.op = .and ∨ g.op = .or) :
    bitAt k.val (gateWord g w) = g.op.eval (g.inputs.map fun i => (w.map (bitAt k.val)).getD i false) := by
  rcases h with h|h
  · simp only [gateWord,h,read_and,GateOp.eval,List.map_map,Function.comp_def,map_lookup]
  · simp only [gateWord,h,read_or,GateOp.eval,List.map_map,Function.comp_def,map_lookup]

theorem rows_run (k : Fin 276) (gs : List Gate) (w : List Word)
    (hm : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    (gs.foldl tick w).map (bitAt k.val) =
      gs.foldl (fun xs g => xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]) (w.map (bitAt k.val)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (tick w g) (fun g' hg' => hm g' (List.mem_cons_of_mem _ hg'))]
    rw [tick,List.map_append,List.map_singleton,eval_step k g w (hm g List.mem_cons_self)]

theorem word_output (C : Circuit) (hm : Monotone2 C) (k : Fin 276) :
    bitAt k.val ((C.gates.foldl tick words).getD C.output 0) = C.eval (words.map (bitAt k.val)) := by
  rw [← map_lookup,rows_run k C.gates words (fun g hg => by simpa using (hm g hg).1)]
  rfl

def edges : List (Nat × Nat) := [(0, 12), (0, 16), (0, 22), (1, 13), (1, 17), (1, 23), (2, 12), (2, 13), (2, 14), (2, 18), (3, 14), (3, 15), (3, 19), (4, 13), (4, 15), (4, 16), (4, 20), (5, 14), (5, 16), (5, 17), (5, 21), (6, 15), (6, 17), (6, 18), (6, 22), (7, 16), (7, 18), (7, 19), (7, 23), (8, 12), (8, 17), (8, 19), (8, 20), (9, 18), (9, 20), (9, 21), (10, 13), (10, 19), (10, 21), (10, 22), (11, 14), (11, 20), (11, 22), (11, 23)]
def target (x : Fin 24 → Bool) := ∃ u v : Fin 24, (u.val,v.val)∈edges ∧ x u=true ∧ x v=true
def correct (C : Circuit) := ∀ x : Fin 24 → Bool,C.eval (List.ofFn x)=true ↔ target x
def input (r : Nat) (i : Fin 24) := bitAt r (varWord i)
theorem row_table (r : Nat) : words.map (bitAt r) = List.ofFn (input r) := by
  apply List.ext_getElem
  · rw [List.length_map,List.length_ofFn]; rfl
  · intro i hi _
    have h : i<words.length := by simpa using hi
    simp only [List.getElem_map,List.getElem_ofFn,input,varWord,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h,Option.getD_some]
theorem row_yes : ∀ e : E, target (input e.val) := by unfold target; decide +kernel
set_option maxHeartbeats 0 in
theorem row_no : ∀ j : Fin 232, ¬target (input (rneg j)) := by unfold target;decide +kernel
theorem actual_lower (C : Circuit) (hm : Monotone2 C) (hc : correct C) (p : permitted words C.gates) :
    55 ≤ C.size := by
  apply word_lower C hm p
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  change bitAt i _ = _
  rw [word_output C hm ⟨i,hi⟩,row_table]
  by_cases he : i<44
  · exact ((hc _).2 (row_yes ⟨i,he⟩)).trans (target_pos ⟨i,he⟩).symm
  · let j : Fin 232 := ⟨i-44,by omega⟩
    have eq : rneg j=i := by simp [rneg,j];omega
    change C.eval (List.ofFn (input i))=goal.getLsbD i
    rw [← eq,target_neg]
    cases h : C.eval (List.ofFn (input (rneg j))) with
    | false => rfl
    | true => exact (row_no j ((hc _).1 h)).elim
end GraphClean9796

namespace GraphClean9796
open GraphRows9796 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def obstruction (g : Gate) (w : List Word) : Prop :=
  ∃ i j, g.op = .and ∧ g.inputs = [i,j] ∧
    let a := w.getD i 0
    let b := w.getD j 0
    let v := a &&& b
    v ≠ a ∧ v ≠ b ∧
    (∃ e f : E, e ≠ f ∧ v.getLsbD e.val=true ∧ v.getLsbD f.val=true) ∧
    ∃ k : Fin 232, v.getLsbD (rneg k)=true

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

theorem obstruction_required (C : Circuit) (hm : Monotone2 C) (small : C.size ≤ 54)
    (hc : correct C) : ∃ pre g post,C.gates=pre++g::post ∧ obstruction g (pre.foldl tick words) := by
  exact locate _ _ (fun hp => by have := actual_lower C hm hc hp;omega)
end GraphClean9796

namespace GraphClean9796.Trace
open GraphRows9796 GraphUnion9796 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
def reads (g : Gate) (m : List Bool) := ∃ i ∈ g.inputs, m.getD i false=true
abbrev St := List Word × List Bool
noncomputable def flag (s : St) (g : Gate) : Bool := by
  classical
  exact decide ((reads g s.2 ∨ ¬permit g s.1) ∧ ¬clean (gateWord g s.1))
noncomputable def step (s : St) (g : Gate) : St := (tick s.1 g,s.2++[flag s g])
def sink (s : St) (g : Gate) := g.op=.and ∧ reads g s.2 ∧ clean (gateWord g s.1) ∧ gateWord g s.1 ≠ 0
def sync (s : St) (v : List Word) := s.1.length=v.length ∧ s.2.length=v.length ∧
  ∀ i, (s.2.getD i false=false → s.1.getD i 0=v.getD i 0) ∧
    (s.2.getD i false=true → ¬clean (s.1.getD i 0))
theorem other {α : Type} (L : List α) (z d : α) (j : Nat) (h : j≠L.length) :
    (L++[z]).getD j d=L.getD j d := by
  by_cases hj : j<L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
theorem last_get {α : Type} (xs : List α) (x d : α) : (xs++[x]).getD xs.length d=x := by simp
theorem extend {s : St} {v : List Word} {g a : Gate} (h : sync s v)
    (clear : flag s g=false → gateWord g s.1=gateWord a v) : sync (step s g) (tick v a) := by
  obtain ⟨hl,hm,h⟩ := h
  refine ⟨by simp [step,tick,hl],by simp [step,tick,hm],?_⟩
  intro i
  by_cases eq : i=v.length
  · subst i
    simp only [step,tick]
    rw [← hm,last_get,hm,← hl,last_get,hl,last_get]
    refine ⟨clear,?_⟩
    simp [flag]
  · simp only [step,tick,other _ _ _ _ eq,other _ _ _ _ (show i≠s.2.length by omega),
      other _ _ _ _ (show i≠s.1.length by omega)]
    exact h i

theorem equal_lookup {s : St} {v : List Word} {g : Gate} (h : sync s v) (no : ¬reads g s.2)
    {i : Nat} (hi : i ∈ g.inputs) : s.1.getD i 0 = v.getD i 0 := by
  apply (h.2.2 i).1
  cases e : s.2.getD i false with
  | false => rfl
  | true => exact (no ⟨i,hi,e⟩).elim

theorem equal_words {s : St} {v : List Word} {g : Gate} (h : sync s v) (no : ¬reads g s.2) :
    gateWord g s.1=gateWord g v := by
  have eq : g.inputs.map (fun i => s.1.getD i 0)=g.inputs.map (fun i => v.getD i 0) :=
    List.map_congr_left (fun i hi => equal_lookup h no hi)
  unfold gateWord
  rw [eq]

theorem equal_permit {s : St} {v : List Word} {g : Gate} (h : sync s v) (no : ¬reads g s.2)
    (p : permit g s.1) : permit g v := by
  intro i j op ins
  have ha := equal_lookup h no (i:=i) (by simp [ins])
  have hb := equal_lookup h no (i:=j) (by simp [ins])
  simpa only [ha,hb] using p i j op ins

theorem or_dirty {s : St} {v : List Word} {g : Gate} (h : sync s v) (yes : reads g s.2)
    (op : g.op=.or) : ¬clean (gateWord g s.1) := by
  obtain ⟨i,hi,flagged⟩ := yes
  have hh := (h.2.2 i).2 flagged
  unfold clean at hh
  push Not at hh
  obtain ⟨k,hk⟩ := hh
  have read : bitAt (rneg k) (gateWord g s.1)=true := by
    rw [eval_step ⟨rneg k,by simp [rneg];omega⟩ _ _ (Or.inr op)]
    simp only [op,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_def,id_eq]
    refine ⟨i,hi,?_⟩
    rw [map_lookup]
    simpa only [bitAt, Bool.not_eq_false] using hk
  intro cl
  exact Bool.noConfusion (read.symm.trans (cl k))

theorem bad_dirty {g : Gate} {w : List Word} (p : ¬permit g w) : ¬clean (gateWord g w) := by
  obtain ⟨i,j,h,eq,_,_,_,k,hk⟩ := obstruct p
  intro cl
  have ww : gateWord g w = w.getD i 0 &&& w.getD j 0 := by simp [gateWord,h,eq,GraphClean9796.and_ones]
  exact Bool.noConfusion (hk.symm.trans (ww ▸ cl k))
def legal (g : Gate) := (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2

theorem simulate_gate {s : St} {v : List Word} {g : Gate}
    (h : sync s v) (l : legal g) (ns : ¬sink s g) :
    ∃ a, legal a ∧ permit a v ∧ sync (step s g) (tick v a) := by
  classical
  by_cases yes : reads g s.2
  · rcases l.1 with op|op
    · let a : Gate := ⟨.or,[]⟩
      refine ⟨a,by simp [legal,a],by simp [permit,a],extend h ?_⟩
      intro f
      have cl : clean (gateWord g s.1) := by simpa [flag,yes] using f
      have zero : gateWord g s.1=0 := by by_contra nz; exact ns ⟨op,yes,cl,nz⟩
      exact zero
    · refine ⟨g,l,by simp [permit,op],extend h ?_⟩
      simp [flag,yes,or_dirty h yes op]
  · by_cases p : permit g s.1
    · exact ⟨g,l,equal_permit h yes p,extend h (fun _ => equal_words h yes)⟩
    · let a : Gate := ⟨.or,[]⟩
      refine ⟨a,by simp [legal,a],by simp [permit,a],extend h ?_⟩
      simp [flag,p,bad_dirty p]

noncomputable def initial : St := (words,List.replicate words.length false)
theorem start_sync : sync initial words := by
  refine ⟨rfl,by simp [initial],?_⟩
  intro i
  by_cases h : i<words.length <;>
    simp [initial,List.getD_eq_getElem?_getD,h]

theorem no_sink_sim (gs : List Gate) (s : St) (v : List Word)
    (l : ∀ g ∈ gs, legal g) (h : sync s v)
    (ns : ∀ pre g post, gs=pre++g::post → ¬sink (pre.foldl step s) g) :
    ∃ t : List Gate, t.length=gs.length ∧ (∀ g ∈ t, legal g) ∧ permitted v t ∧
      sync (gs.foldl step s) (t.foldl tick v) := by
  induction gs generalizing s v with
  | nil => exact ⟨[],rfl,by simp,trivial,h⟩
  | cons g gs ih =>
    obtain ⟨a,la,pa,hs⟩ := simulate_gate h (l _ List.mem_cons_self) (ns [] g gs rfl)
    obtain ⟨t,size,lt,pt,sync'⟩ := ih (step s g) (tick v a) (fun z hz => l _ (List.mem_cons_of_mem _ hz)) hs
      (fun pre z post eq => ns (g::pre) z post (by simp [eq]))
    exact ⟨a::t,by simp [size],by simpa using And.intro la lt,⟨pa,pt⟩,sync'⟩

theorem original (gs : List Gate) (s : St) : (gs.foldl step s).1=gs.foldl tick s.1 := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih => exact ih (step s g)

theorem marked_filter_required (C : Circuit) (hm : Monotone2 C) (small : C.size ≤ 54)
    (hit : (C.gates.foldl tick words).getD C.output 0=goal) :
    ∃ pre g post,C.gates=pre++g::post ∧ sink (pre.foldl step initial) g := by
  classical
  by_contra! no
  obtain ⟨t,sz,lt,pt,hs⟩ := no_sink_sim C.gates initial words (fun g hg => by simpa [legal] using hm g hg)
    start_sync (fun pre g post hg => no pre g post hg)
  have orig : (C.gates.foldl step initial).1.getD C.output 0=goal := by rw [original];exact hit
  have clear : (C.gates.foldl step initial).2.getD C.output false=false := by
    cases hh : (C.gates.foldl step initial).2.getD C.output false with
    | false => rfl
    | true => exact False.elim ((hs.2.2 C.output).2 hh (orig ▸ target_neg))
  have eq := (hs.2.2 C.output).1 clear
  let D : Circuit := ⟨t,C.output⟩
  have mono : Monotone2 D := by intro g hg;simpa [legal] using lt g hg
  have low := word_lower D mono pt (eq.symm.trans orig)
  change t.length ≥ 55 at low
  change C.gates.length ≤ 54 at small
  omega
end GraphClean9796.Trace

namespace GraphClean9796.Trace
open GraphRows9796 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- An actual wire path. The first gate is a strict mixed AND. Each subsequent
gate on the path reads its predecessor and still accepts some nonedge pair.
The keep constructor skips gates not traversed by this path. -/
inductive MixedPath : List Gate → Nat → Prop where
  | source {pre : List Gate} {g : Gate} (bad : obstruction g (pre.foldl tick words)) :
      MixedPath (pre++[g]) (24+pre.length)
  | follow {pre : List Gate} {g : Gate} {i : Nat} (prev : MixedPath pre i) (uses : i∈g.inputs)
      (dirty : ¬clean (gateWord g (pre.foldl tick words))) :
      MixedPath (pre++[g]) (24+pre.length)
  | keep {pre : List Gate} {i : Nat} (g : Gate) (prev : MixedPath pre i) : MixedPath (pre++[g]) i

theorem len_flags (gs : List Gate) (s : St) : (gs.foldl step s).2.length=s.2.length+gs.length := by
  induction gs generalizing s with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons,ih]
    simp [step,Nat.add_comm,Nat.add_left_comm]

theorem flag_path (gs : List Gate) (i : Nat) (flagged : (gs.foldl step initial).2.getD i false=true) :
    MixedPath gs i := by
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    change (List.replicate words.length false).getD i false=true at flagged
    by_cases lt : i<words.length
    · simp [List.getD_eq_getElem?_getD,lt] at flagged
    · simp [List.getD_eq_getElem?_getD,lt] at flagged
  | append_singleton pre g ih =>
    let s := pre.foldl step initial
    have ll : s.2.length = 24+pre.length := (len_flags pre initial).trans (by rw [show initial.2.length=24 by decide])
    change ((pre++[g]).foldl step initial).2.getD i false=true at flagged
    rw [List.foldl_append] at flagged
    change (s.2++[flag s g]).getD i false=true at flagged
    by_cases last : i=s.2.length
    · subst i
      rw [last_get] at flagged
      have h : (reads g s.2 ∨ ¬permit g s.1) ∧ ¬clean (gateWord g s.1) := by simpa [flag] using flagged
      have eq : s.1 = pre.foldl tick words := original pre initial
      rw [ll]
      rcases h.1 with used|bad
      · obtain ⟨j,hj,marked⟩ := used
        exact MixedPath.follow (ih j marked) hj (eq ▸ h.2)
      · exact MixedPath.source (obstruct (eq ▸ bad))
    · rw [other _ _ _ _ last] at flagged
      exact MixedPath.keep g (ih i flagged)

theorem flags_dirty (gs : List Gate) (s : St) (len : s.1.length=s.2.length)
    (inv : ∀ i, s.2.getD i false=true → ¬clean (s.1.getD i 0)) :
    ∀ i, (gs.foldl step s).2.getD i false=true → ¬clean ((gs.foldl step s).1.getD i 0) := by
  induction gs generalizing s with
  | nil => exact inv
  | cons g gs ih =>
    apply ih (step s g) (by simp [step,tick,len])
    intro j
    by_cases eq : j=s.2.length
    · subst j
      change (s.2++[flag s g]).getD s.2.length false=true → ¬clean ((s.1++[gateWord g s.1]).getD s.2.length 0)
      rw [last_get,←len,last_get]
      simp [flag]
    · simp only [step,tick,other _ _ _ _ eq,other _ _ _ _ (show j≠s.1.length by omega)]
      exact inv j
theorem flag_dirty (gs : List Gate) (i : Nat) (m : (gs.foldl step initial).2.getD i false=true) :
    ¬clean ((gs.foldl step initial).1.getD i 0) :=
  flags_dirty _ _ (by simp [initial]) (fun j => (start_sync.2.2 j).2) _ m

theorem correct_word (C : Circuit) (hm : Monotone2 C) (hc : correct C) :
    (C.gates.foldl tick words).getD C.output 0=goal := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  change bitAt i _ = _
  rw [word_output C hm ⟨i,hi⟩,row_table]
  by_cases he : i<44
  · exact ((hc _).2 (row_yes ⟨i,he⟩)).trans (target_pos ⟨i,he⟩).symm
  · let j : Fin 232 := ⟨i-44,by omega⟩
    have eq : rneg j=i := by simp [rneg,j];omega
    change C.eval (List.ofFn (input i))=goal.getLsbD i
    rw [← eq,target_neg]
    cases h : C.eval (List.ofFn (input (rneg j))) with
    | false => rfl
    | true => exact (row_no j ((hc _).1 h)).elim

theorem positive_of_clean {v : Word} (cl : clean v) (nz : v≠0) : ∃ e : E, v.getLsbD e.val=true := by
  by_contra! none
  apply nz
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  by_cases pos : i<44
  · simpa using none ⟨i,pos⟩
  · let k : Fin 232 := ⟨i-44,by omega⟩
    have eq : rneg k=i := by simp [rneg,k]; omega
    simpa [eq] using cl k

/-- Every correct circuit of at most 54 gates must actually feed a wire
descended from a mixed AND into a later nonzero, pair-clean AND. -/
theorem filtering_path_required (C : Circuit) (hm : Monotone2 C) (small : C.size≤54) (hc : correct C) :
    ∃ pre g post i, C.gates=pre++g::post ∧ g.op=.and ∧ g.inputs.length=2 ∧ i∈g.inputs ∧
      MixedPath pre i ∧
      (∃ k : Fin 232, ((pre.foldl tick words).getD i 0).getLsbD (rneg k)=true) ∧
      (∃ e : E, (gateWord g (pre.foldl tick words)).getLsbD e.val=true) ∧
      clean (gateWord g (pre.foldl tick words)) := by
  obtain ⟨pre,g,post,split,op,⟨i,hi,marked⟩,cl,nz⟩ := marked_filter_required C hm small (correct_word C hm hc)
  let s := pre.foldl step initial
  have eq : s.1=pre.foldl tick words := original pre initial
  change clean (gateWord g s.1) at cl
  change gateWord g s.1≠0 at nz
  have path := flag_path pre i marked
  have inC : g ∈ C.gates := split ▸ List.mem_append_right _ List.mem_cons_self
  have len := (hm g inC).2
  have priorDirty : ¬clean (s.1.getD i 0) := by
    have eqi : (pre.foldl step initial).2.getD i false=true := marked
    -- Every true flag is created only on a word which accepts a nonedge pair.
    exact flag_dirty pre i eqi
  have binary : g.inputs.length=2 := by
    rcases e : g.inputs with _|⟨a,_|⟨b,rest⟩⟩
    · simp [e] at hi
    · have same : i=a := by simpa [e] using hi
      subst a
      exact (priorDirty (by simpa [gateWord,op,e,GraphClean9796.and_ones] using cl)).elim
    · simp [e] at len ⊢
      omega
  rw [eq] at priorDirty cl nz
  unfold clean at priorDirty
  push Not at priorDirty
  obtain ⟨k,hk⟩ := priorDirty
  exact ⟨pre,g,post,i,split,op,binary,hi,path,⟨k,by simpa using hk⟩,positive_of_clean cl nz,cl⟩

end GraphClean9796.Trace

namespace GraphFormula9796


abbrev Matrix := Nat → Nat → Int

def col (w : Matrix) (rows : List Nat) (j : Nat) :=
  (rows.map (fun i => w i j)).sum

def rect (w : Matrix) (rows cols : List Nat) :=
  (cols.map (col w rows)).sum

def upper (w : Matrix) (rows cols : List Nat) :=
  (cols.map (fun j => max 0 (col w rows j))).sum

theorem upper_nonneg (w : Matrix) (a b) : 0 ≤ upper w a b := by
  induction b with
  | nil => rfl
  | cons j js ih =>
    simp only [upper,List.map_cons,List.sum_cons] at *
    omega

theorem rect_le_upper (w : Matrix) (a : List Nat) {b c : List Nat} (h : b.Sublist c) :
    rect w a b ≤ upper w a c := by
  induction h with
  | slnil => rfl
  | cons x _ ih =>
    simp only [upper,List.map_cons,List.sum_cons] at *
    omega
  | cons_cons x _ ih =>
    simp only [upper,rect,List.map_cons,List.sum_cons] at *
    omega

theorem split (xs : List Nat) (f : Nat → Int) (p : Nat → Bool) :
    (xs.map f).sum = ((xs.filter p).map f).sum + ((xs.filter (fun i => !p i)).map f).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : p x <;> simp [h] <;> omega

theorem split_cols (w : Matrix) (a b : List Nat) (p : Nat → Bool) :
    rect w a b = rect w a (b.filter p) + rect w a (b.filter (fun i => !p i)) :=
  split b (col w a) p

theorem split_rows (w : Matrix) (a b : List Nat) (p : Nat → Bool) :
    rect w a b = rect w (a.filter p) b + rect w (a.filter (fun i => !p i)) b := by
  induction b with
  | nil => rfl
  | cons j js ih =>
    have h : col w a j = col w (a.filter p) j + col w (a.filter (fun i => !p i)) j :=
      split a (fun i => w i j) p
    simp only [rect, List.map_cons, List.sum_cons] at *
    omega

inductive Formula where
  | var (i : Fin 26)
  | disj (l r : Formula)
  | conj (l r : Formula)

def Formula.eval (v : Fin 26 → Bool) : Formula → Bool
  | .var i => v i
  | .disj l r => l.eval v || r.eval v
  | .conj l r => l.eval v && r.eval v

def Formula.cost (c : Fin 26 → Int) : Formula → Int
  | .var i => c i
  | .disj l r | .conj l r => l.cost c + r.cost c

theorem variable_filter {xs ys : List Nat} (h : xs.Sublist ys) (p : Nat → Bool)
    (yes : ∀ i ∈ xs, p i = true) : xs.Sublist (ys.filter p) := by
  have hh := h.filter p
  rwa [List.filter_eq_self.mpr yes] at hh

theorem formula_bound (w : Matrix) (rows cols : List Nat) (yes no : Nat → Fin 26 → Bool)
    (cost : Fin 26 → Int)
    (cert : ∀ v a b, a.Sublist (rows.filter fun i => yes i v) →
      b.Sublist (cols.filter fun j => !no j v) → rect w a b ≤ cost v)
    (f : Formula) {a b : List Nat} (ha : a.Sublist rows) (hb : b.Sublist cols)
    (hy : ∀ i ∈ a, f.eval (yes i) = true) (hn : ∀ j ∈ b, f.eval (no j) = false) :
    rect w a b ≤ f.cost cost := by
  induction f generalizing a b with
  | var v =>
    exact cert v a b (variable_filter ha _ hy)
      (variable_filter hb _ (fun j hj => by have h : no j v=false := hn j hj; simp [h]))
  | conj l r il ir =>
    let p := fun j => !(l.eval (no j))
    have hl := il ha ((List.filter_sublist (p := p)).trans hb)
      (fun i hi => (Bool.and_eq_true_iff.mp (hy i hi)).1) (by
        intro j hj
        simpa [p] using (List.mem_filter.mp hj).2)
    have hr := ir ha ((List.filter_sublist (p := fun j => !p j)).trans hb)
      (fun i hi => (Bool.and_eq_true_iff.mp (hy i hi)).2) (by
        intro j hj
        have hp : l.eval (no j) = true := by simpa [p] using (List.mem_filter.mp hj).2
        simpa [Formula.eval,hp] using hn j (List.mem_filter.mp hj).1)
    change rect w a b ≤ l.cost cost + r.cost cost
    rw [split_cols w a b p]
    exact add_le_add hl hr
  | disj l r il ir =>
    let p := fun i => l.eval (yes i)
    have hl := il ((List.filter_sublist (p := p)).trans ha) hb
      (fun i hi => (List.mem_filter.mp hi).2)
      (fun j hj => (Bool.or_eq_false_iff.mp (hn j hj)).1)
    have hr := ir ((List.filter_sublist (p := fun i => !p i)).trans ha) hb (by
        intro i hi
        have hp : l.eval (yes i) = false := by simpa [p] using (List.mem_filter.mp hi).2
        simpa [Formula.eval,hp] using hy i (List.mem_filter.mp hi).1)
      (fun j hj => (Bool.or_eq_false_iff.mp (hn j hj)).2)
    change rect w a b ≤ l.cost cost + r.cost cost
    rw [split_rows w a b p]
    exact add_le_add hl hr


def tr (w : Matrix) : Matrix := fun a b => w b a

theorem rect_cons_row (w : Matrix) (i : Nat) (a b : List Nat) :
    rect w (i::a) b = col (tr w) b i + rect w a b := by
  induction b with
  | nil => simp [rect,col]
  | cons j js ih =>
    change col w (i::a) j + rect w (i::a) js = _ + (col w a j + rect w a js)
    rw [ih]
    simp [col,tr]
    omega

theorem transpose (w : Matrix) (a b : List Nat) : rect w a b=rect (tr w) b a := by
  induction a with
  | nil => induction b <;> simp_all [rect,col]
  | cons i is ih => rw [rect_cons_row,ih]; rfl

set_option maxRecDepth 100000
set_option maxHeartbeats 0
def rowInput : List Nat := [4097, 65537, 4194305, 8194, 131074, 8388610, 4100, 8196, 16388, 262148, 16392, 32776, 524296, 8208, 32784, 65552, 1048592, 16416, 65568, 131104, 2097184, 32832, 131136, 262208, 4194368, 65664, 262272, 524416, 8388736, 4352, 131328, 524544, 1048832, 262656, 1049088, 2097664, 9216, 525312, 2098176, 4195328, 18432, 1050624, 4196352, 8390656]
def colInput : List Nat := [4095, 7930, 11241, 15080, 18387, 22226, 25537, 29376, 36775, 40610, 43937, 47776, 51075, 54914, 58241, 69454, 73290, 76616, 80456, 83778, 87618, 102150, 105986, 109312, 116482, 120322, 134813, 138904, 141961, 146056, 149137, 153232, 167557, 171648, 174721, 178816, 181889, 185984, 189057, 200204, 204296, 211464, 232964, 237056, 265531, 269370, 272681, 276520, 279827, 283666, 298275, 302114, 305441, 312579, 331018, 334858, 363778, 367618, 378114, 396313, 400408, 429057, 465928, 498688, 526967, 531058, 535137, 539232, 541267, 545362, 559655, 563746, 567841, 571936, 573955, 592454, 596546, 604736, 610882, 625158, 629250, 657941, 662032, 690693, 698881, 756228, 768512, 788531, 792626, 821283, 825378, 829473, 833568, 1049839, 1053930, 1057001, 1061096, 1066179, 1070274, 1082535, 1086626, 1089697, 1098883, 1102978, 1115214, 1119306, 1135682, 1147910, 1180813, 1184904, 1213573, 1229953, 1234048, 1311787, 1315882, 1344547, 1348642, 1360899, 1381386, 1430530, 1572967, 1577058, 1605671, 1867811, 2099679, 2103514, 2107849, 2111688, 2114003, 2117842, 2122177, 2132359, 2136194, 2140545, 2146691, 2154881, 2165070, 2168906, 2173256, 2177096, 2179394, 2197766, 2230429, 2234520, 2238601, 2242696, 2244753, 2263173, 2271361, 2275456, 2295820, 2361627, 2365466, 2369801, 2375955, 2394371, 2402561, 2408707, 2427146, 2430986, 2435336, 2459906, 2468096, 2492441, 2496536, 2500617, 2570248, 2623575, 2627666, 2631745, 2637907, 2642002, 2656263, 2689094, 2693186, 2701376, 2721798, 2754581, 2787333, 2852868, 2885651, 2889746, 2899987, 2918403, 2988034, 3016721, 3020816, 3057665, 3127296, 3145935, 3150026, 3154121, 3158216, 3162307, 3166402, 3170497, 3174592, 3178631, 3195011, 3211342, 3215434, 3276941, 3285129, 3309701, 3334273, 3407883, 3670087, 3686467, 3702791, 3735622, 3756098, 3981315, 4195262, 4199098, 4203432, 4207272, 4211602, 4215442, 4228006, 4231842, 4236192, 4240032, 4244354, 4248194, 4252544, 4260622, 4264458, 4293382, 4309762, 4326044, 4330136, 4338312, 4346512, 4358788, 4387456, 4456762, 4460602, 4489506, 4719158, 4723250, 4739602, 4751910, 4756002, 4817414, 4837890, 4984882, 5243054, 5247146, 5255336, 5275814, 5279906, 5288096, 5509162, 5799974, 6066210, 6291870, 6295706, 6300040, 6308242, 6312082, 6324614, 6340994, 6349184, 6357262, 6390022, 6422684, 6426776, 6443152, 6553882, 6557722, 6570258, 6619402, 6668546, 6815766, 7098386, 7340174, 7344266, 7372934, 7393410, 7405582, 7471244, 7483528, 7504004, 7532672, 7671818, 7962630, 8245250, 8390525, 8394360, 8397673, 8401512, 8406865, 8410704, 8414017, 8423205, 8427040, 8430369, 8439553, 8446721, 8456012, 8459848, 8463176, 8467016, 8472384, 8476224, 8479552, 8488708, 8505088, 8521245, 8525336, 8528393, 8537617, 8541712, 8553989, 8570369, 8586764, 8590856, 8619524, 8640000, 8652089, 8655928, 8659241, 8668433, 8684833, 8692001, 8701185, 8717576, 8766720, 8782873, 8786968, 8799249, 8803344, 8913525, 8917616, 8921697, 8925792, 8929873, 8933968, 8938049, 8946213, 8954401, 8979012, 9007680, 9044501, 9060881, 9077253, 9101825, 9175089, 9438317, 9442408, 9445481, 9449576, 9454657, 9471013, 9503820, 9507912, 9524288, 9569293, 9602053, 9634828, 9667588, 9700393, 9704488, 9707561, 9733153, 9737248, 9831433, 9880577, 9901064, 9950208, 9961573, 9969761, 9973856, 9994277, 10264609, 10486109, 10489944, 10494281, 10502481, 10510657, 10518789, 10551628, 10559816, 10576192, 10616861, 10748185, 10756361, 10764561, 10805505, 10879001, 11010133, 11026513, 11030608, 11141141, 11419665, 11534413, 11542601, 11599948, 11612232, 11665421, 11935753, 12058693, 12083265, 12124228, 12152896, 12222469, 12509185, 12583740, 12587576, 12591912, 12595752, 12600080, 12616484, 12624672, 12649228, 12657416, 12681988, 12706560, 12714524, 12718616, 12780044, 12792328, 12845368, 12849208, 12853544, 12886304, 13107764, 13111856, 13140516, 13152800, 13238804, 13259280, 13337092, 13365760, 13373488, 13631532, 13905960, 14188580, 14463008, 14680348, 14745868, 14778628, 14811164, 14942488, 14958864, 15016200, 15065344, 15077400, 15335444, 15618064, 15925260, 16199688, 16482308, 16773120]
def rows := List.range rowInput.length
def cols := List.range colInput.length
def packed : Array Nat := #[498977992663909855585207806535812310131185553369012404964858483113522682293492829802928309733977869407225465933356277182134256233640808312171396345710949843055159198567994440869582215839822645715682622481299922724840694895271329886550630538908645320649582290855898423701278705750757052601565272726958674358246562319681934414336331718696302837289283296771035751428445178450342341276068496643698389548176949307580113602097174311176933428090246970318571767772301601694693306038436380559357564556561532011765448177902477258777969534058426728289615754197295092912057897092527796512131843962909439415901453510406183492878173734868877524261014631606915731903226484588959819466121846296195865114356363686891101958250611419086334782711506742301413198609645949644285436966991900987856494784219416663149155085879868631899232481780779579653209450926401745067401595480009276041383198153251275082246239229958270504922462878811417147285958354755827903884530259912407314200064571692113556068768585734105110202344420569174717812112927619641838964714788213268297875561856170377933233426898403719218468417807207204710664837528953322132923744346042456071144595984854133578199136986103416091913594156049112819920717468179281003775386014082794804344058, 498977992663909855585207806535815379314260960290807270913833850369699842295920584614880100280563815645011655324523142098697573175081497490366153185960265259524821840187826634403937323682976116112794788474163666354045057012981435882270959612353671129467414944430872105465448513951126593816916034376070083316655405406828147684267086721074339686104047513701025873942588641036929818020747469316673327493647614056323823480992956799907429676462175501264600896475217964703605464344281752682846279253827650902589522651722084172516692821198124455825989777297674378787112019333245072326190540689088897325752509674036740745959462213379504578450421924944191268825666904450986420559767094566550390552273561439976148629558697878164068497229611632921127548949302255410818296604320968367786112990715251773851949796921315609870018970041234248500165634030440689923517755069382758790132734208267137445929879442248126579526113577441517483918813878431885138155760579411347557968751165714470383710413273727199109022480766861528147630386201606673393856733562552985731457593570903285525000165640678589079380917056210939404341353996564228185283224578650754980886574258547254266489134536458189451505692330259702750560014518302430872408099111395533188101370, 498977992663909855585207806535815379314260960290807298865799498509881482458530309505158453500543171699589261807432782236098962666392668299734425881692020470692008065597363049566831901834023884223865428555444391228364177886594652221287267778420467301309822708442586238346980370232064373723586221157545188016389456585855111989649709040729285646155690237914637390097184043849341397113638829124750395155281240016871897835452162207757159483134574556319957000134885552859397472809522513392852317429402966962758787831879293021416255454597748387283698411280519241137333049187075255704129307536345263696966576137489232257421285753004017543459665668012684510204096610315419875152552527225699648587264198491092416776850007014258997128843136874797430834285524744231155435755305195937904806840002286432539391030707341480617027076318036956710049105385929693282914719047044504598039263046744335301761670643807926397771478561085818603646067624524837873111364049860224087879145149592745277259173055052222655522942134266312243789971337260798140407431097246939778797337946731214460646382827083156124802240393377349693680404838408819588846265146123864927805119057026226491602971046313081145937875271020068719549829733214761145675469148934771950875898, 498977992663908666640078951297713474279940843620779652728984964244473459657144796101664070140429338139320178811256581629229451028968082438317039793889739489604002310210280891335687944206613455535498398741672425327609569109107460784893088550021990951973535631301084133874258151509226318218805399485050299902926050130525591870913632617025343502034852432486486781107489796720526652901754714618039108682019655999818631001365447342838704541228581123458532952102437856648604111836215529108616536890972555979838928461557951377530633112553186470083676430721726951142206526453813726446835483015805905702410913281474834997967083233682297196130324398150212554323949350032677573130886827174084200916560449914013909140494249590009012677221925959961741950505458351748885029176766514100125088711200368541623812398887941488192563190878249468332654615503164197393317392670128338206414555552630792334678829547986552854576116653111078603568285677219222900257248187409615426798614539033220082811065423873714705147824671235976272809041310286241211708938635396198251551058732624627512970791473513219752020797916483714639275249366224735625670796875377852594034420492166670622572390254432928781331829523550072870557007026832549587860583630910818852926714, 498977992663911044530336661773914215165505670039040037125690193308839885001876292814130583272546653560079693344304305440894277650629128960308503946008233935430846310019724682618375921774828167800784952649817284120002590685834250936357393682652060800002847076173840010909173522755369901130572555956755724887428666710571498877962109896489946987078947583824392871441792984109407634997213294507409637295135703778956503247345426122520293553295950804348400879944574484169673867286946142480033915431293353713744947533917516660386794700119072661877862716745366683435385334157765939512319439105055244219791891157694597002288264687213790369640035630066818795128031710118371050894527193525458391645364697882477712441506344544086373346256203840019623710480584660953884552322823319608786164577574125990082192103001187199547501647788786473200522543604925578649029213872514311404367946179625719091298393541993076919166735675055135370341513005834277875303183670617840911514442444207373843179685039344004587056555872904521301870563610606574669313888373181919687326784131787885406198130429199856370984330814016144024090001649327881821695076003449348070146816526917106210839870384309472499638088549351650257655792443831276217072930559672926738183418, 498977992663909855585207806535813844722723256829909844927337578776656672347056326378626726523821052919889014593440471954175057551902271090992368185800190328748074975522391875049252227999393650513668207494449242343036994608090571331384996250956467380091953603697548599478476342635264953664341664745515330691801908175455435011467371521928951242497173775263961349272493650058287085560660973378193841210533613182227754349117900295289183094734325786227964385171972666127037534669552278491618020739876030747233290544539446293389549674619813628607538892047485152397548208874026280392400473650194788433885122619700661579566143019256249586973679184185457829777786838674152318242647796533665991492136719856114029975310557111288868216314539615012758679809986298704821355882066150503790375363655034671774328447170700995258293109574748516444141351857342373103157575392815777710618439314832462310265320176723738861777087906322537703090018939279383404865819830653220023156083746408122122209424787963400086519996359976630568559738175886337467409126024312793998520893303623848521119997703101640312383389029457608625181194056745561988736902423131620809232525300316705285273641637665137800521153198429902937481570885777426616296222053946711406671098, 498977992663909855585207806535815379314260960301623982154999905537516491047481197107039345762825908289171388651969845379076892613276215431228510974277809041801339346629065970590956392988062496056701302193075562516083687148713282065201267128913167104765759335566534171979116868687636525451600031300470178867707563296623543649223415893085906309904434012674039761542441882681524640080052977051012138147429048970652823574292175935946233093718535911421218156182153684301118533574414416223498912317922539167646979675648825774287925691888767540250708337070089304757195879009653799069981836458348028214753822532552192305516107381937789151605082634896694303669260375457195945264576926760562474691228678375466019940702780922485784873207185715307212014729950947720053698227183373083933394871389983137842352913370992330208508610418883649196296791209804470280718500307252425010271670708456814331823320068711343904562139394957210013002106176616981411192625396158878021700053210884944954513665675489335253635463851784680752976315098956003916350230072297529606578840116473806773770527158650268954104288063000738320705699902894538169768887148841371616577987929941793548829127392299869681505902324521209163779473839058511697388756088923849224746234, 498977992663911044530336661773914215165505670049856734390873424600258396816196106049087935586816898596159041784610431835075048027318623144197538987448115085524237270689190380067610361377352998408407916236513833146196329985578384964166885044648665699366790679761671184651442874311070268226346421774853201250013097719774010862550810912215079151061538655502455580618980142485858596209645725598953969816269018027139262572379585792209852821495712630065443636399542591107105486030328738111468389037023649925917572425814985975160682004822724178599188517525034058549969702517089431754244509087958203129381010020955833247390276388375014338365811313636181046092174979913220640218923408746597543854895115243860818089700647911034133944734913493028834320911445747174425646435875017632452248515874049115162334677388737881546948701879113038596812073088718474406042540991489446541539232013127668797665609907770071700862628675991781240436832839469593001628664348082746482717538705299438175419785738044618180596283946482529348612239336588736850885984891545853779862525076675100435392821460286970547837988508019030416461127818889933441801889963448086853029506779945094190152330195910754899160014386525581526422022749780894298624754943084716085605626, 498977994519117188077038381437655230156820248119081703893835445351838169698094452809413457597451849373400077976837059364432278217931077234110343567372372386201136569779831296127028696245220742464076734780679528365303485511027918128739429876805050072037362372866186044266513164925862127753625789799516902339097455456814787383933763482291080001623264225479605993930899562224509263255330914944351916310601027004494249153250680803236163957650319824794249387062370623992746264227473149963050830951571611899357302049474467091291137603454740996259272526477171792846085339736537142807133837366000269835826197773416247742699810109825938864385829975578688974289349636456069433940416595580318280913047974949246648179529209757594503847570551800472475314724920148467866316510605859177813850954409033689759911199243805957141676040945194325885923325973241005549642806484445322126579697809452504825795728208248122583160268296925061796798424384318552875476180947175816242485463147273920940971013017882235237600076791183758195403606626110115249775363009705546716236640197525536520213195678373449279819338665649044283683527862936900768141148953474692763209935142608345882278870964194928044118602550238315444245776110571605578484622577221390045934842, 498977992663909855585207806535813844722723256840726542192838155966426561368023873999320954381970159797001929078170058578937523965582704726978319390126603352133348478707804664254168917580182278338501843743445707020141873306831132989265923618527089892165727986301577497159936516098537705187090731966390305181793906274029042694390887470781419401445520625486255084006408915872532380993828073201716017191973414252091107091228657511809283574003951983842373496255118904193530937607453991082541172191039542943439544357820759806601238989731176030100037333636029058599269493174476561484094301405477424357944696196842261979509035322777131911946316199761518477051164552301101953495234347994885357768286106134836589547428088245836024070610218705140386280767491938644777773653361595130427223986278172944292518813346063217426242847240793274429031528527296680434823749233796120123662587651887190347817737845422857773451533320940368229192782467994810949049851436182001652674312663676862018286613035939224005972995399374405147347969950302607164952213157423333746092980147342146433664470332754315792993050578542611590570834547330667894727004800797426557563619900125011591500339498894575588956831189638970894660054806694121401023577369023625676059898, 498977994519117188077038381437655230156820244411048096245377481624987160704292654432565976770388941841549303014393740315763097342570478867063623988858219215104772258048296133683828760706452700688630323969107278144557555663919534790430783481157959913095315524300294630964790070153941135730607231217978177130607489332290565849089923455779381819406160839213364451518698866893635812685839510345474769716021866606887465792168194586720656060120574502368718049081164624031584642680338168115276037047887926319541024149902560503091501195916860712857238409584919231321879863401436615307169220632440236876551900399537472278261511002330834629295280587572172019601958153725170005850254998703482589556974237322848764004257466000794287390963343118378344151950047423608289939971800740694598409607753721307131064361436241476962931053217858545770574991413096048526859928826265571922499044975090005068344765405307825546628590145163360913749077989758151379435055835834779660334685194634717438473865439899548847664364808158092058728659396195962751320649635670657286332878463807724467843252975854591787276949970444993380456060515057842235274399328019586974964537025554363373519986078522458314552616720708862745931067625158866379457582124966630973371642, 498977992663909883229951316004705687413450154458470349768259096027448414820468595866714923225812670238888294570989855343517524716521803906816531352865150345609464328759047706139757725251358846634364450095018501688786780141549767401667211069642417456729412201190520800489882716875235226725675511689387570052279323680252527583907142574747492437799708143248224416638000363362947311812863818381114612626781242699210402317878491703937315128235788253797769396201063567922645830097898780675075423864858512827313259403121031542860593294749634813996365378847441844027215286023027869661948784832650111297258834166075028677111160396292119058556837745517467132750039675917126108972721251345056941831292771157135811693772069805423533305248038155412019542474608313817785400361431453625988804998724986910464191805328372005512721284369416762522699436650966718216379386936215912088348190905568581066238476729779049136542806763665615170930764014588011466953926584753240952287193736805170833022814471544116733949264963290372377913963975591391139457905747192291995489890307875903138883465701494231570995112727479005564973849179263854505421451334984431876200414373045342662997503064678646223832905122260472560862849194430752706683928210656691502052602, 498977992663909855585260534699551082446727414297503969795576242168069917158861955497867020277664420088874382622429619323682256383707856648569373554425842630117645750028215036716661200372636581100234336167253660089971978610931973952096789154693633878295737096265023305104610089777725550131360802199618680062049882147657534512635474641375084560224337571674541866613279635488992021534413505637537727383798824070502885169823837616035059982416033663801695480022879912618495631835971337808590897868948839167631145522795088950552182893016325134030752501034343783832836148172068145041991562592954883980557639618664584722613693862766152952148469488416725398977624027973299375370564556664629425594934748108433414352525271447639870942627190095290966096718837922964015342897730884034445940790085297120732436751719251424745842635025105645725512567688157269444631944531239800075502319652124077778029605865550571369315219996760770320100312493810354055790502857013315832454424185310798241559906954158922474607304997924757931044111819595531912426336455636028509225400524774629302259348318780707682660131357886040147297081048344378642913837016550578052017056402591743872176906821176659280836399693118963780600828634539455109361210953654928964973818, 498977992663911044530336661773914215165505670039040037125690193502532568145940356002067866714544487593098952965181568029183653920307435466125288970982325143730684963606512143977462670966484494747362938935702439880901333096273031736687031707825533744204692173042773939724400054762817562421064753498992393204326594936218666142331850135723134258568546141350169025233173688719141308254810327144239178001119966372627742805861615721975352038159653572934292788778705123020421399859326788527653885590859910224797916575800893065000426324979176771397764749264236341735218791885517570643452779175140307030621914912655242210085831405801125757248829459281355553394413380183378839685215222327230325860202331841263425098914546149803434042247135920268375627871730445621000522865637391337051958005416661142910057189818694307926636036543929449897372606736275865090784240157393009500398473182840910749252334279246824536078527712025832922659815767660636073790044902420261187119085918635048573449145429987007899307968281869391989776613780091117758463082001746016889268376582051764056415532644372352209947994074510213810361830874378098983573688732612787494147030499564861914748317219791418349876330030221326450365112750184294495849239915497501303108858, 498977992663909883229951316004705687413450154458470349768259096027448414820468551245613246835486684852360697309438307241921226646551598448685690799359949415419721122902424679136985128479440213319123981992220725192978153317750470852762364455684775581041586901265360463350203269034611407686654069320438500160398563817894835148660027833992734728539013128445147346683197146686668929030999669734989820073569951841218642827217474497142527969623653634045404209913719283927953114664246437229760540606146976603978389851941320373996329101658793216791640359862162035016605004149688436676052552850223442955904647179792508290747855552513401395918456516735094201355903089313312585394120236655017055253755920249214453413244889581947147837118584288279412961973711901323904753405808695914936268417102295354670387694379433125179636468307801807219850854656887185806218720073619142517081603220492484917484279704180730583927519260723687369663583240189343588820386650160095765708053255716807236188509227416542235074198030191256117950804824618298934117132253415771182022598334618363118696077740843541952810128075640607335293516423216564761957693434686435819679238681575511979457982987109586749052522904394244521925778779635238119497441315561310295553274, 498977992663909855585207806535813844722723256829909858903320402846747492416664000876612969922255363180862606757684959149254187408305121545269971950983803322660609644971505565904204175885708955078371857885358736892149646489346942494344005913219395206902649546608215248532152636204092369660978378010284394662810379300846516920128340036243999237595960660849899505668841969772944317761504737062555333690357376956799217827997369614319789883209485999747491016733544116645412140025862675675613421598968214551443111217721780894026646260454553079333401560635501824450025410711573257230360171784197534810676708708998819550814026118762586736035521062227851931878038209013998262004625699704287785029493276768657804514434828551122194018123219701606120365979935347251944390695921553438618657185835827026702701793825033183269599712507481244344818401450931738769295545444476613379097408800200036996155436888795504197273858247062980200534837200486815984410974207302865321839093096275259383683479922848090036467392700125536830886158888523475759708338772256312555524482603759065248938546951443340528663748014759058262090991330968906531689221197145598661743509538699289142971416302788052087781227830536713973689022726533682859198916039887233089139962, 498977992663909855585207823837242571003851445693463394282599840383494185239959562824364443149773465234103825197146933723861343926198384074383551407908648544745096158709199833182329438929291617419925669198659631847801982994626260441878295106186562915644804695281702608947939365297477007821709528222738684916544281114962594804209898870062306041456903101517740436266804480451579441299629509268082838096124156846097668988954468079406848949439205869983140700588007496409816999516587018718875784403207642347407966398629355023188017964467264980997065059845673360968123186831881352085672412718620403839445229041258684492788179459549099889549872762948599876226056800280063984830421987016452308126641580463507762576280503242582716828353318342577121874401941818029685377452415709161939481845005571450824838730824387389483079144857858827598865072265269981398174834587538697279244309015848985506287409216612934561628438889049771207002424301314140293933318825663891296894161240534420905495933178106325965067891523677545412161855142151333655590473516718090193169921711195949599060700722306514262755825363389780801156853086898980336389435840169312527403005985618004446966689523479303254142261440137331717089627238274015767229080937280095453312250, 498977990808702523093377231633972459288626269292415931201086012997413729310460321555334939662488563935409087750508303005689951964497998422232917609550040141209307020791708787424900427445514556230120332924267211744945675347106926041824985941211406995795650876520056316622203354584868193336403725454371458761409263300061585897852661449189125712043071322860184978969739028486288725136182945485471019594763786678272640593257700321883365285972560441663540899167222073619913496557193462878105411240040072222279148919426325793738128195825132225351198908374361588258634821387832704661941590653511202532663445516096077937234572741182969442080240339536059840741408411147572125605050069436679424525423800112722997135246893186971189325634727432027596333991702762906071911325658711386993048225215949218768210362291761539412452165577986141952683829753859978589404199575147649345261619197284194201617486644965652609193441766163108581439108109252251041655123439706816151909903513750761505957010259607052048691565369841207309902716775557341269836256728621746026265974385403348627744521806174026944189692828261210830641729410149844991969876359261246826658875259590042644966500038288535514043566632731819481676539648968465362092396286792480185775354, 498977993584092692501155771687127171898035363589739667796305493168370582303053015474644511242398668972544461153243354532113678426167712768687823604989531661212069193153979751485454681092460088144573472688550925943670280514364386999426797445750511780926882105433455341042154870828870285568705119741566557236556354127583674426935404951141775341093094951802532344151260171090300228346456784860050169071886519948829724118694035244505677836189079806768033256738200509495371362108598860610910192974489759699144364874573404276375132308921121860643493301391196000451085575774379685983833825779388333590130941906414980689134346029941677329865640345884123535387894053230162396783272848501132033197007346165390686318693940284888149766539907446050603231209310349128886216070510718223324536093277332595982061216075260122048741414371862033754876138789147308688776156997532938761299994663697422482217661561511550005237178431497637581478156611043289186717391969236581222998734796635288033180757613398851186401154528548379316631161890727993065655109171483651960242664462057085479758704996523284141903273878796322956250493655106856406473574146401968289865039748436729872280351143841118927738538629266049989704353662378823850161131632041800585835770, 498977993584092692501155771687127171898035363589739653820322669098279762221753977981923150422171058976107557830723414094978473826329030839447632164118743667202111838900760109174494450679663028709236499624796167176313760759392903405641428552581862082863408861331635898823109112564407914537557190184451490211751845759719551430786989283361397747995380897433022244468786826090041418386083189286291482889043863445155224237946962637361928731959345955293474491987450590258593449981093042137839571447270547016606323738473622614694347044253999908291366377300862334501690588308030087840573170319865764518596125858108448973811110134541680443273168994785065049319649676111981513018525957973361467345163140687969183099560450962355504630178113314713989982453390852279933960202724148198513293026549691414085644701150095512900032267215352963686596057948046123698793523659212570378147770235634717438292266243307950550767378474103804846193138741391091502402575200739898039680474915737301461385138231886957693715240508241444182971202068110677393421813389520819377897274384091412256547585236681557610477913367430509144439476822081102841124230147296388596734371234523529145901297880571151744144294500428113249210996575030111945894802338179078708393210, 498977993584092692501155771687127171898035363589739653820322669103008587502412900188003525261078684584961503402681912551783637929187029370429640199128703781311435895031140899960773159066361882145046123748005211701748772888058443616626750532838901851929743843101998536457521015255367102101304475154167033259001427979873731483302483368364052551111000528857229532197982288912348192848718540792054810447918341999114533508959400047466451752209038051346050056952720897084282717137155091630779103838277334732088451427101173876515293158666429280101555994990461675391845315717737360088150156007726019347089088395683029933007519988726327436407959920541401846796193138836068644580292544706119925160271119675838599220127294444815027865141979156868689767489848091195063663416716914605531974561126517200210384805830065319648274396610346597212921501078345197933139327939047887134356827008174665110110816331429669878933716038499290232374821797053599475909612017443080294069528623036098911286166248483659139926431623917786277515322721579743179643557559903459484846084939932194833830374896724709382525755680773024934126074023315332264427619579027498472320772448062210639708349790201617077922603851006545346575044080932702399568898605114977013069050, 498977992663909827940464297066922002031996359201349340086573465187518783790004537814433700662294028693477606974083765513713802838134671503652701020546077176574567464676263849462431319969273711378528524725682260770006945592710547401248324691970101260161623116585530408499355793198833495711787657836008324118350290187895644392580185900422023040743350083200202144891712595471402185380078856954871044468154851334004092208748428592592574155469995205922127158225930665244860682596097298215654005404446724588313071692070290692143875711501357415401248319016351235393347010427130731843216720684941356122675092933184291623132918971856410860451185311270086796831097607566791439159851025744037197906153808204252940112938143327798905427927302563915708999024978314683625132617636091897557473392210168793698966975174802703015327533568598191120425021626863886084098071071415823327498730988755527462579205307429658656327197740062637981166246739461751565258413275192179381358366108535094697686544589924278076196605082261268261650040125824259048950115977737591659427655903687401961549491499290526220693583400375460463288291187702045304079704372699533723540466487200091300886788768158463608070771935919161415675342089674558909363773837167053224146170, 498977992663909869407579561270259766068086705644190097347955741063706397517662876704391341780864933067535770862348756689472214648051016645556761710200327742911412192602594679734838152536214411120450283407641864198719743660741713164029417732291840131140710259474739950914768859196369372735608686430671430657077897496487181242178703377473119597182528130690743845387161172792994037615644260053682633286019054675259147451846517939794210926540432812077041785247687557786459686716613883084725631765551540098836252383683403834859792411640785202504976546739230707684184628843391173379867407014246827789604661045710564932177518508116485454059271311414366235475352434576337594456853766044627844430524518680535583977285210798430734973416960447356703573806482333184880488438342053303777887974995761790989508665305267697843790119204702962034536312029416576278635513299810425415068825926564247257122997354736705181988781446993636543549153677070269920880842501160352856766503302531398679884959428629881075326795274021504695899315012611792572643156567371093710786831536191167868859155077805098781002463007801582742828710561630573967256191309678108053230100711653617894283828294133766197986457667195996627234944141852513038521816334790151182611706, 498977992663909869407579561270259766068086705644190097347480991310008483215510684270069643433030701923248987733421976636634209694585540193468962671434326390273582083930973166211014666643162120593413160701450863833454462036187296911531472197596568161427342627758845135284590445089101966287814062785343800464394034547937459661950550759057055434828233178965714367412520543170490548470286182042089010656996194222023805764516013564354675078763124964478542047659374674523518341430788486104345591666420186940583979823946548972920095270782568218018538856377720734130304404605463154803994456970504478661063965784372472587675921013505707909578275947170837748136607844588652584948818210089871956413779684064694351091964555047686153211489907308947773105058160160174184740909695696257512830966817878218110063162712998560756123533469206366206309136706366690360027228500959855013428108381613775497660344222759322879624222775336572513022671515472092438331730288152465688510732190236407429759722707973032173258381864786802832325046125558111344473985224062532232249904572844358509638387774198903499233235683732351676645829880848957038403524350329974107471613202181186329607927206097456174773806462442431291419866565169718346438054732222951173256442, 498977992663909869407579561270259766068086705644190097347955741063706397517674526609226973360389069129239570700218515952603194939684823596444651524190506966058613148628435648359392018104312196918992225727899154977040699274466474081605954904592077711880394717642313419879358500683205815390953869736686947530648983730107341802644836057671103153294389684473558783082658117596754748942039359247960161911346281813496040426339476941949483174102165739075460557661200106838663481320284373517990926308998478218365817541202051611302413867121115228845867373222993659003054670768179561730495957152749275276938161262074372808762013071204491317255358604581135919233624394942225009641345285157127372532803241610852460978459834211710391437846488885374806509268006032593550181434066774325792071400615814188044148277994382311135092640684127245503193629510965735781311969045485838101703009619468166739931492390833582688354597505607094371558165565395606141048123075220599642302756611364743317327278429775755927680140849285003141023235305330206968733833822515049763617920147128287032059488152531053770163847528048672557186214917309678236822363957882721877065805351453797789767571431485154125739027730651948150775830385235907263184654781039309132264698, 498977992663909855585233959705027514633829318003427484924157729308375796725547934025117650889656065713686047460710156719655667007149069038519503528523195762123570155781331068805655956585566207471664220850776612302144444410230291757162364736709616239523667914715200088396369878626312145725192070418331134481353285569641873293012068900473860369448144110718598430409308520690093485774058538128229130007406029945495016694568912400250613196465351593588527825819856708483382431659703972200723617825681837347800831058706176726426266995642507271539525404800522557307893165728062935887613353906875471731671329559508898534316348464929451379772501424688320574054486438523093668154938241857772525371309602554723379427011278658204659259811466579836406812146891821199442378425410853694066942765593542838334502520733864564987277916452402434744026994931498155113505520004755008972157854411613975961367943793992889578771558391679494791191233401982780298469816203793888607645040626610305831297750089902398185224482011860643018778225664107776535721450835949745823464241905642210630315481466795454238147608053578465800804339879382820026279155962140161041968347883321070726739689385652876308435172503531596926332970753888349705962284070733519553950970, 498977992663909855585233959705027514633829318003427512875648627694859522585993816576238674182277054562273070976823257541088071253360956401746781497708683203561699773606340544670507228337223392415144594569473530903523517910301425632597460995113869155957217379701697757919446603348579260605525095418607977099775064477632628863503782290981644314080006977559876900170337360970072745184985312958193091060338508193393113389920454805072390313868966356875768740050546855552245393928680347463320062930553544775122795412893273648981618943192377350750608742027018418479096730508265331743624216744257616360896791313873029127147990483718818050033829951601187334723525885482405466806928492972039596459823613422359148622992481616504344191974360032159034219756627782548003240993098907256611285551616272116141566822508892273803330864492490199247828858203099030215701327616988658316860314992871903048414573865306253236540512484440942324816682990421162856845122302055045819828010532999965705545017235622599783147794895365787743886755578716068026165282683046960242154711258554536171001258834841418295800386900018641919014752032940707883672192975842911121870387911333746117752002730009558938564778007359282079444420984800477323695856558691253872096506, 498977992663909855585155078372076606998719101238140395248950445741957615445655145556933537375057149754469992706914734878810741108973459238251437892555911764536042024135895211261706138689246728842211691023398079612302633684865991009864650050520224120790819360741801753451198363689811564635973798310545299062739703342767276357598588402879939043728022608523755074336510951889846152203425476125222170290076634059176903604838478019306995947080795800844419411889137148582974824585568437818231379709816893141034292869539974821984948369120888904223282047353705543485053262733182585083586708319693463532845214015893406917868509564998360095617544729387428382670754073276376230356206337727138452908115484612909224726439566536736915804273145970938942951209372478457599621806691353566573114319602015962360900165785392643023493219846736930463881899951837089030443848642248558838233169594764638953473446914229891047758248695973692762657500573902403371603755281322599718178119343119976132970606871955070406296251919727218053428832588406707152599629781899284734314964631814546760184494388487486314395653494282928735571261374132412457724682776254983487061761617908183811186267261217103160884320649991377735735356358914851749182837867795932382885114, 498977992663909855585233959705027514633829318003427498900140553378466616806852796470256827499645743740974850702164976788356361752804654428731566452154732533167656206209770094064450128711672592083006512908596603197720295891320737865588082499426820434235558313238104629206484631260381653631199477354133777440573079880936941252803307806535866770283942604561487848522041127949420348564264789816290716183763745240993446850769960584915059650634416676532311029145952465139439026502598100446154848397777084581158115774321673948354826097819648174052335779977466687587546078100110725081921192339448083080427566593070727723916479997452750004077053288103435013843586749302095784732203176018974737135937897086508160344232036123083185205854965581159012791900000213755324170116071308386812015289676591934217075301845502913067448486549629720210505261951530822888563584454075885225667661796011854226644368316297937872312210697355560983434498548885116588053269233271071337091436538814283291460255933323689524230462464930140056593060028267511423770772726209744134049144321325522472860831791485335633236822567877097755268576254386676129702785431936833889383569108639658496397860760460095416389161906878570717376527539517408258098688679028108168918266, 498977992663909855585207806535815379314260960290807284889816981868817330060701530764742578136119755983952065101572269752600370162975729433231460343423312397569511351888986681507029046709104474887947907225170622794225339577037986896014128664029147122997772596261064615153777384952083710997362332674721602742417486026930342119461251971122386390709793100227782396791686441628941499865293781951883006804563534312397962947296194075766412758759591636619389998901210653416251795163290393325902572778924256728781084934438328190193792144454507413506775142737068832940641120170242417645950848876180027245705098522538553426698470293923527713564181707370271693254761701643054941280337048461769657983431646905659568833992419522988956725167028727357739121830065906947642905016297881191485686032015244473591937696734405586410700202289459541318470584292455083573557886754771679752285614938909973544430016498312396860377304309495390754139159886481213791819742249426119470714263493943234666711277898130694977460784398088573651333516521315840593664087209871087349145539744101268486027860531063676581466763368405434897769324933575107605843771538992692475171342718578401419842751517353499978768689263882968371210990782493056414962033098100395813238010, 498977992663909855585207806535813844722723256829909844927337886205683340018841047088614910347594011882266468704196306891533854465289398497920246052642654715587457182495205028768889985494341832608024754560715696116983772418310871430322853787154884028507391875462297089595714089305582296595496767994871468222900278534305844890387120913567771358249935725875783431160944611462803476515684138320274479963385911886279416496397127548095933133535072222239604926188769536747529851832658986547643224598386778056554701977817680108307011170451098920577405946300587867294299778095767106626300452404483063769461562470427346965434852609593155263182703755234995320117785069938061449598331588499210411682992665710521706848179408710930077558626204886984636738204143066057175444337230082868641037242619775786864308550251516257589658887017717467570415935319477581965803940747158066139147782828533864880591895303980840061358585797479611691121242796918333790888617177680187721805477761894279592118658579083422884804077733929828452545189451113017559238440506589041237807158630299598635216137386396262444850430854859619201850760843219477186586860098680644743658803289673776003936069380000787716317590783180260159661089704236786948411111768443841873048826, 498977992663909855585260534699551082446727412421679308581865246972127070929598934274206764834956457229618887793754115748100928082498417889852093065889320502897190074735389324171713008481268374879065860363907786527157420484525568090130384435212827888144784662692701488486503514100253146530391751666805321064785616291607851446620151689293875626111684106160604164858927730790257908904100476871853685482432805768287843390198292809042930323471608306250544086268162309373371277247531426325002415465624697286084178615301558590958536326883060807561968337991328158012186944982324914360770744656205747840789303178826068079260640008298607419322578782861286894255175292925032682285885733671291386377775669600251079696078295491223297686554660993233027717645114789398920382979327502851114487479612496509205970438251766955062134386023125954064833432667333686774432518883953006869774765963944132863268248914895584980301664104517297163545528507418803755938824581460577649878373551767758677778933222482962311299191684523799928382084256225253241391794614543689682024511745039526837754297338049030416344136898406206448254805895342607102271721617397848159626091031342188114803196799056597387937148847288682326517759506936882140973865458217720176309498, 498977992663909855585207823837242571003851445693463394282598600750322138129168902724673712320877260807326545886536900742349764664928466798910264674981801479418890124397183167400707095797471636005745730891598881363411028708803787428556103387883325172678611779291795317696660283126735048722620601069459663104390517271955918241580236579312690952398594431404906658842860239686023766426522492095714224936150078329298462634099952883649880159315585731659402540910818408435364721250894125242197828651253564028494317427454935297110468942870100883436585280007072723708054811982312059360885004544980230563047139047006852813841858235640239035371616489919039245838568638386517274967635551515380152722530471827275005079275590333837693629989394447213177497682523960784318979469251878974426700133636186386345593269540918318242858496592131290142947498454365717895308760424668312015324378865845730044511726678224335396672237402007282571804940926564959802710658558875729983930142683524949605499514906571790135963862038597770692222409860875796768043142063477491617189287250467291597251173044178235607866014179894657273022154250839183999703829421780024558774207180510767709681247364395005628909291379030627034642228069204089479166134319502573978645754, 498977992663909855585207823837242571003851445693463394282916566658952222046973218295346169932757426661083222284352837030669067770573217923606525934906020602360287819724352912447789319175557407065178455173434017249665711232625572160485407835669937845455588598918405282930309056791487352470956026066683976203803482924644143372045217409946159600686429371503220392030605914473371652090833525664009949804573678238902751959252636001913569929978889009454731043676499591701954656225522833504608274566856328672702545519606885160562749545200983916547030730023443337696923489384608077064591813552790573543118200012083329383334165710462921582061939129497271661477784485365620074568659304517154155271342440440670380008639497285388131528300779155384113033170998263124045784062988813113487219876786754668547113820713549798146522361391360130547564466804643113753150408150057944446719622721574183732308395344114981737092382378570835984909174979482861112785527530207843685856064623363362280919054622195424432024389145979293480648591935122097997929265408506759564514262380807654340749071094026841110585050131398745822173350531807582828527814505641906210793520730348864430730101553010377035874012790397397577540450864646900995278414474526727607022842, 498977992663909855585207789234385118441595067966356295572076556802991206541549374138273874303654116844017286945713011226828227033983099848920580635291365973310589494953068222478205857287106395759260613030528243355172417510476544665035663672909723212504843678132210912811577821215266456137276837235087860609660961515405277254910117669110533884678481699580507023712702049163743202244953716513985284105315773975174824072432452166691877750778270183636680056028592563094854046588560100877612348991926604305608160274776213037210799111063531614474547996151379949500730700132629325905819502828798186682841412469140228729961638397081194976390305924447732855937992361808358892360268430130232964952462063676576904412220418294810624646437145340016415295672310712856405270359402374481089359309331315612474622383867987705662503852388810923485568156501930853720020159419331959682861191793485129955488121091787418334962076749873316094852527413147258954138461385206965417623130665237766479459501721521674249445257963305571907866372185435852809822021440242788078238856283095536072784721326287152631860348951356042194476175777472118735422424234165209979739554681386336779044694179294071272370802721874862887017432856154739823002056114999238257669370, 498977992663909855585207806535813844722723256829909844927337579585210132606443700466944700599558345080066214658892738238512871245831281985035008810893705169678111776316371219358027878278249413925166276175310164432610421589521686611817567513175536025686906442303890775479525502750819608714402680926755071484483495689993027625219722346368324988777102255886035681435531243171167837039594582282943198200110589159772517602814650699896491505856633207514751836939210507062833900823664275175929205222180292069815920215068058373026812870982647331247816368492159853580783711892102221413781423474544533931901627989172874073213365738085658987208436550122932370683776066530620219831008874298924064217141289086027701040726460999455544894084428904850460743855245704486871952996164949773477115132144844926382829646036404326499866505143121241471569475066875221739593357606616955621340249905908753563296034501562525826469304922319088452720562669165232433346821090584111129226693116847780204061821441246826335012257426666597921041200656681238689188310035678872974925307623019709357963038557439680267910582949484229347933850327237607456403135973068204056874276939164072472119634901574978910606085912541207269121772309985729858526891142863738962048250, 498977992663908666640105104466927144191046904794297306701630534993301279692409801439738773406951038309975330450047074236379649997695534516980243488001183412163799290909934254778018474817917329304466604627995902575022996814397110705260919481912298451899025429815360482652954974285474903681164216192462365984916714578011809813422271705148287485700556538844195510414957328811047088034110326937197120535122749732727352546242010840086676207028930010731164841460342501522302786394784353538314658497875438522005210296063872165531024059192708795467051534729740768672866556977821522208328304969036773953323736824364748630684326156035428273264439810900653466456765931177648063068244508085383734319913685303062523749410199332356204305880801553261141339674007706098014798243642874716872766739703151065453027072093974443894923821953472890234030045630697990761816586420534393034085343844791013555556425988848689771974077660916667916397262398535720129716545000856140614183013752035400207128546915630454073263660702832640337475469319423547579537856974937884818847558822186038825508084652603255796851280338524680736505028863701181730590811900575439604794317950932099316080507806366578076363376298860143138628003993174791213570965940554986309678330, 498977992663911044530283933610176977441501514447270573471162832738453249871069723222464453476930371175231968111244870155393657123524552558422811892030943056716439649286588413624499204756696806203106510080957244995913029601417948117281892772680251921776743674020382339332573421285749218973070031769490967790113363197179914432884669933196911963027554851697140543494527659905296469679997545045446748094652969523859937366120899119645255734877508046237478269653260995495347234983351644358155030096626586310409759478475614839189189916547325653995697056792653268401871559654577682004163463774268360258501458931311495848864043520081878181498762195794827505395509838990178894311334626468155301354882548510141793463092818730406727922365366840585814538640802741042411939893395008708684702163230372984029003598640801517050453144265816357957218020132897342910602219585327023472664455862001956400170255290743390950721215688828869231445660894486173565463217320871129450180716173348130828615975004159723526760863904622476558740545347292161186036435174891131318465305079130341937911772700008797988697424851978428622452331047917543946694816270544236706865487017958064240061915509766901046898357991987252377718325172857999316787039719575133975344378, 498977992663909855585233959705027514633829318003427498899983148908259302587134789174770005932777884143639557419998516553022345389739825951234916519467916363336795205554686580529919905039980110711180213213252056118902699861166282054506333484404569464570248197268247453105923693423924598537644351306629979156030212913118656549530364068149673197524914570087396881789471030087899842283628419111051314436551745259504155390986547931377552785292016818004434095472757756536822270347354617835005122884443080937285681981908048618683950526015021793811395948629971177491068304211070204854132851629093797947115101639432580956049087640903327099884433913581848168832815606862905592209539932225290450271657054501168016865190806868579044715907305372072558387736830529600979129918898048378587249476957053112591908169159774812670007177908805094689545761574277199678110128232753841721228499602129854314792870111547267685408864743001921363260424123615400707584991510486954230607954397175938080716896132002656770606267293149571370753748220144026373179878209147560503606052532709041097843812754753826392487488719855461240280926842138825468386420598586329318541583653065908205368470272086162267151336561433497910406150731085530510533878021876239456400634, 498977992663911044530362814943127885076611731212557691098335764445053071313572236580926920211508643189025629347949932133639972513011333167641628663938857910172675841522446411444780091085563895466729006685175189907142989659282961964565561166129679542511553971398051323858695100086715459407456192792212042729496754864409210735586125157972144915627683553691573933498029553079500482429832488382240683172941844581625735221964748942692257499688509129215579814023948070568787408979616765025647234942379546588287144049234803744830850968171670857037619156217580037183350230735873337295604464727658820905234038481879635535355266667196368794123741783660021047767159316623229621001909505774414481760613692682826174938481178526641186853943506463136899846025902438367928622791487316044915450477642549789292122065974823508243741958625124817997282552239118060970597583596483664880816193590127248956517108976310549250428508000429199825736860592192873274483484722861602865998117510815813534434787892506583488366052525948519102137401382018616306679957285481026782146611836239601317511097802718350007731188358742242848939076729453596335529129838397060115192379235063235967118447826415145510000214756960275695551941377580569067897800311595650570122490, 498977990808702523093377248935401185569754454360661849878496882785927449042596569270830920388918911214645773440276673539389084847180744003935447273522440833986695946348537000679439552085015392367366637123211957700772011637972284620810859324078789591606071549088202116086393007653370840311751003611143101084853133172690896687634446865772499085297054783757170952576621000010862537008634320543797290366986963656091270177003021086854481183155600186385004275394641642691860152479301261537202309667040622510131905849023574615484768064780246898780008116370682758309689173751885605941120428950558128001960070489234432486256159481526222288975371868697979182046862061936603563570476788077400445560719868715196000772171960815805112491767683266474914164004100771592179031389027563281823568090926819126541088522655662581011849736809640212199441656503711296321500960947101523656243998902570642802415573123743833209693158376586970646205450316199045522256685568332515439548328781672709487261298612080554237316889343520435996864286631855505272390031430929392445008430253764184957436661467441668864861794468190851789382646392931743480070485506958903219995774387017263002947748424740468316623568642854416036669387082024638999118767588984461040678138, 498977993584092692501155754385698445616907176612841774350366788987137355156321727434535158984878132410609437331390631647168583243348395043292155579073534130771912743587436897442285163843048849432073320204894509025708209715783047616601888513301103745838914818434717259777103026626567729683778888353669067962231688429136026833651710409936144372556338383954284091186605856984550909213660830838563614782930592601890214067826049497440080452751153188299473973584489971949535199314260825372433242148119228184054156475428711188996848133423794582039150172904029371104213007663804666479436350006835816116143008603247220466026006405975750883809426938492119097997416891133890377897210890454793471306429376595925042785945773455052938744941813905718617913753678609801498473884695114434025742896465879260224478571305502865186536787355053938878728025040689108809149912659426374714426574139017860628693253356623626932201666005791949309258647241144530957961823636202153769570156213263925222650230882079207384207836768790883437522184518003667506071860573798979117982784284096819133065784161873709988852829175996177326099027600323456501455726012493179312292251071141024636154232425484282082766556975084150738847517900272189954108582556472052237858042, 498977993584092692501155788988555898179163554339948873060890999813253025093603329875194394491011878083182879706118103734715086480290780694393101767469821588043015124453762769174043394970503897517571067902723992966187858015457714934532428757050882247283169637220605225254716830243086225299364678591387096939651240082546605587056398782468804087837510356065689878323988143615257520196876671560968005058302660704650706759810838189253325680900521313623821280297346848178828877456951452371524774756766643559447634858532418700107293363466438590785960895010986051445483140192458262743018787818853913140907414901918723290838255039576152805668229449113015671314040643333566101332809155169180252312528453504842958701780633130355725581337098609925651106275210925494582348503464500786868605482548565243080974380637939032719845772619816041527175617567335674088588668816448248092339354508465705609378595502624253966521899027620464945010902478068388643506417683591071493686894217560785897715010624396785696463130694313930428579807487158091101708599659152543063715375240958639939629538144586092717666990768270678180367744209048637219133092485101022306571017288936028358631070947824232041148239490774281426793899810186446594838809437897216794162426, 498977993584092692501155771687127171898035363600570662491918055398032021831659130603765553379677971431323555049673630910521487439290598195631267698101863096669528251699578013422833778925867655183419713972219654884232322532890436056224617113042721710967696572846135362200258106362577499103982042671133522107328972221967016080340751724477271827743001697907756678306613050056932542247656558987252219413690674817208819999380979097398559031339477966569266347517875084578653848307564065239637552187361519877402180513420650188490128004468468990918462235033965310746233709499967581818182922189866574705731062160347556580294195520928169856825770713086097619049017218364430540626389661722103016541795869051987747541567570802119246318595315281838896046585333472543291916138625773922843250426951505316124716738919264824308557938992492185552257896099374413431439227390132540432687706013540619662595168398636204374341402280375329829513476462810662177642019254315024610616504832816516770582951404656328652011048380579690483352399764719596802094678219883923886023366606705540520307100644629340447901305680977451243514315029650485124507289339249194409811089346062949569515533031886205778930144662180820045877075551151946224830739672026608839554298]
def wmat : Matrix := fun i j => (Int.ofNat (((packed.getD i 0) >>> (9*j)) % 512)) - 250
def price : Int := 1002
def literal (input : Nat) (i : Fin 26) : Bool :=
  if i.val<24 then input.testBit i.val else decide (i.val=25)
def positive (r : Nat) := literal (rowInput.getD r 0)
def negative (r : Nat) := literal (colInput.getD r 0)

def cap (v : Fin 26) : Bool :=
  let rs := rows.filter fun i => positive i v
  let cs := cols.filter fun j => !negative j v
  if rs.isEmpty || cs.isEmpty then true else
  if rs.length ≤ cs.length then rs.sublists.all fun a => decide (upper wmat a cs ≤ price)
  else cs.sublists.all fun b => decide (upper (tr wmat) b rs ≤ price)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caps : ∀ v : Fin 26, cap v = true := by decide +kernel

theorem literal_bound (v : Fin 26) (a b : List Nat)
    (ha : a.Sublist (rows.filter fun i => positive i v))
    (hb : b.Sublist (cols.filter fun j => !negative j v)) : rect wmat a b ≤ price := by
  have hc := caps v
  dsimp only [cap] at hc
  split at hc
  · rename_i h
    rcases Bool.or_eq_true_iff.mp h with h|h
    · rw [List.isEmpty_iff.mp h] at ha
      have e : a=[] := List.sublist_nil.mp ha
      rw [e,transpose];simp [rect,price]
    · rw [List.isEmpty_iff.mp h] at hb
      have e : b=[] := List.sublist_nil.mp hb
      rw [e];simp [rect,price]
  · split at hc
    · exact (rect_le_upper _ _ hb).trans (decide_eq_true_iff.mp (List.all_eq_true.mp hc _ (List.mem_sublists.mpr ha)))
    · rw [transpose]
      exact (rect_le_upper _ _ ha).trans (decide_eq_true_iff.mp (List.all_eq_true.mp hc _ (List.mem_sublists.mpr hb)))

theorem total : rect wmat rows cols = 52888 := by decide +kernel

def Formula.leaves : Formula → Nat
  | .var _ => 1
  | .conj a b | .disj a b => a.leaves+b.leaves

theorem cost_eq (e : Formula) : e.cost (fun _ => price) = price*(e.leaves:Int) := by
  induction e with
  | var _ => simp [Formula.cost,Formula.leaves]
  | conj a b ih jh | disj a b ih jh => simp [Formula.cost,Formula.leaves,ih,jh,mul_add]

def fedges : List (Fin 24 × Fin 24) := [(0,12), (0,16), (0,22), (1,13), (1,17), (1,23), (2,12), (2,13), (2,14), (2,18), (3,14), (3,15), (3,19), (4,13), (4,15), (4,16), (4,20), (5,14), (5,16), (5,17), (5,21), (6,15), (6,17), (6,18), (6,22), (7,16), (7,18), (7,19), (7,23), (8,12), (8,17), (8,19), (8,20), (9,18), (9,20), (9,21), (10,13), (10,19), (10,21), (10,22), (11,14), (11,20), (11,22), (11,23)]
def graph (x : Fin 24 → Bool) := fedges.any fun p => x p.1 && x p.2
def assignment (r : Nat) (i : Fin 24) := r.testBit i.val
theorem graph_iff (x : Fin 24 → Bool) : graph x = true ↔ GraphClean9796.target x := by
  have edges_eq : GraphClean9796.edges = fedges.map (fun p => (p.1.val,p.2.val)) := rfl
  simp only [graph,List.any_eq_true,Bool.and_eq_true_iff,GraphClean9796.target,edges_eq,List.mem_map]
  constructor
  · rintro ⟨p,hp,ha,hb⟩
    exact ⟨p.1,p.2,⟨p,hp,rfl⟩,ha,hb⟩
  · rintro ⟨a,b,⟨p,hp,he⟩,ha,hb⟩
    have h1 : p.1=a := Fin.ext (congrArg Prod.fst he)
    have h2 : p.2=b := Fin.ext (congrArg Prod.snd he)
    exact ⟨p,hp,h1.symm ▸ ha,h2.symm ▸ hb⟩
theorem trueRows : ∀ r ∈ rowInput, graph (assignment r)=true := by decide +kernel
theorem falseCols : ∀ r ∈ colInput, graph (assignment r)=false := by decide +kernel
theorem getD_in {xs : List Nat} {i : Nat} (hi : i < xs.length) : xs.getD i 0 ∈ xs := by
  simp [List.getD_eq_getElem?_getD,hi]

theorem lower (e : Formula) (ok : ∀ r, e.eval (literal r)=graph (assignment r)) :
    53 ≤ e.leaves := by
  have h := formula_bound wmat rows cols positive negative (fun _ => price) literal_bound e
    (List.Sublist.refl _) (List.Sublist.refl _)
    (fun i hi => (ok _).trans (trueRows _ (getD_in (List.mem_range.mp hi))))
    (fun j hj => (ok _).trans (falseCols _ (getD_in (List.mem_range.mp hj))))
  rw [total,cost_eq] at h
  unfold price at h
  omega
end GraphFormula9796

namespace GraphFormula9796
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def base (x : Fin 24 → Bool) (i : Fin 26) := if h : i.val<24 then x ⟨i.val,h⟩ else decide (i.val=25)
def init : List Formula := List.ofFn fun i : Fin 24 => Formula.var ⟨i.val,by omega⟩
def readF (ws : List Formula) (j : Nat) := ws.getD j (.var 24)
def two (f : Formula → Formula → Formula) (k : Fin 26) (ws : List Formula) : List Nat → Formula
  | [] => .var k
  | [a] => readF ws a
  | a::b::_ => f (readF ws a) (readF ws b)
def gateF (ws : List Formula) (g : Gate) : Formula :=
  match g.op with
  | .and => two .conj 25 ws g.inputs
  | .or => two .disj 24 ws g.inputs
  | _ => .var 24
def stepF (ws : List Formula) (g : Gate) := ws++[gateF ws g]
def expand (c : Circuit) := readF (c.gates.foldl stepF init) c.output
def realStep (xs : List Bool) (g : Gate) := xs++[g.op.eval (g.inputs.map fun i => xs.getD i false)]
theorem read_eval (x : Fin 24 → Bool) (ws : List Formula) (j : Nat) :
    (readF ws j).eval (base x)=(ws.map (fun f => f.eval (base x))).getD j false := by
  simp only [readF,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[j]? <;> rfl
theorem gate_eval (x : Fin 24 → Bool) (ws : List Formula) (g : Gate)
    (h : (g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2) :
    (gateF ws g).eval (base x)=g.op.eval (g.inputs.map fun i => (ws.map (fun f => f.eval (base x))).getD i false) := by
  rcases g with ⟨op,ls⟩
  rcases h with ⟨hp,hl⟩
  change op=.and ∨ op=.or at hp
  change ls.length≤2 at hl
  rcases hp with rfl|rfl <;> rcases ls with _|⟨a,_|⟨b,_|⟨c,rest⟩⟩⟩ <;>
    simp_all [gateF,two,Formula.eval,base,GateOp.eval,read_eval]
theorem fold_eval (x : Fin 24 → Bool) (gs : List Gate)
    (h : ∀ g ∈ gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2) (ws : List Formula) :
    (gs.foldl stepF ws).map (fun f => f.eval (base x))=gs.foldl realStep (ws.map (fun f => f.eval (base x))) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,List.foldl_cons, ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]
    simp [stepF,realStep,gate_eval x ws g (h g List.mem_cons_self)]
theorem expand_eval (C : Circuit) (hm : Monotone2 C) (x : Fin 24 → Bool) :
    (expand C).eval (base x) = C.eval (List.ofFn x) := by
  rw [expand,read_eval,fold_eval _ _ (fun g hg => hm g hg)]
  have eq : init.map (fun f => f.eval (base x))=List.ofFn x := by
    rw [init,← List.ofFn_comp']
    rfl
  rw [eq]
  rfl
theorem base_assignment (r : Nat) : base (assignment r) = literal r := by
  funext i
  by_cases h : i.val<24 <;> simp [base,assignment,literal,h]
theorem expanded_lower (C : Circuit) (hm : Monotone2 C) (hc : GraphClean9796.correct C) :
    53 ≤ (expand C).leaves := by
  apply lower
  intro r
  rw [← base_assignment,expand_eval _ hm]
  exact Bool.eq_iff_iff.mpr ((hc _).trans (graph_iff _).symm)

def starCircuit : Circuit := ⟨[⟨.or, [16,22]⟩, ⟨.or, [12,24]⟩, ⟨.and, [0,25]⟩, ⟨.or, [17,23]⟩, ⟨.or, [13,27]⟩, ⟨.and, [1,28]⟩, ⟨.or, [14,18]⟩, ⟨.or, [13,30]⟩, ⟨.or, [12,31]⟩, ⟨.and, [2,32]⟩, ⟨.or, [15,19]⟩, ⟨.or, [14,34]⟩, ⟨.and, [3,35]⟩, ⟨.or, [16,20]⟩, ⟨.or, [15,37]⟩, ⟨.or, [13,38]⟩, ⟨.and, [4,39]⟩, ⟨.or, [17,21]⟩, ⟨.or, [16,41]⟩, ⟨.or, [14,42]⟩, ⟨.and, [5,43]⟩, ⟨.or, [18,22]⟩, ⟨.or, [17,45]⟩, ⟨.or, [15,46]⟩, ⟨.and, [6,47]⟩, ⟨.or, [19,23]⟩, ⟨.or, [18,49]⟩, ⟨.or, [16,50]⟩, ⟨.and, [7,51]⟩, ⟨.or, [19,20]⟩, ⟨.or, [17,53]⟩, ⟨.or, [12,54]⟩, ⟨.and, [8,55]⟩, ⟨.or, [20,21]⟩, ⟨.or, [18,57]⟩, ⟨.and, [9,58]⟩, ⟨.or, [21,22]⟩, ⟨.or, [19,60]⟩, ⟨.or, [13,61]⟩, ⟨.and, [10,62]⟩, ⟨.or, [22,23]⟩, ⟨.or, [20,64]⟩, ⟨.or, [14,65]⟩, ⟨.and, [11,66]⟩, ⟨.or, [63,67]⟩, ⟨.or, [59,68]⟩, ⟨.or, [56,69]⟩, ⟨.or, [52,70]⟩, ⟨.or, [48,71]⟩, ⟨.or, [44,72]⟩, ⟨.or, [40,73]⟩, ⟨.or, [36,74]⟩, ⟨.or, [33,75]⟩, ⟨.or, [29,76]⟩, ⟨.or, [26,77]⟩], 78⟩
def starTree : Formula := (.disj ((.conj (.var 0) ((.disj (.var 12) ((.disj (.var 16) (.var 22))))))) ((.disj ((.conj (.var 1) ((.disj (.var 13) ((.disj (.var 17) (.var 23))))))) ((.disj ((.conj (.var 2) ((.disj (.var 12) ((.disj (.var 13) ((.disj (.var 14) (.var 18))))))))) ((.disj ((.conj (.var 3) ((.disj (.var 14) ((.disj (.var 15) (.var 19))))))) ((.disj ((.conj (.var 4) ((.disj (.var 13) ((.disj (.var 15) ((.disj (.var 16) (.var 20))))))))) ((.disj ((.conj (.var 5) ((.disj (.var 14) ((.disj (.var 16) ((.disj (.var 17) (.var 21))))))))) ((.disj ((.conj (.var 6) ((.disj (.var 15) ((.disj (.var 17) ((.disj (.var 18) (.var 22))))))))) ((.disj ((.conj (.var 7) ((.disj (.var 16) ((.disj (.var 18) ((.disj (.var 19) (.var 23))))))))) ((.disj ((.conj (.var 8) ((.disj (.var 12) ((.disj (.var 17) ((.disj (.var 19) (.var 20))))))))) ((.disj ((.conj (.var 9) ((.disj (.var 18) ((.disj (.var 20) (.var 21))))))) ((.disj ((.conj (.var 10) ((.disj (.var 13) ((.disj (.var 19) ((.disj (.var 21) (.var 22))))))))) ((.conj (.var 11) ((.disj (.var 14) ((.disj (.var 20) ((.disj (.var 22) (.var 23))))))))))))))))))))))))))))))
def valid (g : Gate) : Bool :=
  match g.op with
  | .and | .or => decide (g.inputs.length≤2)
  | _ => false
theorem star_mono : Monotone2 starCircuit := by
  have h : starCircuit.gates.all valid=true := by decide +kernel
  intro g hg
  have p := List.all_eq_true.mp h g hg
  cases e : g.op <;> simp_all [valid]
theorem star_size : starCircuit.size = 55 := rfl
theorem star_expands : expand starCircuit = starTree := by rfl
theorem star_eval (x : Fin 24 → Bool) : starTree.eval (base x)=graph x := by
  simp [starTree,Formula.eval,base,graph,fedges,List.any_cons,Bool.and_or_distrib_left,Bool.or_assoc]
theorem star_correct : GraphClean9796.correct starCircuit := by
  intro x
  rw [← expand_eval _ star_mono,star_expands,star_eval,graph_iff]
end GraphFormula9796

namespace GraphFormula9796
open GraphRows9796 GraphClean9796 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def cleanCheck (w : Word) : Bool := (List.finRange 232).all fun k => !(w.getLsbD (rneg k))
def gateCheck (w : List Word) (g : Gate) : Bool :=
  match g.op with
  | .and => cleanCheck (gateWord g w)
  | _ => true
def starCheck (w : List Word) : List Gate → Bool
  | [] => true
  | g::gs => gateCheck w g && starCheck (tick w g) gs

theorem check_sound (w : List Word) (gs : List Gate) (checked : starCheck w gs=true) : permitted w gs := by
  induction gs generalizing w with
  | nil => trivial
  | cons g gs ih =>
    obtain ⟨hc,tail⟩ := Bool.and_eq_true_iff.mp checked
    refine ⟨?_,ih (tick w g) tail⟩
    intro i j op ins
    apply Or.inr;apply Or.inr;apply Or.inr
    have cc : cleanCheck (gateWord g w)=true := by simpa [gateCheck,op] using hc
    have ww : gateWord g w=w.getD i 0 &&& w.getD j 0 := by simp [gateWord,op,ins,GraphClean9796.and_ones]
    rw [←ww]
    intro k
    simpa using List.all_eq_true.mp cc k (List.mem_finRange k)

theorem optimum_in_class : permitted words starCircuit.gates ∧ starCircuit.size=55 ∧ correct starCircuit ∧
    ∀ C, Monotone2 C → correct C → permitted words C.gates → 55≤C.size := by
  exact ⟨check_sound _ _ (by decide +kernel),star_size,star_correct,actual_lower⟩

theorem star_leaves : starTree.leaves=56 := by decide +kernel
end GraphFormula9796

namespace GraphElimination9796
open PEqualNP.Outside.L_meta_7398_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
private theorem supportBound (A : List (Fin 24)) (E : List (Fin 24 × Fin 24)) (k : Nat)
    (enough : k+1 ≤ (Finset.univ.filter (fun i => depCheck A E i=true)).card) :
    ∀ s, HasCircuitSize 24 (gfn A E) s → k ≤ s := by
  intro s hs
  have h := q117 24 (gfn A E) (Finset.univ.filter (fun i => depCheck A E i=true)) (fun i hi => q154 A E i (Finset.mem_filter.mp hi).2) s hs
  omega
private def a0 : List (Fin 24) := []
private def e0 : List (Fin 24 × Fin 24) := [(11, 22), (11, 23)]
private theorem h0 : ∀ s, HasCircuitSize 24 (gfn a0 e0) s → 2 ≤ s := by
  exact supportBound _ _ _ (by decide +kernel)
private def a1 : List (Fin 24) := [22]
private def e1 : List (Fin 24 × Fin 24) := [(11, 23)]
private theorem h1 : ∀ s, HasCircuitSize 24 (gfn a1 e1) s → 2 ≤ s := by
  exact supportBound _ _ _ (by decide +kernel)
private def a2 : List (Fin 24) := []
private def e2 : List (Fin 24 × Fin 24) := [(10, 22), (11, 22), (11, 23)]
private theorem h2 : ∀ s, HasCircuitSize 24 (gfn a2 e2) s → 4 ≤ s := by
  intro s hs
  exact q155 (n:=23) a2 e2 10 a0 e0 a1 e1 2 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 2≤2) h0) (q216 (by decide : 2≤2) h1) s hs
private def a3 : List (Fin 24) := []
private def e3 : List (Fin 24 × Fin 24) := [(6, 22), (10, 22), (11, 22), (11, 23)]
private theorem h3 : ∀ s, HasCircuitSize 24 (gfn a3 e3) s → 5 ≤ s := by
  intro s hs
  exact q190 (n:=23) a3 e3 6 a2 e2 4 (by decide) rfl rfl (by decide) h2 s hs
private def a4 : List (Fin 24) := []
private def e4 : List (Fin 24 × Fin 24) := [(6, 22), (11, 22), (11, 23)]
private theorem h4 : ∀ s, HasCircuitSize 24 (gfn a4 e4) s → 4 ≤ s := by
  intro s hs
  exact q155 (n:=23) a4 e4 6 a0 e0 a1 e1 2 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 2≤2) h0) (q216 (by decide : 2≤2) h1) s hs
private def a5 : List (Fin 24) := [10]
private def e5 : List (Fin 24 × Fin 24) := [(6, 22), (11, 22), (11, 23)]
private theorem h5 : ∀ s, HasCircuitSize 24 (gfn a5 e5) s → 5 ≤ s := by
  intro s hs
  exact q190 (n:=23) a5 e5 10 a4 e4 4 (by decide) rfl rfl (by decide) h4 s hs
private def a6 : List (Fin 24) := []
private def e6 : List (Fin 24 × Fin 24) := [(6, 22), (10, 21), (10, 22), (11, 22), (11, 23)]
private theorem h6 : ∀ s, HasCircuitSize 24 (gfn a6 e6) s → 7 ≤ s := by
  intro s hs
  exact q155 (n:=23) a6 e6 21 a3 e3 a5 e5 5 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 5≤5) h3) (q216 (by decide : 5≤5) h5) s hs
private def a7 : List (Fin 24) := []
private def e7 : List (Fin 24 × Fin 24) := [(6, 22), (10, 21), (10, 22), (11, 20), (11, 22), (11, 23)]
private theorem h7 : ∀ s, HasCircuitSize 24 (gfn a7 e7) s → 8 ≤ s := by
  intro s hs
  exact q190 (n:=23) a7 e7 20 a6 e6 7 (by decide) rfl rfl (by decide) h6 s hs
private def a8 : List (Fin 24) := []
private def e8 : List (Fin 24 × Fin 24) := [(6, 22), (10, 19), (10, 21), (10, 22), (11, 20), (11, 22), (11, 23)]
private theorem h8 : ∀ s, HasCircuitSize 24 (gfn a8 e8) s → 9 ≤ s := by
  intro s hs
  exact q190 (n:=23) a8 e8 19 a7 e7 8 (by decide) rfl rfl (by decide) h7 s hs
private def a9 : List (Fin 24) := []
private def e9 : List (Fin 24 × Fin 24) := [(6, 18), (6, 22), (10, 19), (10, 21), (10, 22), (11, 20), (11, 22), (11, 23)]
private theorem h9 : ∀ s, HasCircuitSize 24 (gfn a9 e9) s → 10 ≤ s := by
  intro s hs
  exact q190 (n:=23) a9 e9 18 a8 e8 9 (by decide) rfl rfl (by decide) h8 s hs
private def a10 : List (Fin 24) := []
private def e10 : List (Fin 24 × Fin 24) := [(6, 17), (6, 18), (6, 22), (10, 19), (10, 21), (10, 22), (11, 20), (11, 22), (11, 23)]
private theorem h10 : ∀ s, HasCircuitSize 24 (gfn a10 e10) s → 11 ≤ s := by
  intro s hs
  exact q190 (n:=23) a10 e10 17 a9 e9 10 (by decide) rfl rfl (by decide) h9 s hs
private def a11 : List (Fin 24) := []
private def e11 : List (Fin 24 × Fin 24) := [(10, 21), (10, 22)]
private theorem h11 : ∀ s, HasCircuitSize 24 (gfn a11 e11) s → 2 ≤ s := by
  exact supportBound _ _ _ (by decide +kernel)
private def a12 : List (Fin 24) := [22]
private def e12 : List (Fin 24 × Fin 24) := [(10, 21)]
private theorem h12 : ∀ s, HasCircuitSize 24 (gfn a12 e12) s → 2 ≤ s := by
  exact supportBound _ _ _ (by decide +kernel)
private def a13 : List (Fin 24) := []
private def e13 : List (Fin 24 × Fin 24) := [(10, 21), (10, 22), (11, 22)]
private theorem h13 : ∀ s, HasCircuitSize 24 (gfn a13 e13) s → 4 ≤ s := by
  intro s hs
  exact q155 (n:=23) a13 e13 11 a11 e11 a12 e12 2 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 2≤2) h11) (q216 (by decide : 2≤2) h12) s hs
private def a14 : List (Fin 24) := []
private def e14 : List (Fin 24 × Fin 24) := [(6, 22), (10, 21), (10, 22), (11, 22)]
private theorem h14 : ∀ s, HasCircuitSize 24 (gfn a14 e14) s → 5 ≤ s := by
  intro s hs
  exact q190 (n:=23) a14 e14 6 a13 e13 4 (by decide) rfl rfl (by decide) h13 s hs
private def a15 : List (Fin 24) := []
private def e15 : List (Fin 24 × Fin 24) := [(6, 22), (10, 21), (10, 22)]
private theorem h15 : ∀ s, HasCircuitSize 24 (gfn a15 e15) s → 4 ≤ s := by
  intro s hs
  exact q155 (n:=23) a15 e15 6 a11 e11 a12 e12 2 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 2≤2) h11) (q216 (by decide : 2≤2) h12) s hs
private def a16 : List (Fin 24) := [11]
private def e16 : List (Fin 24 × Fin 24) := [(6, 22), (10, 21), (10, 22)]
private theorem h16 : ∀ s, HasCircuitSize 24 (gfn a16 e16) s → 5 ≤ s := by
  intro s hs
  exact q190 (n:=23) a16 e16 11 a15 e15 4 (by decide) rfl rfl (by decide) h15 s hs
private def a17 : List (Fin 24) := []
private def e17 : List (Fin 24 × Fin 24) := [(6, 22), (10, 21), (10, 22), (11, 20), (11, 22)]
private theorem h17 : ∀ s, HasCircuitSize 24 (gfn a17 e17) s → 7 ≤ s := by
  intro s hs
  exact q155 (n:=23) a17 e17 20 a14 e14 a16 e16 5 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 5≤5) h14) (q216 (by decide : 5≤5) h16) s hs
private def a18 : List (Fin 24) := []
private def e18 : List (Fin 24 × Fin 24) := [(6, 17), (6, 22), (10, 21), (10, 22), (11, 20), (11, 22)]
private theorem h18 : ∀ s, HasCircuitSize 24 (gfn a18 e18) s → 8 ≤ s := by
  intro s hs
  exact q190 (n:=23) a18 e18 17 a17 e17 7 (by decide) rfl rfl (by decide) h17 s hs
private def a19 : List (Fin 24) := [23]
private def e19 : List (Fin 24 × Fin 24) := [(6, 17), (6, 22), (10, 21), (10, 22), (11, 20), (11, 22)]
private theorem h19 : ∀ s, HasCircuitSize 24 (gfn a19 e19) s → 9 ≤ s := by
  intro s hs
  exact q190 (n:=23) a19 e19 23 a18 e18 8 (by decide) rfl rfl (by decide) h18 s hs
private def a20 : List (Fin 24) := [19, 23]
private def e20 : List (Fin 24 × Fin 24) := [(6, 17), (6, 22), (10, 21), (10, 22), (11, 20), (11, 22)]
private theorem h20 : ∀ s, HasCircuitSize 24 (gfn a20 e20) s → 10 ≤ s := by
  intro s hs
  exact q190 (n:=23) a20 e20 19 a19 e19 9 (by decide) rfl rfl (by decide) h19 s hs
private def a21 : List (Fin 24) := [18, 19, 23]
private def e21 : List (Fin 24 × Fin 24) := [(6, 17), (6, 22), (10, 21), (10, 22), (11, 20), (11, 22)]
private theorem h21 : ∀ s, HasCircuitSize 24 (gfn a21 e21) s → 11 ≤ s := by
  intro s hs
  exact q190 (n:=23) a21 e21 18 a20 e20 10 (by decide) rfl rfl (by decide) h20 s hs
private def a22 : List (Fin 24) := []
private def e22 : List (Fin 24 × Fin 24) := [(6, 17), (6, 18), (6, 22), (7, 18), (7, 19), (7, 23), (10, 19), (10, 21), (10, 22), (11, 20), (11, 22), (11, 23)]
private theorem h22 : ∀ s, HasCircuitSize 24 (gfn a22 e22) s → 13 ≤ s := by
  intro s hs
  exact q155 (n:=23) a22 e22 7 a10 e10 a21 e21 11 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 11≤11) h10) (q216 (by decide : 11≤11) h21) s hs
private def a23 : List (Fin 24) := []
private def e23 : List (Fin 24 × Fin 24) := [(6, 17), (6, 18), (6, 22), (7, 16), (7, 18), (7, 19), (7, 23), (10, 19), (10, 21), (10, 22), (11, 20), (11, 22), (11, 23)]
private theorem h23 : ∀ s, HasCircuitSize 24 (gfn a23 e23) s → 14 ≤ s := by
  intro s hs
  exact q190 (n:=23) a23 e23 16 a22 e22 13 (by decide) rfl rfl (by decide) h22 s hs
private def a24 : List (Fin 24) := []
private def e24 : List (Fin 24 × Fin 24) := [(6, 15), (6, 17), (6, 18), (6, 22), (7, 16), (7, 18), (7, 19), (7, 23), (10, 19), (10, 21), (10, 22), (11, 20), (11, 22), (11, 23)]
private theorem h24 : ∀ s, HasCircuitSize 24 (gfn a24 e24) s → 15 ≤ s := by
  intro s hs
  exact q190 (n:=23) a24 e24 15 a23 e23 14 (by decide) rfl rfl (by decide) h23 s hs
private def a25 : List (Fin 24) := []
private def e25 : List (Fin 24 × Fin 24) := [(6, 15), (6, 17), (6, 18), (6, 22), (7, 16), (7, 18), (7, 19), (7, 23), (10, 19), (10, 21), (10, 22), (11, 14), (11, 20), (11, 22), (11, 23)]
private theorem h25 : ∀ s, HasCircuitSize 24 (gfn a25 e25) s → 16 ≤ s := by
  intro s hs
  exact q190 (n:=23) a25 e25 14 a24 e24 15 (by decide) rfl rfl (by decide) h24 s hs
private def a26 : List (Fin 24) := []
private def e26 : List (Fin 24 × Fin 24) := [(6, 15), (6, 17), (6, 18), (6, 22), (7, 16), (7, 18), (7, 19), (7, 23), (10, 13), (10, 19), (10, 21), (10, 22), (11, 14), (11, 20), (11, 22), (11, 23)]
private theorem h26 : ∀ s, HasCircuitSize 24 (gfn a26 e26) s → 17 ≤ s := by
  intro s hs
  exact q190 (n:=23) a26 e26 13 a25 e25 16 (by decide) rfl rfl (by decide) h25 s hs
private def a27 : List (Fin 24) := []
private def e27 : List (Fin 24 × Fin 24) := [(10, 21), (10, 22), (11, 22), (11, 23)]
private theorem h27 : ∀ s, HasCircuitSize 24 (gfn a27 e27) s → 5 ≤ s := by
  intro s hs
  exact q190 (n:=23) a27 e27 21 a2 e2 4 (by decide) rfl rfl (by decide) h2 s hs
private def a28 : List (Fin 24) := [23]
private def e28 : List (Fin 24 × Fin 24) := [(10, 21), (10, 22), (11, 22)]
private theorem h28 : ∀ s, HasCircuitSize 24 (gfn a28 e28) s → 5 ≤ s := by
  intro s hs
  exact q190 (n:=23) a28 e28 23 a13 e13 4 (by decide) rfl rfl (by decide) h13 s hs
private def a29 : List (Fin 24) := []
private def e29 : List (Fin 24 × Fin 24) := [(7, 23), (10, 21), (10, 22), (11, 22), (11, 23)]
private theorem h29 : ∀ s, HasCircuitSize 24 (gfn a29 e29) s → 7 ≤ s := by
  intro s hs
  exact q155 (n:=23) a29 e29 7 a27 e27 a28 e28 5 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 5≤5) h27) (q216 (by decide : 5≤5) h28) s hs
private def a30 : List (Fin 24) := []
private def e30 : List (Fin 24 × Fin 24) := [(7, 18), (7, 23), (10, 21), (10, 22), (11, 22), (11, 23)]
private theorem h30 : ∀ s, HasCircuitSize 24 (gfn a30 e30) s → 8 ≤ s := by
  intro s hs
  exact q190 (n:=23) a30 e30 18 a29 e29 7 (by decide) rfl rfl (by decide) h29 s hs
private def a31 : List (Fin 24) := []
private def e31 : List (Fin 24 × Fin 24) := [(6, 18), (6, 22), (7, 18), (7, 23), (10, 21), (10, 22), (11, 22), (11, 23)]
private theorem h31 : ∀ s, HasCircuitSize 24 (gfn a31 e31) s → 9 ≤ s := by
  intro s hs
  exact q190 (n:=23) a31 e31 6 a30 e30 8 (by decide) rfl rfl (by decide) h30 s hs
private def a32 : List (Fin 24) := []
private def e32 : List (Fin 24 × Fin 24) := [(6, 18), (6, 22), (10, 21), (10, 22), (11, 22), (11, 23)]
private theorem h32 : ∀ s, HasCircuitSize 24 (gfn a32 e32) s → 8 ≤ s := by
  intro s hs
  exact q190 (n:=23) a32 e32 18 a6 e6 7 (by decide) rfl rfl (by decide) h6 s hs
private def a33 : List (Fin 24) := [7]
private def e33 : List (Fin 24 × Fin 24) := [(6, 18), (6, 22), (10, 21), (10, 22), (11, 22), (11, 23)]
private theorem h33 : ∀ s, HasCircuitSize 24 (gfn a33 e33) s → 9 ≤ s := by
  intro s hs
  exact q190 (n:=23) a33 e33 7 a32 e32 8 (by decide) rfl rfl (by decide) h32 s hs
private def a34 : List (Fin 24) := []
private def e34 : List (Fin 24 × Fin 24) := [(6, 18), (6, 22), (7, 16), (7, 18), (7, 23), (10, 21), (10, 22), (11, 22), (11, 23)]
private theorem h34 : ∀ s, HasCircuitSize 24 (gfn a34 e34) s → 11 ≤ s := by
  intro s hs
  exact q155 (n:=23) a34 e34 16 a31 e31 a33 e33 9 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 9≤9) h31) (q216 (by decide : 9≤9) h33) s hs
private def a35 : List (Fin 24) := []
private def e35 : List (Fin 24 × Fin 24) := [(6, 15), (6, 18), (6, 22), (7, 16), (7, 18), (7, 23), (10, 21), (10, 22), (11, 22), (11, 23)]
private theorem h35 : ∀ s, HasCircuitSize 24 (gfn a35 e35) s → 12 ≤ s := by
  intro s hs
  exact q190 (n:=23) a35 e35 15 a34 e34 11 (by decide) rfl rfl (by decide) h34 s hs
private def a36 : List (Fin 24) := []
private def e36 : List (Fin 24 × Fin 24) := [(6, 15), (6, 18), (6, 22), (7, 16), (7, 18), (7, 23), (10, 21), (10, 22), (11, 14), (11, 22), (11, 23)]
private theorem h36 : ∀ s, HasCircuitSize 24 (gfn a36 e36) s → 13 ≤ s := by
  intro s hs
  exact q190 (n:=23) a36 e36 14 a35 e35 12 (by decide) rfl rfl (by decide) h35 s hs
private def a37 : List (Fin 24) := []
private def e37 : List (Fin 24 × Fin 24) := [(6, 15), (6, 18), (6, 22), (7, 16), (7, 18), (7, 23), (10, 13), (10, 21), (10, 22), (11, 14), (11, 22), (11, 23)]
private theorem h37 : ∀ s, HasCircuitSize 24 (gfn a37 e37) s → 14 ≤ s := by
  intro s hs
  exact q190 (n:=23) a37 e37 13 a36 e36 13 (by decide) rfl rfl (by decide) h36 s hs
private def a38 : List (Fin 24) := [20]
private def e38 : List (Fin 24 × Fin 24) := [(6, 15), (6, 18), (6, 22), (7, 16), (7, 18), (7, 23), (10, 13), (10, 21), (10, 22), (11, 14), (11, 22), (11, 23)]
private theorem h38 : ∀ s, HasCircuitSize 24 (gfn a38 e38) s → 15 ≤ s := by
  intro s hs
  exact q190 (n:=23) a38 e38 20 a37 e37 14 (by decide) rfl rfl (by decide) h37 s hs
private def a39 : List (Fin 24) := [19, 20]
private def e39 : List (Fin 24 × Fin 24) := [(6, 15), (6, 18), (6, 22), (7, 16), (7, 18), (7, 23), (10, 13), (10, 21), (10, 22), (11, 14), (11, 22), (11, 23)]
private theorem h39 : ∀ s, HasCircuitSize 24 (gfn a39 e39) s → 16 ≤ s := by
  intro s hs
  exact q190 (n:=23) a39 e39 19 a38 e38 15 (by decide) rfl rfl (by decide) h38 s hs
private def a40 : List (Fin 24) := [17, 19, 20]
private def e40 : List (Fin 24 × Fin 24) := [(6, 15), (6, 18), (6, 22), (7, 16), (7, 18), (7, 23), (10, 13), (10, 21), (10, 22), (11, 14), (11, 22), (11, 23)]
private theorem h40 : ∀ s, HasCircuitSize 24 (gfn a40 e40) s → 17 ≤ s := by
  intro s hs
  exact q190 (n:=23) a40 e40 17 a39 e39 16 (by decide) rfl rfl (by decide) h39 s hs
private def a41 : List (Fin 24) := []
private def e41 : List (Fin 24 × Fin 24) := [(6, 15), (6, 17), (6, 18), (6, 22), (7, 16), (7, 18), (7, 19), (7, 23), (8, 17), (8, 19), (8, 20), (10, 13), (10, 19), (10, 21), (10, 22), (11, 14), (11, 20), (11, 22), (11, 23)]
private theorem h41 : ∀ s, HasCircuitSize 24 (gfn a41 e41) s → 19 ≤ s := by
  intro s hs
  exact q155 (n:=23) a41 e41 8 a26 e26 a40 e40 17 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 17≤17) h26) (q216 (by decide : 17≤17) h40) s hs
private def a42 : List (Fin 24) := []
private def e42 : List (Fin 24 × Fin 24) := [(6, 15), (6, 17), (6, 18), (6, 22), (7, 16), (7, 18), (7, 19), (7, 23), (8, 12), (8, 17), (8, 19), (8, 20), (10, 13), (10, 19), (10, 21), (10, 22), (11, 14), (11, 20), (11, 22), (11, 23)]
private theorem h42 : ∀ s, HasCircuitSize 24 (gfn a42 e42) s → 20 ≤ s := by
  intro s hs
  exact q190 (n:=23) a42 e42 12 a41 e41 19 (by decide) rfl rfl (by decide) h41 s hs
private def a43 : List (Fin 24) := []
private def e43 : List (Fin 24 × Fin 24) := [(6, 22), (10, 19), (10, 22), (11, 22), (11, 23)]
private theorem h43 : ∀ s, HasCircuitSize 24 (gfn a43 e43) s → 7 ≤ s := by
  intro s hs
  exact q155 (n:=23) a43 e43 19 a3 e3 a5 e5 5 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 5≤5) h3) (q216 (by decide : 5≤5) h5) s hs
private def a44 : List (Fin 24) := []
private def e44 : List (Fin 24 × Fin 24) := [(6, 17), (6, 22), (10, 19), (10, 22), (11, 22), (11, 23)]
private theorem h44 : ∀ s, HasCircuitSize 24 (gfn a44 e44) s → 8 ≤ s := by
  intro s hs
  exact q190 (n:=23) a44 e44 17 a43 e43 7 (by decide) rfl rfl (by decide) h43 s hs
private def a45 : List (Fin 24) := []
private def e45 : List (Fin 24 × Fin 24) := [(6, 17), (6, 22), (7, 19), (7, 23), (10, 19), (10, 22), (11, 22), (11, 23)]
private theorem h45 : ∀ s, HasCircuitSize 24 (gfn a45 e45) s → 9 ≤ s := by
  intro s hs
  exact q190 (n:=23) a45 e45 7 a44 e44 8 (by decide) rfl rfl (by decide) h44 s hs
private def a46 : List (Fin 24) := [7]
private def e46 : List (Fin 24 × Fin 24) := [(6, 17), (6, 22), (10, 19), (10, 22), (11, 22), (11, 23)]
private theorem h46 : ∀ s, HasCircuitSize 24 (gfn a46 e46) s → 9 ≤ s := by
  intro s hs
  exact q190 (n:=23) a46 e46 7 a44 e44 8 (by decide) rfl rfl (by decide) h44 s hs
private def a47 : List (Fin 24) := []
private def e47 : List (Fin 24 × Fin 24) := [(6, 17), (6, 22), (7, 16), (7, 19), (7, 23), (10, 19), (10, 22), (11, 22), (11, 23)]
private theorem h47 : ∀ s, HasCircuitSize 24 (gfn a47 e47) s → 11 ≤ s := by
  intro s hs
  exact q155 (n:=23) a47 e47 16 a45 e45 a46 e46 9 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 9≤9) h45) (q216 (by decide : 9≤9) h46) s hs
private def a48 : List (Fin 24) := []
private def e48 : List (Fin 24 × Fin 24) := [(6, 15), (6, 17), (6, 22), (7, 16), (7, 19), (7, 23), (10, 19), (10, 22), (11, 22), (11, 23)]
private theorem h48 : ∀ s, HasCircuitSize 24 (gfn a48 e48) s → 12 ≤ s := by
  intro s hs
  exact q190 (n:=23) a48 e48 15 a47 e47 11 (by decide) rfl rfl (by decide) h47 s hs
private def a49 : List (Fin 24) := []
private def e49 : List (Fin 24 × Fin 24) := [(6, 15), (6, 17), (6, 22), (7, 16), (7, 19), (7, 23), (10, 19), (10, 22), (11, 14), (11, 22), (11, 23)]
private theorem h49 : ∀ s, HasCircuitSize 24 (gfn a49 e49) s → 13 ≤ s := by
  intro s hs
  exact q190 (n:=23) a49 e49 14 a48 e48 12 (by decide) rfl rfl (by decide) h48 s hs
private def a50 : List (Fin 24) := []
private def e50 : List (Fin 24 × Fin 24) := [(6, 15), (6, 17), (6, 22), (7, 16), (7, 19), (7, 23), (10, 13), (10, 19), (10, 22), (11, 14), (11, 22), (11, 23)]
private theorem h50 : ∀ s, HasCircuitSize 24 (gfn a50 e50) s → 14 ≤ s := by
  intro s hs
  exact q190 (n:=23) a50 e50 13 a49 e49 13 (by decide) rfl rfl (by decide) h49 s hs
private def a51 : List (Fin 24) := [23]
private def e51 : List (Fin 24 × Fin 24) := [(11, 22)]
private theorem h51 : ∀ s, HasCircuitSize 24 (gfn a51 e51) s → 2 ≤ s := by
  exact supportBound _ _ _ (by decide +kernel)
private def a52 : List (Fin 24) := []
private def e52 : List (Fin 24 × Fin 24) := [(7, 23), (11, 22), (11, 23)]
private theorem h52 : ∀ s, HasCircuitSize 24 (gfn a52 e52) s → 4 ≤ s := by
  intro s hs
  exact q155 (n:=23) a52 e52 7 a0 e0 a51 e51 2 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 2≤2) h0) (q216 (by decide : 2≤2) h51) s hs
private def a53 : List (Fin 24) := []
private def e53 : List (Fin 24 × Fin 24) := [(7, 16), (7, 23), (11, 22), (11, 23)]
private theorem h53 : ∀ s, HasCircuitSize 24 (gfn a53 e53) s → 5 ≤ s := by
  intro s hs
  exact q190 (n:=23) a53 e53 16 a52 e52 4 (by decide) rfl rfl (by decide) h52 s hs
private def a54 : List (Fin 24) := []
private def e54 : List (Fin 24 × Fin 24) := [(7, 16), (7, 23)]
private theorem h54 : ∀ s, HasCircuitSize 24 (gfn a54 e54) s → 2 ≤ s := by
  exact supportBound _ _ _ (by decide +kernel)
private def a55 : List (Fin 24) := [23]
private def e55 : List (Fin 24 × Fin 24) := [(7, 16)]
private theorem h55 : ∀ s, HasCircuitSize 24 (gfn a55 e55) s → 2 ≤ s := by
  exact supportBound _ _ _ (by decide +kernel)
private def a56 : List (Fin 24) := []
private def e56 : List (Fin 24 × Fin 24) := [(7, 16), (7, 23), (11, 23)]
private theorem h56 : ∀ s, HasCircuitSize 24 (gfn a56 e56) s → 4 ≤ s := by
  intro s hs
  exact q155 (n:=23) a56 e56 11 a54 e54 a55 e55 2 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 2≤2) h54) (q216 (by decide : 2≤2) h55) s hs
private def a57 : List (Fin 24) := [22]
private def e57 : List (Fin 24 × Fin 24) := [(7, 16), (7, 23), (11, 23)]
private theorem h57 : ∀ s, HasCircuitSize 24 (gfn a57 e57) s → 5 ≤ s := by
  intro s hs
  exact q190 (n:=23) a57 e57 22 a56 e56 4 (by decide) rfl rfl (by decide) h56 s hs
private def a58 : List (Fin 24) := []
private def e58 : List (Fin 24 × Fin 24) := [(7, 16), (7, 23), (10, 22), (11, 22), (11, 23)]
private theorem h58 : ∀ s, HasCircuitSize 24 (gfn a58 e58) s → 7 ≤ s := by
  intro s hs
  exact q155 (n:=23) a58 e58 10 a53 e53 a57 e57 5 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 5≤5) h53) (q216 (by decide : 5≤5) h57) s hs
private def a59 : List (Fin 24) := []
private def e59 : List (Fin 24 × Fin 24) := [(6, 22), (7, 16), (7, 23), (10, 22), (11, 22), (11, 23)]
private theorem h59 : ∀ s, HasCircuitSize 24 (gfn a59 e59) s → 8 ≤ s := by
  intro s hs
  exact q190 (n:=23) a59 e59 6 a58 e58 7 (by decide) rfl rfl (by decide) h58 s hs
private def a60 : List (Fin 24) := [6]
private def e60 : List (Fin 24 × Fin 24) := [(7, 16), (7, 23), (10, 22), (11, 22), (11, 23)]
private theorem h60 : ∀ s, HasCircuitSize 24 (gfn a60 e60) s → 8 ≤ s := by
  intro s hs
  exact q190 (n:=23) a60 e60 6 a58 e58 7 (by decide) rfl rfl (by decide) h58 s hs
private def a61 : List (Fin 24) := []
private def e61 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (7, 16), (7, 23), (10, 22), (11, 22), (11, 23)]
private theorem h61 : ∀ s, HasCircuitSize 24 (gfn a61 e61) s → 10 ≤ s := by
  intro s hs
  exact q155 (n:=23) a61 e61 15 a59 e59 a60 e60 8 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 8≤8) h59) (q216 (by decide : 8≤8) h60) s hs
private def a62 : List (Fin 24) := []
private def e62 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (7, 16), (7, 23), (10, 22), (11, 14), (11, 22), (11, 23)]
private theorem h62 : ∀ s, HasCircuitSize 24 (gfn a62 e62) s → 11 ≤ s := by
  intro s hs
  exact q190 (n:=23) a62 e62 14 a61 e61 10 (by decide) rfl rfl (by decide) h61 s hs
private def a63 : List (Fin 24) := []
private def e63 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (7, 16), (7, 23), (10, 13), (10, 22), (11, 14), (11, 22), (11, 23)]
private theorem h63 : ∀ s, HasCircuitSize 24 (gfn a63 e63) s → 12 ≤ s := by
  intro s hs
  exact q190 (n:=23) a63 e63 13 a62 e62 11 (by decide) rfl rfl (by decide) h62 s hs
private def a64 : List (Fin 24) := [19]
private def e64 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (7, 16), (7, 23), (10, 13), (10, 22), (11, 14), (11, 22), (11, 23)]
private theorem h64 : ∀ s, HasCircuitSize 24 (gfn a64 e64) s → 13 ≤ s := by
  intro s hs
  exact q190 (n:=23) a64 e64 19 a63 e63 12 (by decide) rfl rfl (by decide) h63 s hs
private def a65 : List (Fin 24) := [17, 19]
private def e65 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (7, 16), (7, 23), (10, 13), (10, 22), (11, 14), (11, 22), (11, 23)]
private theorem h65 : ∀ s, HasCircuitSize 24 (gfn a65 e65) s → 14 ≤ s := by
  intro s hs
  exact q190 (n:=23) a65 e65 17 a64 e64 13 (by decide) rfl rfl (by decide) h64 s hs
private def a66 : List (Fin 24) := []
private def e66 : List (Fin 24 × Fin 24) := [(6, 15), (6, 17), (6, 22), (7, 16), (7, 19), (7, 23), (8, 17), (8, 19), (10, 13), (10, 19), (10, 22), (11, 14), (11, 22), (11, 23)]
private theorem h66 : ∀ s, HasCircuitSize 24 (gfn a66 e66) s → 16 ≤ s := by
  intro s hs
  exact q155 (n:=23) a66 e66 8 a50 e50 a65 e65 14 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 14≤14) h50) (q216 (by decide : 14≤14) h65) s hs
private def a67 : List (Fin 24) := []
private def e67 : List (Fin 24 × Fin 24) := [(6, 15), (6, 17), (6, 22), (7, 16), (7, 19), (7, 23), (8, 12), (8, 17), (8, 19), (10, 13), (10, 19), (10, 22), (11, 14), (11, 22), (11, 23)]
private theorem h67 : ∀ s, HasCircuitSize 24 (gfn a67 e67) s → 17 ≤ s := by
  intro s hs
  exact q190 (n:=23) a67 e67 12 a66 e66 16 (by decide) rfl rfl (by decide) h66 s hs
private def a68 : List (Fin 24) := [21]
private def e68 : List (Fin 24 × Fin 24) := [(6, 15), (6, 17), (6, 22), (7, 16), (7, 19), (7, 23), (8, 12), (8, 17), (8, 19), (10, 13), (10, 19), (10, 22), (11, 14), (11, 22), (11, 23)]
private theorem h68 : ∀ s, HasCircuitSize 24 (gfn a68 e68) s → 18 ≤ s := by
  intro s hs
  exact q190 (n:=23) a68 e68 21 a67 e67 17 (by decide) rfl rfl (by decide) h67 s hs
private def a69 : List (Fin 24) := [20, 21]
private def e69 : List (Fin 24 × Fin 24) := [(6, 15), (6, 17), (6, 22), (7, 16), (7, 19), (7, 23), (8, 12), (8, 17), (8, 19), (10, 13), (10, 19), (10, 22), (11, 14), (11, 22), (11, 23)]
private theorem h69 : ∀ s, HasCircuitSize 24 (gfn a69 e69) s → 19 ≤ s := by
  intro s hs
  exact q190 (n:=23) a69 e69 20 a68 e68 18 (by decide) rfl rfl (by decide) h68 s hs
private def a70 : List (Fin 24) := [18, 20, 21]
private def e70 : List (Fin 24 × Fin 24) := [(6, 15), (6, 17), (6, 22), (7, 16), (7, 19), (7, 23), (8, 12), (8, 17), (8, 19), (10, 13), (10, 19), (10, 22), (11, 14), (11, 22), (11, 23)]
private theorem h70 : ∀ s, HasCircuitSize 24 (gfn a70 e70) s → 20 ≤ s := by
  intro s hs
  exact q190 (n:=23) a70 e70 18 a69 e69 19 (by decide) rfl rfl (by decide) h69 s hs
private def a71 : List (Fin 24) := []
private def e71 : List (Fin 24 × Fin 24) := [(6, 15), (6, 17), (6, 18), (6, 22), (7, 16), (7, 18), (7, 19), (7, 23), (8, 12), (8, 17), (8, 19), (8, 20), (9, 18), (9, 20), (9, 21), (10, 13), (10, 19), (10, 21), (10, 22), (11, 14), (11, 20), (11, 22), (11, 23)]
private theorem h71 : ∀ s, HasCircuitSize 24 (gfn a71 e71) s → 22 ≤ s := by
  intro s hs
  exact q155 (n:=23) a71 e71 9 a42 e42 a70 e70 20 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 20≤20) h42) (q216 (by decide : 20≤20) h70) s hs
private def a72 : List (Fin 24) := []
private def e72 : List (Fin 24 × Fin 24) := [(11, 20), (11, 22), (11, 23)]
private theorem h72 : ∀ s, HasCircuitSize 24 (gfn a72 e72) s → 3 ≤ s := by
  exact supportBound _ _ _ (by decide +kernel)
private def a73 : List (Fin 24) := [22]
private def e73 : List (Fin 24 × Fin 24) := [(11, 20), (11, 23)]
private theorem h73 : ∀ s, HasCircuitSize 24 (gfn a73 e73) s → 3 ≤ s := by
  exact supportBound _ _ _ (by decide +kernel)
private def a74 : List (Fin 24) := []
private def e74 : List (Fin 24 × Fin 24) := [(10, 22), (11, 20), (11, 22), (11, 23)]
private theorem h74 : ∀ s, HasCircuitSize 24 (gfn a74 e74) s → 5 ≤ s := by
  intro s hs
  exact q155 (n:=23) a74 e74 10 a72 e72 a73 e73 3 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 3≤3) h72) (q216 (by decide : 3≤3) h73) s hs
private def a75 : List (Fin 24) := []
private def e75 : List (Fin 24 × Fin 24) := [(6, 22), (10, 22), (11, 20), (11, 22), (11, 23)]
private theorem h75 : ∀ s, HasCircuitSize 24 (gfn a75 e75) s → 6 ≤ s := by
  intro s hs
  exact q190 (n:=23) a75 e75 6 a74 e74 5 (by decide) rfl rfl (by decide) h74 s hs
private def a76 : List (Fin 24) := []
private def e76 : List (Fin 24 × Fin 24) := [(6, 22), (11, 20), (11, 22), (11, 23)]
private theorem h76 : ∀ s, HasCircuitSize 24 (gfn a76 e76) s → 5 ≤ s := by
  intro s hs
  exact q155 (n:=23) a76 e76 6 a72 e72 a73 e73 3 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 3≤3) h72) (q216 (by decide : 3≤3) h73) s hs
private def a77 : List (Fin 24) := [10]
private def e77 : List (Fin 24 × Fin 24) := [(6, 22), (11, 20), (11, 22), (11, 23)]
private theorem h77 : ∀ s, HasCircuitSize 24 (gfn a77 e77) s → 6 ≤ s := by
  intro s hs
  exact q190 (n:=23) a77 e77 10 a76 e76 5 (by decide) rfl rfl (by decide) h76 s hs
private def a78 : List (Fin 24) := []
private def e78 : List (Fin 24 × Fin 24) := [(6, 22), (10, 19), (10, 22), (11, 20), (11, 22), (11, 23)]
private theorem h78 : ∀ s, HasCircuitSize 24 (gfn a78 e78) s → 8 ≤ s := by
  intro s hs
  exact q155 (n:=23) a78 e78 19 a75 e75 a77 e77 6 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 6≤6) h75) (q216 (by decide : 6≤6) h77) s hs
private def a79 : List (Fin 24) := []
private def e79 : List (Fin 24 × Fin 24) := [(6, 18), (6, 22), (10, 19), (10, 22), (11, 20), (11, 22), (11, 23)]
private theorem h79 : ∀ s, HasCircuitSize 24 (gfn a79 e79) s → 9 ≤ s := by
  intro s hs
  exact q190 (n:=23) a79 e79 18 a78 e78 8 (by decide) rfl rfl (by decide) h78 s hs
private def a80 : List (Fin 24) := []
private def e80 : List (Fin 24 × Fin 24) := [(6, 15), (6, 18), (6, 22), (10, 19), (10, 22), (11, 20), (11, 22), (11, 23)]
private theorem h80 : ∀ s, HasCircuitSize 24 (gfn a80 e80) s → 10 ≤ s := by
  intro s hs
  exact q190 (n:=23) a80 e80 15 a79 e79 9 (by decide) rfl rfl (by decide) h79 s hs
private def a81 : List (Fin 24) := []
private def e81 : List (Fin 24 × Fin 24) := [(6, 15), (6, 18), (6, 22), (10, 13), (10, 19), (10, 22), (11, 20), (11, 22), (11, 23)]
private theorem h81 : ∀ s, HasCircuitSize 24 (gfn a81 e81) s → 11 ≤ s := by
  intro s hs
  exact q190 (n:=23) a81 e81 13 a80 e80 10 (by decide) rfl rfl (by decide) h80 s hs
private def a82 : List (Fin 24) := [6]
private def e82 : List (Fin 24 × Fin 24) := [(10, 22), (11, 22), (11, 23)]
private theorem h82 : ∀ s, HasCircuitSize 24 (gfn a82 e82) s → 5 ≤ s := by
  intro s hs
  exact q190 (n:=23) a82 e82 6 a2 e2 4 (by decide) rfl rfl (by decide) h2 s hs
private def a83 : List (Fin 24) := []
private def e83 : List (Fin 24 × Fin 24) := [(6, 18), (6, 22), (10, 22), (11, 22), (11, 23)]
private theorem h83 : ∀ s, HasCircuitSize 24 (gfn a83 e83) s → 7 ≤ s := by
  intro s hs
  exact q155 (n:=23) a83 e83 18 a3 e3 a82 e82 5 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 5≤5) h3) (q216 (by decide : 5≤5) h82) s hs
private def a84 : List (Fin 24) := []
private def e84 : List (Fin 24 × Fin 24) := [(6, 15), (6, 18), (6, 22), (10, 22), (11, 22), (11, 23)]
private theorem h84 : ∀ s, HasCircuitSize 24 (gfn a84 e84) s → 8 ≤ s := by
  intro s hs
  exact q190 (n:=23) a84 e84 15 a83 e83 7 (by decide) rfl rfl (by decide) h83 s hs
private def a85 : List (Fin 24) := []
private def e85 : List (Fin 24 × Fin 24) := [(6, 15), (6, 18), (6, 22), (10, 13), (10, 22), (11, 22), (11, 23)]
private theorem h85 : ∀ s, HasCircuitSize 24 (gfn a85 e85) s → 9 ≤ s := by
  intro s hs
  exact q190 (n:=23) a85 e85 13 a84 e84 8 (by decide) rfl rfl (by decide) h84 s hs
private def a86 : List (Fin 24) := [20]
private def e86 : List (Fin 24 × Fin 24) := [(6, 15), (6, 18), (6, 22), (10, 13), (10, 22), (11, 22), (11, 23)]
private theorem h86 : ∀ s, HasCircuitSize 24 (gfn a86 e86) s → 10 ≤ s := by
  intro s hs
  exact q190 (n:=23) a86 e86 20 a85 e85 9 (by decide) rfl rfl (by decide) h85 s hs
private def a87 : List (Fin 24) := [19, 20]
private def e87 : List (Fin 24 × Fin 24) := [(6, 15), (6, 18), (6, 22), (10, 13), (10, 22), (11, 22), (11, 23)]
private theorem h87 : ∀ s, HasCircuitSize 24 (gfn a87 e87) s → 11 ≤ s := by
  intro s hs
  exact q190 (n:=23) a87 e87 19 a86 e86 10 (by decide) rfl rfl (by decide) h86 s hs
private def a88 : List (Fin 24) := []
private def e88 : List (Fin 24 × Fin 24) := [(6, 15), (6, 18), (6, 22), (8, 19), (8, 20), (10, 13), (10, 19), (10, 22), (11, 20), (11, 22), (11, 23)]
private theorem h88 : ∀ s, HasCircuitSize 24 (gfn a88 e88) s → 13 ≤ s := by
  intro s hs
  exact q155 (n:=23) a88 e88 8 a81 e81 a87 e87 11 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 11≤11) h81) (q216 (by decide : 11≤11) h87) s hs
private def a89 : List (Fin 24) := []
private def e89 : List (Fin 24 × Fin 24) := [(6, 15), (6, 18), (6, 22), (8, 12), (8, 19), (8, 20), (10, 13), (10, 19), (10, 22), (11, 20), (11, 22), (11, 23)]
private theorem h89 : ∀ s, HasCircuitSize 24 (gfn a89 e89) s → 14 ≤ s := by
  intro s hs
  exact q190 (n:=23) a89 e89 12 a88 e88 13 (by decide) rfl rfl (by decide) h88 s hs
private def a90 : List (Fin 24) := []
private def e90 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (10, 19), (10, 22), (11, 22), (11, 23)]
private theorem h90 : ∀ s, HasCircuitSize 24 (gfn a90 e90) s → 8 ≤ s := by
  intro s hs
  exact q190 (n:=23) a90 e90 15 a43 e43 7 (by decide) rfl rfl (by decide) h43 s hs
private def a91 : List (Fin 24) := []
private def e91 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (10, 13), (10, 19), (10, 22), (11, 22), (11, 23)]
private theorem h91 : ∀ s, HasCircuitSize 24 (gfn a91 e91) s → 9 ≤ s := by
  intro s hs
  exact q190 (n:=23) a91 e91 13 a90 e90 8 (by decide) rfl rfl (by decide) h90 s hs
private def a92 : List (Fin 24) := []
private def e92 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (10, 22), (11, 22), (11, 23)]
private theorem h92 : ∀ s, HasCircuitSize 24 (gfn a92 e92) s → 7 ≤ s := by
  intro s hs
  exact q155 (n:=23) a92 e92 15 a3 e3 a82 e82 5 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 5≤5) h3) (q216 (by decide : 5≤5) h82) s hs
private def a93 : List (Fin 24) := []
private def e93 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (10, 13), (10, 22), (11, 22), (11, 23)]
private theorem h93 : ∀ s, HasCircuitSize 24 (gfn a93 e93) s → 8 ≤ s := by
  intro s hs
  exact q190 (n:=23) a93 e93 13 a92 e92 7 (by decide) rfl rfl (by decide) h92 s hs
private def a94 : List (Fin 24) := [19]
private def e94 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (10, 13), (10, 22), (11, 22), (11, 23)]
private theorem h94 : ∀ s, HasCircuitSize 24 (gfn a94 e94) s → 9 ≤ s := by
  intro s hs
  exact q190 (n:=23) a94 e94 19 a93 e93 8 (by decide) rfl rfl (by decide) h93 s hs
private def a95 : List (Fin 24) := []
private def e95 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (8, 19), (10, 13), (10, 19), (10, 22), (11, 22), (11, 23)]
private theorem h95 : ∀ s, HasCircuitSize 24 (gfn a95 e95) s → 11 ≤ s := by
  intro s hs
  exact q155 (n:=23) a95 e95 8 a91 e91 a94 e94 9 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 9≤9) h91) (q216 (by decide : 9≤9) h94) s hs
private def a96 : List (Fin 24) := []
private def e96 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (8, 12), (8, 19), (10, 13), (10, 19), (10, 22), (11, 22), (11, 23)]
private theorem h96 : ∀ s, HasCircuitSize 24 (gfn a96 e96) s → 12 ≤ s := by
  intro s hs
  exact q190 (n:=23) a96 e96 12 a95 e95 11 (by decide) rfl rfl (by decide) h95 s hs
private def a97 : List (Fin 24) := [20]
private def e97 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (8, 12), (8, 19), (10, 13), (10, 19), (10, 22), (11, 22), (11, 23)]
private theorem h97 : ∀ s, HasCircuitSize 24 (gfn a97 e97) s → 13 ≤ s := by
  intro s hs
  exact q190 (n:=23) a97 e97 20 a96 e96 12 (by decide) rfl rfl (by decide) h96 s hs
private def a98 : List (Fin 24) := [18, 20]
private def e98 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (8, 12), (8, 19), (10, 13), (10, 19), (10, 22), (11, 22), (11, 23)]
private theorem h98 : ∀ s, HasCircuitSize 24 (gfn a98 e98) s → 14 ≤ s := by
  intro s hs
  exact q190 (n:=23) a98 e98 18 a97 e97 13 (by decide) rfl rfl (by decide) h97 s hs
private def a99 : List (Fin 24) := []
private def e99 : List (Fin 24 × Fin 24) := [(6, 15), (6, 18), (6, 22), (8, 12), (8, 19), (8, 20), (9, 18), (9, 20), (10, 13), (10, 19), (10, 22), (11, 20), (11, 22), (11, 23)]
private theorem h99 : ∀ s, HasCircuitSize 24 (gfn a99 e99) s → 16 ≤ s := by
  intro s hs
  exact q155 (n:=23) a99 e99 9 a89 e89 a98 e98 14 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 14≤14) h89) (q216 (by decide : 14≤14) h98) s hs
private def a100 : List (Fin 24) := []
private def e100 : List (Fin 24 × Fin 24) := [(11, 20), (11, 22)]
private theorem h100 : ∀ s, HasCircuitSize 24 (gfn a100 e100) s → 2 ≤ s := by
  exact supportBound _ _ _ (by decide +kernel)
private def a101 : List (Fin 24) := [22]
private def e101 : List (Fin 24 × Fin 24) := [(11, 20)]
private theorem h101 : ∀ s, HasCircuitSize 24 (gfn a101 e101) s → 2 ≤ s := by
  exact supportBound _ _ _ (by decide +kernel)
private def a102 : List (Fin 24) := []
private def e102 : List (Fin 24 × Fin 24) := [(10, 22), (11, 20), (11, 22)]
private theorem h102 : ∀ s, HasCircuitSize 24 (gfn a102 e102) s → 4 ≤ s := by
  intro s hs
  exact q155 (n:=23) a102 e102 10 a100 e100 a101 e101 2 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 2≤2) h100) (q216 (by decide : 2≤2) h101) s hs
private def a103 : List (Fin 24) := []
private def e103 : List (Fin 24 × Fin 24) := [(6, 22), (10, 22), (11, 20), (11, 22)]
private theorem h103 : ∀ s, HasCircuitSize 24 (gfn a103 e103) s → 5 ≤ s := by
  intro s hs
  exact q190 (n:=23) a103 e103 6 a102 e102 4 (by decide) rfl rfl (by decide) h102 s hs
private def a104 : List (Fin 24) := [6]
private def e104 : List (Fin 24 × Fin 24) := [(10, 22), (11, 20), (11, 22)]
private theorem h104 : ∀ s, HasCircuitSize 24 (gfn a104 e104) s → 5 ≤ s := by
  intro s hs
  exact q190 (n:=23) a104 e104 6 a102 e102 4 (by decide) rfl rfl (by decide) h102 s hs
private def a105 : List (Fin 24) := []
private def e105 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (10, 22), (11, 20), (11, 22)]
private theorem h105 : ∀ s, HasCircuitSize 24 (gfn a105 e105) s → 7 ≤ s := by
  intro s hs
  exact q155 (n:=23) a105 e105 15 a103 e103 a104 e104 5 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 5≤5) h103) (q216 (by decide : 5≤5) h104) s hs
private def a106 : List (Fin 24) := []
private def e106 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (10, 13), (10, 22), (11, 20), (11, 22)]
private theorem h106 : ∀ s, HasCircuitSize 24 (gfn a106 e106) s → 8 ≤ s := by
  intro s hs
  exact q190 (n:=23) a106 e106 13 a105 e105 7 (by decide) rfl rfl (by decide) h105 s hs
private def a107 : List (Fin 24) := []
private def e107 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22)]
private theorem h107 : ∀ s, HasCircuitSize 24 (gfn a107 e107) s → 2 ≤ s := by
  exact supportBound _ _ _ (by decide +kernel)
private def a108 : List (Fin 24) := [22]
private def e108 : List (Fin 24 × Fin 24) := [(6, 15)]
private theorem h108 : ∀ s, HasCircuitSize 24 (gfn a108 e108) s → 2 ≤ s := by
  exact supportBound _ _ _ (by decide +kernel)
private def a109 : List (Fin 24) := []
private def e109 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (11, 22)]
private theorem h109 : ∀ s, HasCircuitSize 24 (gfn a109 e109) s → 4 ≤ s := by
  intro s hs
  exact q155 (n:=23) a109 e109 11 a107 e107 a108 e108 2 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 2≤2) h107) (q216 (by decide : 2≤2) h108) s hs
private def a110 : List (Fin 24) := []
private def e110 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (10, 22), (11, 22)]
private theorem h110 : ∀ s, HasCircuitSize 24 (gfn a110 e110) s → 5 ≤ s := by
  intro s hs
  exact q190 (n:=23) a110 e110 10 a109 e109 4 (by decide) rfl rfl (by decide) h109 s hs
private def a111 : List (Fin 24) := [10]
private def e111 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (11, 22)]
private theorem h111 : ∀ s, HasCircuitSize 24 (gfn a111 e111) s → 5 ≤ s := by
  intro s hs
  exact q190 (n:=23) a111 e111 10 a109 e109 4 (by decide) rfl rfl (by decide) h109 s hs
private def a112 : List (Fin 24) := []
private def e112 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (10, 13), (10, 22), (11, 22)]
private theorem h112 : ∀ s, HasCircuitSize 24 (gfn a112 e112) s → 7 ≤ s := by
  intro s hs
  exact q155 (n:=23) a112 e112 13 a110 e110 a111 e111 5 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 5≤5) h110) (q216 (by decide : 5≤5) h111) s hs
private def a113 : List (Fin 24) := [20]
private def e113 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (10, 13), (10, 22), (11, 22)]
private theorem h113 : ∀ s, HasCircuitSize 24 (gfn a113 e113) s → 8 ≤ s := by
  intro s hs
  exact q190 (n:=23) a113 e113 20 a112 e112 7 (by decide) rfl rfl (by decide) h112 s hs
private def a114 : List (Fin 24) := []
private def e114 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (9, 20), (10, 13), (10, 22), (11, 20), (11, 22)]
private theorem h114 : ∀ s, HasCircuitSize 24 (gfn a114 e114) s → 10 ≤ s := by
  intro s hs
  exact q155 (n:=23) a114 e114 9 a106 e106 a113 e113 8 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 8≤8) h106) (q216 (by decide : 8≤8) h113) s hs
private def a115 : List (Fin 24) := []
private def e115 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (8, 20), (9, 20), (10, 13), (10, 22), (11, 20), (11, 22)]
private theorem h115 : ∀ s, HasCircuitSize 24 (gfn a115 e115) s → 11 ≤ s := by
  intro s hs
  exact q190 (n:=23) a115 e115 8 a114 e114 10 (by decide) rfl rfl (by decide) h114 s hs
private def a116 : List (Fin 24) := [8]
private def e116 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (9, 20), (10, 13), (10, 22), (11, 20), (11, 22)]
private theorem h116 : ∀ s, HasCircuitSize 24 (gfn a116 e116) s → 11 ≤ s := by
  intro s hs
  exact q190 (n:=23) a116 e116 8 a114 e114 10 (by decide) rfl rfl (by decide) h114 s hs
private def a117 : List (Fin 24) := []
private def e117 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (8, 12), (8, 20), (9, 20), (10, 13), (10, 22), (11, 20), (11, 22)]
private theorem h117 : ∀ s, HasCircuitSize 24 (gfn a117 e117) s → 13 ≤ s := by
  intro s hs
  exact q155 (n:=23) a117 e117 12 a115 e115 a116 e116 11 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 11≤11) h115) (q216 (by decide : 11≤11) h116) s hs
private def a118 : List (Fin 24) := [23]
private def e118 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (8, 12), (8, 20), (9, 20), (10, 13), (10, 22), (11, 20), (11, 22)]
private theorem h118 : ∀ s, HasCircuitSize 24 (gfn a118 e118) s → 14 ≤ s := by
  intro s hs
  exact q190 (n:=23) a118 e118 23 a117 e117 13 (by decide) rfl rfl (by decide) h117 s hs
private def a119 : List (Fin 24) := [19, 23]
private def e119 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (8, 12), (8, 20), (9, 20), (10, 13), (10, 22), (11, 20), (11, 22)]
private theorem h119 : ∀ s, HasCircuitSize 24 (gfn a119 e119) s → 15 ≤ s := by
  intro s hs
  exact q190 (n:=23) a119 e119 19 a118 e118 14 (by decide) rfl rfl (by decide) h118 s hs
private def a120 : List (Fin 24) := [18, 19, 23]
private def e120 : List (Fin 24 × Fin 24) := [(6, 15), (6, 22), (8, 12), (8, 20), (9, 20), (10, 13), (10, 22), (11, 20), (11, 22)]
private theorem h120 : ∀ s, HasCircuitSize 24 (gfn a120 e120) s → 16 ≤ s := by
  intro s hs
  exact q190 (n:=23) a120 e120 18 a119 e119 15 (by decide) rfl rfl (by decide) h119 s hs
private def a121 : List (Fin 24) := []
private def e121 : List (Fin 24 × Fin 24) := [(6, 15), (6, 18), (6, 22), (7, 18), (7, 19), (7, 23), (8, 12), (8, 19), (8, 20), (9, 18), (9, 20), (10, 13), (10, 19), (10, 22), (11, 20), (11, 22), (11, 23)]
private theorem h121 : ∀ s, HasCircuitSize 24 (gfn a121 e121) s → 18 ≤ s := by
  intro s hs
  exact q155 (n:=23) a121 e121 7 a99 e99 a120 e120 16 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 16≤16) h99) (q216 (by decide : 16≤16) h120) s hs
private def a122 : List (Fin 24) := [21]
private def e122 : List (Fin 24 × Fin 24) := [(6, 15), (6, 18), (6, 22), (7, 18), (7, 19), (7, 23), (8, 12), (8, 19), (8, 20), (9, 18), (9, 20), (10, 13), (10, 19), (10, 22), (11, 20), (11, 22), (11, 23)]
private theorem h122 : ∀ s, HasCircuitSize 24 (gfn a122 e122) s → 19 ≤ s := by
  intro s hs
  exact q190 (n:=23) a122 e122 21 a121 e121 18 (by decide) rfl rfl (by decide) h121 s hs
private def a123 : List (Fin 24) := [17, 21]
private def e123 : List (Fin 24 × Fin 24) := [(6, 15), (6, 18), (6, 22), (7, 18), (7, 19), (7, 23), (8, 12), (8, 19), (8, 20), (9, 18), (9, 20), (10, 13), (10, 19), (10, 22), (11, 20), (11, 22), (11, 23)]
private theorem h123 : ∀ s, HasCircuitSize 24 (gfn a123 e123) s → 20 ≤ s := by
  intro s hs
  exact q190 (n:=23) a123 e123 17 a122 e122 19 (by decide) rfl rfl (by decide) h122 s hs
private def a124 : List (Fin 24) := [16, 17, 21]
private def e124 : List (Fin 24 × Fin 24) := [(6, 15), (6, 18), (6, 22), (7, 18), (7, 19), (7, 23), (8, 12), (8, 19), (8, 20), (9, 18), (9, 20), (10, 13), (10, 19), (10, 22), (11, 20), (11, 22), (11, 23)]
private theorem h124 : ∀ s, HasCircuitSize 24 (gfn a124 e124) s → 21 ≤ s := by
  intro s hs
  exact q190 (n:=23) a124 e124 16 a123 e123 20 (by decide) rfl rfl (by decide) h123 s hs
private def a125 : List (Fin 24) := [14, 16, 17, 21]
private def e125 : List (Fin 24 × Fin 24) := [(6, 15), (6, 18), (6, 22), (7, 18), (7, 19), (7, 23), (8, 12), (8, 19), (8, 20), (9, 18), (9, 20), (10, 13), (10, 19), (10, 22), (11, 20), (11, 22), (11, 23)]
private theorem h125 : ∀ s, HasCircuitSize 24 (gfn a125 e125) s → 22 ≤ s := by
  intro s hs
  exact q190 (n:=23) a125 e125 14 a124 e124 21 (by decide) rfl rfl (by decide) h124 s hs
private def a126 : List (Fin 24) := []
private def e126 : List (Fin 24 × Fin 24) := [(5, 14), (5, 16), (5, 17), (5, 21), (6, 15), (6, 17), (6, 18), (6, 22), (7, 16), (7, 18), (7, 19), (7, 23), (8, 12), (8, 17), (8, 19), (8, 20), (9, 18), (9, 20), (9, 21), (10, 13), (10, 19), (10, 21), (10, 22), (11, 14), (11, 20), (11, 22), (11, 23)]
private theorem h126 : ∀ s, HasCircuitSize 24 (gfn a126 e126) s → 24 ≤ s := by
  intro s hs
  exact q155 (n:=23) a126 e126 5 a71 e71 a125 e125 22 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (q216 (by decide : 22≤22) h71) (q216 (by decide : 22≤22) h125) s hs
private def a127 : List (Fin 24) := []
private def e127 : List (Fin 24 × Fin 24) := [(4, 13), (4, 15), (4, 16), (4, 20), (5, 14), (5, 16), (5, 17), (5, 21), (6, 15), (6, 17), (6, 18), (6, 22), (7, 16), (7, 18), (7, 19), (7, 23), (8, 12), (8, 17), (8, 19), (8, 20), (9, 18), (9, 20), (9, 21), (10, 13), (10, 19), (10, 21), (10, 22), (11, 14), (11, 20), (11, 22), (11, 23)]
private theorem h127 : ∀ s, HasCircuitSize 24 (gfn a127 e127) s → 25 ≤ s := by
  intro s hs
  exact q190 (n:=23) a127 e127 4 a126 e126 24 (by decide) rfl rfl (by decide) h126 s hs
private def a128 : List (Fin 24) := []
private def e128 : List (Fin 24 × Fin 24) := [(3, 14), (3, 15), (3, 19), (4, 13), (4, 15), (4, 16), (4, 20), (5, 14), (5, 16), (5, 17), (5, 21), (6, 15), (6, 17), (6, 18), (6, 22), (7, 16), (7, 18), (7, 19), (7, 23), (8, 12), (8, 17), (8, 19), (8, 20), (9, 18), (9, 20), (9, 21), (10, 13), (10, 19), (10, 21), (10, 22), (11, 14), (11, 20), (11, 22), (11, 23)]
private theorem h128 : ∀ s, HasCircuitSize 24 (gfn a128 e128) s → 26 ≤ s := by
  intro s hs
  exact q190 (n:=23) a128 e128 3 a127 e127 25 (by decide) rfl rfl (by decide) h127 s hs
private def a129 : List (Fin 24) := []
private def e129 : List (Fin 24 × Fin 24) := [(2, 12), (2, 13), (2, 14), (2, 18), (3, 14), (3, 15), (3, 19), (4, 13), (4, 15), (4, 16), (4, 20), (5, 14), (5, 16), (5, 17), (5, 21), (6, 15), (6, 17), (6, 18), (6, 22), (7, 16), (7, 18), (7, 19), (7, 23), (8, 12), (8, 17), (8, 19), (8, 20), (9, 18), (9, 20), (9, 21), (10, 13), (10, 19), (10, 21), (10, 22), (11, 14), (11, 20), (11, 22), (11, 23)]
private theorem h129 : ∀ s, HasCircuitSize 24 (gfn a129 e129) s → 27 ≤ s := by
  intro s hs
  exact q190 (n:=23) a129 e129 2 a128 e128 26 (by decide) rfl rfl (by decide) h128 s hs
private def a130 : List (Fin 24) := []
private def e130 : List (Fin 24 × Fin 24) := [(1, 13), (1, 17), (1, 23), (2, 12), (2, 13), (2, 14), (2, 18), (3, 14), (3, 15), (3, 19), (4, 13), (4, 15), (4, 16), (4, 20), (5, 14), (5, 16), (5, 17), (5, 21), (6, 15), (6, 17), (6, 18), (6, 22), (7, 16), (7, 18), (7, 19), (7, 23), (8, 12), (8, 17), (8, 19), (8, 20), (9, 18), (9, 20), (9, 21), (10, 13), (10, 19), (10, 21), (10, 22), (11, 14), (11, 20), (11, 22), (11, 23)]
private theorem h130 : ∀ s, HasCircuitSize 24 (gfn a130 e130) s → 28 ≤ s := by
  intro s hs
  exact q190 (n:=23) a130 e130 1 a129 e129 27 (by decide) rfl rfl (by decide) h129 s hs
private def a131 : List (Fin 24) := []
private def e131 : List (Fin 24 × Fin 24) := [(0, 12), (0, 16), (0, 22), (1, 13), (1, 17), (1, 23), (2, 12), (2, 13), (2, 14), (2, 18), (3, 14), (3, 15), (3, 19), (4, 13), (4, 15), (4, 16), (4, 20), (5, 14), (5, 16), (5, 17), (5, 21), (6, 15), (6, 17), (6, 18), (6, 22), (7, 16), (7, 18), (7, 19), (7, 23), (8, 12), (8, 17), (8, 19), (8, 20), (9, 18), (9, 20), (9, 21), (10, 13), (10, 19), (10, 21), (10, 22), (11, 14), (11, 20), (11, 22), (11, 23)]
private theorem h131 : ∀ s, HasCircuitSize 24 (gfn a131 e131) s → 29 ≤ s := by
  intro s hs
  exact q190 (n:=23) a131 e131 0 a130 e130 28 (by decide) rfl rfl (by decide) h130 s hs

theorem unrestricted_lower (C : Circuit) (hf : FanInTwo C) (hc : GraphClean9796.correct C) : 29≤C.size := by
  apply h131 C.size
  refine ⟨C,hf,le_refl _,?_⟩
  intro x
  have eq := Bool.eq_iff_iff.mpr ((hc x).trans (GraphFormula9796.graph_iff x).symm)
  exact eq
end GraphElimination9796


namespace GraphMatching9796
open GraphRows9796 GraphClean9796 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

def G : SimpleGraph V where
  Adj a b := adjacent a b=true
  symm := ⟨fun a b h => (adj_sym b a).trans h⟩
  loopless := ⟨by decide +kernel⟩
instance : DecidableRel G.Adj := fun a b => inferInstanceAs (Decidable (adjacent a b=true))

theorem degree_ge_two (v : V) : 2 ≤ (G.neighborSet v).ncard := by
  let nbr (u : V) := Finset.univ.filter (fun i : V => adjacent u i=true)
  have eq (u : V) : nbr u=G.neighborFinset u := by
    ext i
    rw [SimpleGraph.mem_neighborFinset]
    change i∈(Finset.univ.filter (fun z : V => adjacent u z=true)) ↔ adjacent u i=true
    simp
  have bound : ∀ u : V, 2 ≤ (nbr u).card := by dsimp only [nbr];decide +kernel
  rw [SimpleGraph.ncard_neighborSet,SimpleGraph.degree,←eq]
  apply bound

def leftSide : Finset V := Finset.univ.filter (fun u : V => u.val<12)
theorem no_isolates : ∀ u : V, ∃ v : V, G.Adj u v := by decide +kernel
theorem distinct_neighborhoods : ∀ a b : V, a≠b → ∃ c : V, ¬(G.Adj a c ↔ G.Adj b c) := by decide +kernel
theorem local_witness : ∀ u v : V, G.Adj u v → ∃ a b : V,
    G.Adj u a ∧ a≠v ∧ G.Adj v b ∧ b≠u ∧ (a=b ∨ ¬G.Adj a b) := by decide +kernel
theorem left_covers : ∀ u v : V, G.Adj u v → u∈leftSide ∨ v∈leftSide := by decide +kernel
theorem endpoints : ∀ e : E, ∃ u v : V,
    G.Adj u v ∧ onRow e.val u=true ∧ onRow e.val v=true := by decide +kernel
theorem graph_pairs : ∀ u v : V, GraphFormula9796.graph (fun i => decide (i=u ∨ i=v))=true ↔ G.Adj u v := by decide +kernel

theorem monotone_lower (C : Circuit) (hm : Monotone2 C) (hc : correct C) : 35≤C.size := by
  have bound := PEqualNP.Outside.L_meta_3049 24 12 G C no_isolates
    (fun u v ne _ _ _ => distinct_neighborhoods u v ne)
    (fun u v uv _ _ => local_witness u v uv)
    ⟨leftSide,fun u v uv _ _ => left_covers u v uv, by decide +kernel⟩
    (fun S cover => matching_cover S (by
      intro e
      obtain ⟨u,v,uv,hu,hv⟩ := endpoints e
      rcases cover u v uv (degree_ge_two u) (degree_ge_two v) with h|h
      · exact ⟨u,h,hu⟩
      · exact ⟨v,h,hv⟩))
    hm (fun u v => (hc _).trans ((GraphFormula9796.graph_iff _).symm.trans (graph_pairs u v)))
  omega
end GraphMatching9796

#print axioms GraphFormula9796.optimum_in_class
#print axioms GraphFormula9796.expanded_lower
#print axioms GraphClean9796.Trace.filtering_path_required
#print axioms GraphElimination9796.unrestricted_lower
#print axioms GraphMatching9796.monotone_lower
