import Mathlib.Tactic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.Forall2
import PEqualNP.Defs

-- Exact 59-row Heawood instance, L-meta-4602.
-- clean_lower proves that 27 gates are necessary if no AND gate fires on a
-- maximal independent set. optimum certifies an attaining clean circuit.
-- loss_tradeoff shows that zeroing all such AND gates of any 26-gate solution
-- must destroy at least two of the 21 single-edge positives.
-- sufficient_splits and pair_bound are independent lower bounds on AND/OR counts.
-- heawood_one_more_gate meets the posted crossed-output condition at 27 gates.

namespace HeawoodCrossing
abbrev Word := BitVec 59
abbrev Gate := Bool × Fin 40 × Fin 40
abbrev Event := Bool × Word × Word
def combine (op : Bool) (a b : Word) : Word :=
  if op = true then a ||| b else a &&& b
def step (xs : List Word) (g : Gate) : List Word :=
  xs ++ [combine g.1 (xs.getD g.2.1.val 0) (xs.getD g.2.2.val 0)]
def trace (xs : List Word) : List Gate → List Event
  | [] => []
  | g :: gs => (g.1, xs.getD g.2.1.val 0, xs.getD g.2.2.val 0) :: trace (step xs g) gs
def bad (p : Bool) (i j k : Nat) (w : Word) : Prop :=
  w.getLsbD i = p ∧ w.getLsbD j = p ∧ w.getLsbD k = !p
def crossed (p : Bool) (i j k : Nat) (e : Event) : Prop :=
  e.1 = p ∧ e.2.1.getLsbD i ≠ e.2.2.getLsbD i ∧
  e.2.1.getLsbD i = e.2.2.getLsbD j ∧ e.2.2.getLsbD i = e.2.1.getLsbD j ∧
  e.2.1.getLsbD k = !p ∧ e.2.2.getLsbD k = !p

theorem local_cross (p op : Bool) (i j k : Nat) (a b : Word)
    (ha : ¬ bad p i j k a) (hb : ¬ bad p i j k b)
    (hout : bad p i j k (combine op a b)) : crossed p i j k (op,a,b) := by
  unfold bad at ha hb hout
  unfold crossed
  cases op <;> simp [combine, BitVec.getLsbD_or, BitVec.getLsbD_and] at hout ⊢ <;>
    cases p <;> cases hai : a.getLsbD i <;> cases haj : a.getLsbD j <;>
    cases hak : a.getLsbD k <;> cases hbi : b.getLsbD i <;>
    cases hbj : b.getLsbD j <;> cases hbk : b.getLsbD k <;>
    simp_all

theorem default_good (p : Bool) (i j k : Nat) : ¬ bad p i j k 0 := by
  cases p <;> simp [bad]

theorem clean_read {p i j k} {xs : List Word}
    (h : ∀ v ∈ xs, ¬ bad p i j k v) (a : Nat) : ¬ bad p i j k (xs.getD a 0) := by
  by_cases ha : a < xs.length
  · rw [List.getD_eq_getElem _ _ ha]
    exact h _ (List.getElem_mem ha)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact default_good p i j k

theorem first_cross {p i j k} (gs : List Gate) (xs : List Word)
    (start : ∀ v ∈ xs, ¬ bad p i j k v)
    (finish : ∃ v ∈ gs.foldl step xs, bad p i j k v) :
    ∃ e ∈ trace xs gs, crossed p i j k e := by
  induction gs generalizing xs with
  | nil =>
    obtain ⟨v,hv,b⟩ := finish
    exact False.elim (start v hv b)
  | cons g gs ih =>
    let a := xs.getD g.2.1.val 0
    let b := xs.getD g.2.2.val 0
    by_cases fresh : bad p i j k (combine g.1 a b)
    · exact ⟨_,List.Mem.head _,local_cross _ _ _ _ _ a b
          (clean_read start _) (clean_read start _) fresh⟩
    · have clean : ∀ v ∈ step xs g, ¬ bad p i j k v := by
        intro v hv
        rcases List.mem_append.mp hv with hv|hv
        · exact start v hv
        · have hve := List.mem_singleton.mp hv
          subst v
          exact fresh
      obtain ⟨e,he,hc⟩ := ih (step xs g) clean finish
      exact ⟨e,List.Mem.tail _ he,hc⟩

end HeawoodCrossing

namespace HeawoodCrossing
def input : List Word := [95229015649944073, 63038587928642, 256463372304, 4292497062825988, 8521482511360, 14003410187716736, 55389823206179104, 189297016294080519, 155696362464215096, 218994303131713984, 183565875465424384, 229736628136996864, 270286071508729856, 288160007409369088]
def goal : Word := 2097151

def admissible (p : Bool) (i j k : Nat) : Bool :=
  input.all fun w => !(w.getLsbD i == p && w.getLsbD j == p && w.getLsbD k == !p)
theorem good_inputs (p i j k) (h : admissible p i j k=true) :
    ∀ w ∈ input, ¬ bad p i j k w := by
  intro w hw b
  have chk := List.all_eq_true.mp h w hw
  rcases b with ⟨h₁,h₂,h₃⟩
  simp [h₁,h₂,h₃] at chk

def observed (gs : List Gate) (a b : Fin 39) (op : Bool) : List Event :=
  trace input (gs ++ [(op, a.castSucc, b.castSucc)])

theorem all_crossings (gs : List Gate) (a b : Fin 39) (op : Bool)
    (hit : combine op ((gs.foldl step input).getD a.val 0)
                       ((gs.foldl step input).getD b.val 0) = goal)
    (p i j k) (h : admissible p i j k = true) (goalBad : bad p i j k goal) :
    ∃ e ∈ observed gs a b op, crossed p i j k e := by
  apply first_cross _ _ (good_inputs _ _ _ _ h)
  refine ⟨goal,?_,goalBad⟩
  rw [List.foldl_append]
  exact List.mem_append_right _ (List.mem_singleton.mpr hit.symm)

def events (p : Bool) (es : List Event) := es.filter fun e => e.1 == p
def bitcode (es : List Event) (r : Nat) (i : Fin es.length) : Bool :=
  es[i].2.1.getLsbD r

theorem code_separates (p : Bool) (es : List Event) (i j k : Nat)
    (h : ∃ e ∈ es, crossed p i j k e) :
    bitcode (events p es) i ≠ bitcode (events p es) j := by
  obtain ⟨e,he,hp,hd,_,hs,_⟩ := h
  have mem : e ∈ events p es := List.mem_filter.mpr ⟨he,by simp [hp]⟩
  obtain ⟨n,hn,atn⟩ := List.mem_iff_getElem.mp mem
  intro same
  have eq := congrFun same ⟨n,hn⟩
  change (events p es)[n].2.1.getLsbD i = (events p es)[n].2.1.getLsbD j at eq
  rw [atn] at eq
  exact hd (eq.trans hs.symm)

def rpos (i : Fin 21) := i.val
def rneg (i : Fin 37) := i.val+21

def comparison (p : Bool) (i j k : Nat) : Bool :=
  admissible p i j k && (goal.getLsbD i == p && goal.getLsbD j == p && goal.getLsbD k == !p)

theorem yields_bad (p i j k) (h : comparison p i j k=true) :
    admissible p i j k=true ∧ bad p i j k goal := by
  simpa [comparison,bad,and_assoc] using h

def verNeg : Bool :=
  (List.finRange 37).all fun i => (List.finRange 37).all fun j =>
    i == j || (List.finRange 21).any fun k => comparison false (rneg i) (rneg j) (rpos k)
def verPos : Bool :=
  (List.finRange 21).all fun i => (List.finRange 21).all fun j =>
    i == j || (List.finRange 37).any fun k => comparison true (rpos i) (rpos j) (rneg k)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem coverage : verNeg=true ∧ verPos=true := by decide +kernel

theorem sufficient_splits (gs : List Gate) (a b : Fin 39) (op : Bool)
    (hit : combine op ((gs.foldl step input).getD a.val 0)
                       ((gs.foldl step input).getD b.val 0) = goal) :
    let es := observed gs a b op
    6 ≤ (events false es).length ∧ 5 ≤ (events true es).length := by
  let es := observed gs a b op
  have separate (p : Bool) (i j k : Nat) (hc : comparison p i j k = true) :
      bitcode (events p es) i ≠ bitcode (events p es) j := by
    obtain ⟨ha,hb⟩ := yields_bad p i j k hc
    exact code_separates p es i j k (all_crossings gs a b op hit _ _ _ _ ha hb)
  have count {m n : Nat} (p : Bool) (r : Fin m → Nat) (s : Fin n → Nat)
      (cert : (List.finRange m).all (fun i => (List.finRange m).all fun j =>
          i == j || (List.finRange n).any fun k => comparison p (r i) (r j) (s k)) = true) :
      m ≤ 2 ^ (events p es).length := by
    have inj : Function.Injective (fun i : Fin m => bitcode (events p es) (r i)) := by
      intro i j same
      by_contra ne
      have q := List.all_eq_true.mp (List.all_eq_true.mp cert i (List.mem_finRange i)) j (List.mem_finRange j)
      simp only [beq_eq_false_iff_ne.mpr ne,Bool.false_or] at q
      obtain ⟨k,_,hk⟩ := List.any_eq_true.mp q
      exact separate p _ _ _ hk same
    simpa using Fintype.card_le_of_injective _ inj
  have ha := count false rneg rpos coverage.1
  have ho := count true rpos rneg coverage.2
  change 6 ≤ (events false es).length ∧ 5 ≤ (events true es).length
  constructor
  · by_contra! h
    have hh : 2^(events false es).length ≤ 2^5 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · by_contra! h
    have hh : 2^(events true es).length ≤ 2^4 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
end HeawoodCrossing

namespace HeawoodCrossing
def negBit (w : Word) (r : Fin 37) := w.getLsbD (rneg r)
def varWord (v : Fin 14) := input.getD v.val 0
def absent (v : Fin 14) (r : Fin 37) := !(negBit (varWord v) r)
def zeros (v w : Fin 14) := Finset.univ.filter fun r : Fin 37 => absent v r && absent w r
def adjacent (v w : Fin 14) : Bool :=
  (List.finRange 21).any fun e =>
    (varWord v).getLsbD (rpos e) && (varWord w).getLsbD (rpos e) && v != w

def pinned (e : Event) (v : Fin 14) : Prop :=
  (∀ r, absent v r = true → negBit e.2.1 r = false) ∨
  (∀ r, absent v r = true → negBit e.2.2 r = false)

theorem raw_pinned (e : Event) (v : Fin 14)
    (h : e.2.1 = varWord v ∨ e.2.2 = varWord v) : pinned e v := by
  rcases h with h|h
  · left; intro r hr; simpa [h,absent] using hr
  · right; intro r hr; simpa [h,absent] using hr

theorem excluded (e : Event) (v : Fin 14) (h : pinned e v) (i j : Fin 37)
    (hi : absent v i=true) (hj : absent v j=true) (k : Nat) :
    ¬ crossed false (rneg i) (rneg j) k e := by
  rintro ⟨_,d,a,b,_,_⟩
  rcases h with h|h
  · have h₁ := h i hi
    have h₂ := h j hj
    exact d (h₁.trans (h₂.symm.trans b.symm))
  · have h₁ := h i hi
    have h₂ := h j hj
    exact d (a.trans (h₂.trans h₁.symm))

theorem at_least_seventeen : ∀ v w : Fin 14, adjacent v w = false → 17 ≤ (zeros v w).card := by
  decide +kernel

theorem no_triangle : ∀ a b c : Fin 14,
    adjacent a b = true → adjacent b c = true → adjacent a c = false := by decide +kernel

theorem no_square : ∀ a b c d : Fin 14, a ≠ b → c ≠ d →
    adjacent a c = true → adjacent a d = true →
    adjacent b c = true → adjacent b d = false := by decide +kernel

theorem pair_bound (gs : List Gate) (a b : Fin 39) (op : Bool)
    (hit : combine op ((gs.foldl step input).getD a.val 0)
                       ((gs.foldl step input).getD b.val 0) = goal)
    (u v : Event) (rest : List Event)
    (hp : (events false (observed gs a b op)).Perm (u::v::rest))
    (x y : Fin 14) (px : pinned u x) (py : pinned v y)
    (nonedge : adjacent x y=false) :
    7 ≤ (events false (observed gs a b op)).length := by
  let Z := zeros x y
  have inject : Function.Injective (fun r : Z => bitcode rest (rneg r.val)) := by
    intro r s same
    by_contra ne
    have diff : r.val ≠ s.val := fun eq => ne (Subtype.ext eq)
    have q := List.all_eq_true.mp (List.all_eq_true.mp coverage.1 r.val (List.mem_finRange _))
      s.val (List.mem_finRange _)
    simp only [beq_eq_false_iff_ne.mpr diff,Bool.false_or] at q
    obtain ⟨k,_,hk⟩ := List.any_eq_true.mp q
    obtain ⟨hc,hbad⟩ := yields_bad _ _ _ _ hk
    obtain ⟨e,he,hcross⟩ := all_crossings gs a b op hit _ _ _ _ hc hbad
    have hf : e ∈ events false (observed gs a b op) :=
      List.mem_filter.mpr ⟨he,by simp [hcross.1]⟩
    have hr : absent x r.val=true ∧ absent y r.val=true := by
      simpa [zeros,Z] using r.property
    have hs : absent x s.val=true ∧ absent y s.val=true := by
      simpa [zeros,Z] using s.property
    have unused := hp.mem_iff.mp hf
    simp only [List.mem_cons] at unused
    rcases unused with rfl|rfl|remain
    · exact excluded _ x px _ _ hr.1 hs.1 _ hcross
    · exact excluded _ y py _ _ hr.2 hs.2 _ hcross
    · obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp remain
      have heq := congrFun same ⟨i,hi⟩
      change rest[i].2.1.getLsbD (rneg r.val) = rest[i].2.1.getLsbD (rneg s.val) at heq
      rw [eq] at heq
      exact hcross.2.1 (heq.trans hcross.2.2.2.1.symm)
  have size : Z.card ≤ 2^rest.length := by simpa using Fintype.card_le_of_injective _ inject
  have hmin := at_least_seventeen x y nonedge
  have hlen := hp.length_eq
  simp only [List.length_cons] at hlen
  change (zeros x y).card ≤ 2^rest.length at size
  by_contra! h
  have bound : 2^rest.length ≤ 2^4 := Nat.pow_le_pow_right (by decide) (by omega)
  omega

end HeawoodCrossing

namespace UnionBudget
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
end UnionBudget

namespace HeawoodClean
open HeawoodCrossing
abbrev V := Fin 14
abbrev E := Fin 21
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

theorem adj_iff_neg (u v : V) :
    adjacent u v=true ↔ ∀ k : Fin 37, ¬ (onRow (rneg k) u=true ∧ onRow (rneg k) v=true) := by
  revert u v
  decide +kernel

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

def matched : Fin 7 → E := ![0, 6, 4, 16, 20, 11, 14]
theorem disjoint_matching : ∀ i j : Fin 7, ∀ v : V,
    onRow (matched i).val v=true → onRow (matched j).val v=true → i=j := by decide +kernel
theorem matching_cover (X : R) (h : ∀ e : E, Hits X e.val) : 7≤X.card := by
  classical
  have representatives (i : Fin 7) : ∃ v : X, onRow (matched i).val v.val=true := by
    obtain ⟨v,hv,hon⟩ := h (matched i)
    exact ⟨⟨v,hv⟩,hon⟩
  choose f hf using representatives
  have inj : Function.Injective f := by
    intro i j eq
    exact disjoint_matching i j (f i).val (hf i) (eq.symm ▸ hf j)
  simpa using Fintype.card_le_of_injective _ inj

theorem raw_alive : ∀ v : V, ∃ r : Fin 37, onRow (rneg r) v=true := by decide +kernel
theorem target_pos : ∀ e : E, goal.getLsbD e.val=true := by decide +kernel
theorem target_neg : ∀ r : Fin 37, goal.getLsbD (rneg r)=false := by decide +kernel
end HeawoodClean

namespace HeawoodClean
open HeawoodCrossing UnionBudget
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
end HeawoodClean

namespace HeawoodClean
open HeawoodCrossing UnionBudget

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

def clean (w : Word) : Prop := ∀ k : Fin 37, w.getLsbD (rneg k)=false

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
end HeawoodClean

namespace HeawoodClean
open HeawoodCrossing UnionBudget
def CleanTrace (xs : List Word) (gs : List Gate) : Prop :=
  ∀ e ∈ trace xs gs, e.1=false → clean (e.2.1 &&& e.2.2)

theorem ready_read {s r l t} (B : Budget s r l t) {xs : List Word}
    (old : ∀ w∈xs, Ready s w) (i : Nat) : Ready s (xs.getD i 0) := by
  by_cases hi : i < xs.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact old _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact ⟨_,zero_wire B⟩

theorem program (gs : List Gate) (xs : List Word) (s : Pool) (r l t : Nat)
    (B : Budget s r l t) (old : ∀ w∈xs, Ready s w) (cleaned : CleanTrace xs gs) :
    ∃ z r' l' t', Budget z r' l' t' ∧ r'+l'+t'=r+l+t+gs.length ∧
      ∀ w∈gs.foldl step xs, Ready z w := by
  induction gs generalizing xs s r l t with
  | nil => exact ⟨s,r,l,t,B,by simp,old⟩
  | cons g gs ih =>
    let a := xs.getD g.2.1.val 0
    let b := xs.getD g.2.2.val 0
    obtain ⟨X,hX⟩ := ready_read B old g.2.1.val
    obtain ⟨Y,hY⟩ := ready_read B old g.2.2.val
    have advance : Advance s r l t (combine g.1 a b) := by
      cases hg : g.1 with
      | true => exact or_step B hX hY
      | false => exact and_step B hX hY (cleaned (g.1,a,b) (List.Mem.head _) hg)
    obtain ⟨z,r',l',t',Bigger,B',sum,new⟩ := advance
    have nextReady : ∀ w∈step xs g, Ready z w := by
      intro w hw
      rcases List.mem_append.mp hw with hw|hw
      · obtain ⟨T,hT⟩ := old w hw
        exact ⟨_,widen Bigger hT⟩
      · have eq := List.mem_singleton.mp hw
        exact eq ▸ new
    have nextClean : CleanTrace (step xs g) gs :=
      fun e he hf => cleaned e (List.Mem.tail _ he) hf
    obtain ⟨final,R,L,T,done,size,get⟩ := ih _ _ _ _ _ B' nextReady nextClean
    exact ⟨final,R,L,T,done,by simp only [List.length_cons];omega,get⟩

theorem output_lower {s r l t} (B : Budget s r l t) (h : Ready s goal) : 27 ≤ r+l+t := by
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

theorem raw_list : ∀ w∈input, ∃ v : V, w=varWord v := by
  have valid : input.all (fun w => (List.finRange 14).any fun v => w == varWord v)=true := by decide +kernel
  intro w hw
  obtain ⟨v,_,eq⟩ := List.any_eq_true.mp (List.all_eq_true.mp valid w hw)
  exact ⟨v,beq_iff_eq.mp eq⟩

theorem clean_lower (gs : List Gate) (cleaned : CleanTrace input gs)
    (hit : goal ∈ gs.foldl step input) : 27 ≤ gs.length := by
  have old : ∀ w∈input, Ready start w := by
    intro w hw
    obtain ⟨v,rfl⟩ := raw_list w hw
    exact ⟨_,input_wire startBudget v⟩
  obtain ⟨z,r,l,t,B,n,lookup⟩ := program gs input start 0 0 0 startBudget old cleaned
  have lim := output_lower B (lookup _ hit)
  omega

theorem must_misfire (gs : List Gate) (a b : Fin 39) (op : Bool) (n : gs.length≤25)
    (hit : combine op ((gs.foldl step input).getD a.val 0)
                      ((gs.foldl step input).getD b.val 0) = goal) :
    ∃ e∈trace input gs, e.1=false ∧ ∃ k : Fin 37,
      e.2.1.getLsbD (rneg k)=true ∧ e.2.2.getLsbD (rneg k)=true := by
  classical
  by_contra! absent
  let finish : Gate := (op,a.castSucc,b.castSucc)
  have prior : CleanTrace input gs := by
    intro e he hfalse k
    specialize absent e he hfalse k
    cases h : e.2.1.getLsbD (rneg k) <;> simp_all
  have trace_append (xs : List Word) (pre rest : List Gate) :
      trace xs (pre++rest)=trace xs pre ++ trace (pre.foldl step xs) rest := by
    induction pre generalizing xs with
    | nil => rfl
    | cons g gs ih => simp [trace,ih]
  have cleanAll : CleanTrace input (gs++[finish]) := by
    intro e he hop
    rw [trace_append] at he
    rcases List.mem_append.mp he with old|last
    · exact prior e old hop
    · simp only [trace,List.mem_singleton] at last
      subst e
      change op=false at hop
      subst op
      intro k
      change ((gs.foldl step input).getD a.val 0 &&& (gs.foldl step input).getD b.val 0).getLsbD (rneg k)=false
      change (gs.foldl step input).getD a.val 0 &&& (gs.foldl step input).getD b.val 0 = goal at hit
      rw [hit,target_neg]
  have target : goal ∈ (gs++[finish]).foldl step input := by
    rw [List.foldl_append]
    exact List.mem_append_right _ (List.mem_singleton.mpr hit.symm)
  have lower := clean_lower _ cleanAll target
  simp only [List.length_append,List.length_singleton] at lower
  omega
end HeawoodClean

namespace HeawoodClean
open HeawoodCrossing
def subword (x y : Word) := ∀ r, x.getLsbD r=true → y.getLsbD r=true
theorem sub_refl (x : Word) : subword x x := fun _ h => h
theorem sub_zero (x : Word) : subword 0 x := by simp [subword]
theorem sub_op (p : Bool) {x y a b : Word} (h : subword x a) (k : subword y b) :
    subword (combine p x y) (combine p a b) := by
  intro r hr
  cases p
  · have both : x.getLsbD r=true ∧ y.getLsbD r=true := by simpa [combine] using hr
    simp [combine,h _ both.1,k _ both.2]
  · have either : x.getLsbD r=true ∨ y.getLsbD r=true := by simpa [combine] using hr
    rcases either with ht|ht
    · simp [combine,h _ ht]
    · simp [combine,k _ ht]

theorem sub_read {xs ys : List Word} (h : List.Forall₂ subword xs ys) (i : Nat) :
    subword (xs.getD i 0) (ys.getD i 0) := by
  by_cases hi : i<xs.length
  · have hj : i<ys.length := h.length_eq ▸ hi
    rw [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj]
    exact h.get hi hj
  · have len := h.length_eq
    rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
    exact sub_refl _

def value (xs : List Word) (g : Gate) :=
  combine g.1 (xs.getD g.2.1.val 0) (xs.getD g.2.2.val 0)
def altered (xs : List Word) (g : Gate) : Gate :=
  if g.1 || (List.finRange 37).all (fun r => !(value xs g).getLsbD (rneg r)) then g
  else (false,39,39)
def rewriteGates (xs : List Word) : List Gate → List Gate
  | [] => []
  | g::gs => altered xs g :: rewriteGates (step xs g) gs

theorem edited_len (xs : List Word) (gs : List Gate) :
    (rewriteGates xs gs).length=gs.length := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih => simp [rewriteGates,ih]

theorem edit_one {xs ys : List Word} (rel : List.Forall₂ subword xs ys) (len : xs.length≤39)
    (g : Gate) :
    ( (altered ys g).1=false → clean (value xs (altered ys g))) ∧
    List.Forall₂ subword (step xs (altered ys g)) (step ys g) := by
  have sub : subword (value xs g) (value ys g) := sub_op _ (sub_read rel _) (sub_read rel _)
  have append {gg : Gate} (v : subword (value xs gg) (value ys g)) :
      List.Forall₂ subword (step xs gg) (step ys g) := List.rel_append rel (.cons v .nil)
  unfold altered
  split
  next h =>
    refine ⟨?_,append sub⟩
    intro hg r
    rw [hg,Bool.false_or] at h
    have no : (value ys g).getLsbD (rneg r)=false := by
      simpa using List.all_eq_true.mp h r (List.mem_finRange r)
    cases yes : (value xs g).getLsbD (rneg r)
    · rfl
    · exact (sub _ yes).symm.trans no
  next _ =>
    have zero : value xs (false,39,39)=0 := by
      change xs.getD 39 0 &&& xs.getD 39 0 = 0
      rw [List.getD_eq_default _ _ len]
      rfl
    exact ⟨fun _ r => by simp [zero],append (zero ▸ sub_zero _)⟩

theorem edit_run (gs : List Gate) (xs ys : List Word) (rel : List.Forall₂ subword xs ys)
    (len : xs.length+gs.length≤40) :
    CleanTrace xs (rewriteGates ys gs) ∧
    List.Forall₂ subword ((rewriteGates ys gs).foldl step xs) (gs.foldl step ys) := by
  induction gs generalizing xs ys with
  | nil => exact ⟨by simp [CleanTrace,trace,rewriteGates],rel⟩
  | cons g gs ih =>
    have lim : xs.length≤39 := by simp only [List.length_cons] at len;omega
    obtain ⟨cleanOne,next⟩ := edit_one rel lim g
    have nextLen : (step xs (altered ys g)).length+gs.length≤40 := by
      simp [step] at len ⊢;omega
    obtain ⟨ct,rt⟩ := ih _ _ next nextLen
    refine ⟨?_,rt⟩
    intro e mem hf
    rcases List.mem_cons.mp mem with h|rest
    · subst e
      change (altered ys g).1=false at hf
      have good := cleanOne hf
      simpa [value,combine,hf] using good
    · exact ct e rest hf

theorem lost_positive (gs : List Gate) (i : Nat) (n : gs.length≤26)
    (hit : (gs.foldl step input).getD i 0 = goal) :
    ∃ e : E, (((rewriteGates input gs).foldl step input).getD i 0).getLsbD e.val=false := by
  classical
  have self : List.Forall₂ subword input input := List.forall₂_of_length_eq_of_get rfl
    (fun _ _ _ => sub_refl _)
  have len : input.length+gs.length≤40 := by have x : input.length=14 := rfl;omega
  obtain ⟨isClean,rel⟩ := edit_run gs input input self len
  let wires := (rewriteGates input gs).foldl step input
  have below := sub_read rel i
  rw [hit] at below
  by_contra! allPos
  have equalsGoal : wires.getD i 0 = goal := by
    apply BitVec.eq_of_getLsbD_eq
    intro r hr
    by_cases hi : r<21
    · have y := allPos (⟨r,hi⟩ : E)
      simpa [target_pos ⟨r,hi⟩] using (show (wires.getD i 0).getLsbD r = true from Bool.eq_true_of_not_eq_false y)
    · have high : ∀ k : Fin 59, 21≤k.val → goal.getLsbD k.val=false := by decide +kernel
      have f : goal.getLsbD r=false := high ⟨r,hr⟩ (show 21≤r from by omega)
      rw [f]
      cases y : (wires.getD i 0).getLsbD r
      · rfl
      · exact (below _ y).symm.trans f
  have member : goal ∈ wires := by
    by_cases ok : i<wires.length
    · rw [←equalsGoal,List.getD_eq_getElem _ _ ok]
      exact List.getElem_mem ok
    · rw [List.getD_eq_default _ _ (by omega)] at equalsGoal
      have nz : goal≠0 := by decide
      exact False.elim (nz equalsGoal.symm)
  have bound := clean_lower (rewriteGates input gs) isClean member
  rw [edited_len] at bound
  omega
end HeawoodClean

namespace HeawoodClean
open HeawoodCrossing UnionBudget
def positives (w : Word) : Finset E := Finset.univ.filter fun e => w.getLsbD e.val
def incident (v : V) : Finset E := positives (varWord v)

theorem regular : ∀ v : V, (incident v).card=3 := by decide +kernel

theorem covered_card (X : R) : (X.biUnion incident).card ≤ 3*X.card := by
  induction X using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.biUnion_insert,Finset.card_insert_of_notMem ha]
    have u := Finset.card_union_le (incident a) (S.biUnion incident)
    rw [regular] at u
    omega

theorem sparse_budget {s r l t} (B : Budget s r l t) (v : Word) (safe : clean v)
    (h : Ready s v) : 4*(positives v).card ≤ 3*(r+l+t+1) := by
  obtain ⟨X,w⟩ := h
  have emp : X=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    obtain ⟨k,hk⟩ := raw_alive u
    have yes := w.rawSound _ ⟨u,hu,hk⟩
    rw [safe k] at yes
    contradiction
  subst X
  obtain ⟨P,hp,dom⟩ := w.cover (by simp)
  have x1 : positives v ⊆ blocks s := by
    intro e he
    have on : v.getLsbD e.val=true := (Finset.mem_filter.mp he).2
    simpa [Hits] using w.origin e on
  have x2 : positives v ⊆ P.biUnion incident := by
    intro e he
    obtain ⟨u,hu,b⟩ := dom e (Finset.mem_filter.mp he).2
    exact Finset.mem_biUnion.mpr ⟨u,hu,Finset.mem_filter.mpr ⟨Finset.mem_univ _,b⟩⟩
  have a := (Finset.card_le_card x1).trans (B.richCost s.claimed B.covers)
  have b := (Finset.card_le_card x2).trans (covered_card P)
  have c := one B.lightCost hp
  have d := B.claimCost
  omega

def charged (xs : List Word) : List Gate → Nat
  | [] => 0
  | g::gs => (if value xs g=0 then 0 else 1) + charged (step xs g) gs

set_option maxHeartbeats 900000 in
theorem paid_program (gs : List Gate) (xs : List Word) (s : Pool) (r l t : Nat)
    (B : Budget s r l t) (old : ∀ w∈xs, Ready s w) (cleaned : CleanTrace xs gs) :
    ∃ z r' l' t', Budget z r' l' t' ∧ r'+l'+t'=r+l+t+charged xs gs ∧
      ∀ w∈gs.foldl step xs, Ready z w := by
  induction gs generalizing xs s r l t with
  | nil => exact ⟨s,r,l,t,B,by simp [charged],old⟩
  | cons g gs ih =>
    have nextClean : CleanTrace (step xs g) gs :=
      fun e he hf => cleaned e (List.Mem.tail _ he) hf
    by_cases free : value xs g=0
    · have newReady : ∀ w∈step xs g, Ready s w := by
        intro w hw
        rcases List.mem_append.mp hw with h|h
        · exact old _ h
        · have eq : w=value xs g := List.mem_singleton.mp h
          rw [eq,free]
          exact ⟨_,zero_wire B⟩
      obtain ⟨z,R,L,T,done,size,get⟩ := ih _ _ _ _ _ B newReady nextClean
      exact ⟨z,R,L,T,done,by simpa [charged,free] using size,get⟩
    · obtain ⟨X,hX⟩ := ready_read B old g.2.1.val
      obtain ⟨Y,hY⟩ := ready_read B old g.2.2.val
      have advance : Advance s r l t (value xs g) := by
        unfold value
        cases hg : g.1 with
        | true => exact or_step B hX hY
        | false => exact and_step B hX hY (cleaned (g.1,xs.getD g.2.1.val 0,xs.getD g.2.2.val 0) (List.Mem.head _) hg)
      obtain ⟨z,R,L,T,ext,bud,sum,new⟩ := advance
      have newReady : ∀ w∈step xs g, Ready z w := by
        intro w hw
        rcases List.mem_append.mp hw with h|h
        · obtain ⟨Y,prev⟩ := old w h
          exact ⟨_,widen ext prev⟩
        · exact (List.mem_singleton.mp h) ▸ new
      obtain ⟨z',R',L',T',done,size,get⟩ := ih _ _ _ _ _ bud newReady nextClean
      refine ⟨z',R',L',T',done,?_,get⟩
      simp only [charged,ite_eq_right free];omega

def marked (xs : List Word) (g : Gate) : Bool :=
  !(g.1 || (List.finRange 37).all (fun r => !(value xs g).getLsbD (rneg r)))
def countMarked (xs : List Word) : List Gate → Nat
  | [] => 0
  | g::gs => (if marked xs g then 1 else 0) + countMarked (step xs g) gs

theorem count_zero_nochange (gs : List Gate) (xs : List Word) (h : countMarked xs gs=0) :
    rewriteGates xs gs=gs := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    simp only [countMarked,Nat.add_eq_zero_iff] at h
    have keep : marked xs g=false := by cases e : marked xs g <;> simp_all
    have on : altered xs g=g := by simpa [marked,altered] using
        (show (if !(marked xs g) then g else (false,39,39))=g by simp [keep])
    simp [rewriteGates,on,ih _ h.2]

theorem charge_erased (xs ys : List Word) (gs : List Gate) (len : xs.length+gs.length≤40) :
    charged xs (rewriteGates ys gs) + countMarked ys gs ≤ gs.length := by
  induction gs generalizing xs ys with
  | nil => simp [rewriteGates,charged,countMarked]
  | cons g gs ih =>
    let h := altered ys g
    have upper : xs.length≤39 := by simp only [List.length_cons] at len;omega
    have nextLen : (step xs h).length+gs.length≤40 := by simp [step] at len ⊢;omega
    have bound := ih (step xs h) (step ys g) nextLen
    change charged (step xs (altered ys g)) (rewriteGates (step ys g) gs) + _ ≤ _ at bound
    simp only [rewriteGates,charged,countMarked,List.length_cons]
    cases eq : marked ys g with
    | false => simp only [Bool.false_eq_true,ite_false,zero_add];split <;> omega
    | true =>
      have off : altered ys g=(false,39,39) := by
        unfold altered
        have zero : (g.1 || (List.finRange 37).all (fun r => !(value ys g).getLsbD (rneg r)))=false := by
          simpa [marked] using eq
        simp [zero]
      have out : value xs (altered ys g)=0 := by
        rw [off]
        change xs.getD 39 0 &&& xs.getD 39 0 = 0
        rw [List.getD_eq_default _ _ upper];rfl
      simp only [out,zero_add,↓reduceIte];omega

theorem loss_tradeoff (gs : List Gate) (i : Nat) (n : gs.length≤26)
    (hit : (gs.foldl step input).getD i 0=goal) :
    let cleanedWord := ((rewriteGates input gs).foldl step input).getD i 0
    4*(positives cleanedWord).card + 3*countMarked input gs ≤ 3*(gs.length+1) ∧
      (positives cleanedWord).card ≤ 19 := by
  have self : List.Forall₂ subword input input := List.forall₂_of_length_eq_of_get rfl
    (fun _ _ _ => sub_refl _)
  have len : input.length+gs.length≤40 := by have x : input.length=14 := rfl;omega
  obtain ⟨cs,rel⟩ := edit_run gs input input self len
  have below := sub_read rel i
  rw [hit] at below
  have safe : clean (((rewriteGates input gs).foldl step input).getD i 0) := by
    intro k
    cases eq : (((rewriteGates input gs).foldl step input).getD i 0).getLsbD (rneg k)
    · rfl
    · exact (below _ eq).symm.trans (target_neg k)
  have old : ∀ w∈input, Ready start w := by
    intro w hw
    obtain ⟨v,rfl⟩ := raw_list w hw
    exact ⟨_,input_wire startBudget v⟩
  obtain ⟨z,r,l,t,B,total,lookup⟩ := paid_program _ _ _ _ _ _ startBudget old cs
  have sb := sparse_budget B _ safe (ready_read B lookup i)
  have ch := charge_erased input input gs len
  have markedSome : 0<countMarked input gs := by
    by_contra! hz
    have eq := count_zero_nochange gs input (by omega)
    obtain ⟨e,lost⟩ := lost_positive gs i n hit
    rw [eq,hit,target_pos e] at lost
    contradiction
  dsimp only
  constructor <;> omega
end HeawoodClean

namespace HeawoodClean
open HeawoodCrossing
def dirtySupport (xs : List Word) : List Gate → Finset E
  | [] => ∅
  | g::gs => (if marked xs g then positives (value xs g) else ∅) ∪ dirtySupport (step xs g) gs

def agreeAt (r : Nat) (a b : Word) := a.getLsbD r = b.getLsbD r
theorem agree_read {xs ys : List Word} (r : Nat) (eq : List.Forall₂ (agreeAt r) xs ys) (i : Nat) :
    agreeAt r (xs.getD i 0) (ys.getD i 0) := by
  by_cases ok : i<xs.length
  · have ok' : i<ys.length := eq.length_eq ▸ ok
    rw [List.getD_eq_getElem _ _ ok,List.getD_eq_getElem _ _ ok']
    exact eq.get ok ok'
  · have same := eq.length_eq
    rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
    rfl

theorem agree_run (gs : List Gate) (xs ys : List Word) (e : E)
    (h : List.Forall₂ (agreeAt e.val) xs ys) (len : xs.length+gs.length≤40)
    (miss : e∉dirtySupport ys gs) :
    List.Forall₂ (agreeAt e.val) ((rewriteGates ys gs).foldl step xs) (gs.foldl step ys) := by
  induction gs generalizing xs ys with
  | nil => exact h
  | cons g gs ih =>
    have lim : xs.length≤39 := by simp only [List.length_cons] at len;omega
    have htail : e∉dirtySupport (step ys g) gs := fun he => miss (Finset.mem_union_right _ he)
    have bits : agreeAt e.val (value xs (altered ys g)) (value ys g) := by
      unfold altered
      split
      next on =>
        have a := agree_read _ h g.2.1.val
        have b := agree_read _ h g.2.2.val
        unfold agreeAt at a b ⊢
        unfold value combine
        cases hg : g.1 <;> simp only [Bool.false_eq_true,↓reduceIte,BitVec.getLsbD_and,BitVec.getLsbD_or] <;> rw [a,b]
      next off =>
        have yes : marked ys g=true := by simp [marked,off]
        have n : e∉positives (value ys g) := by
          intro he
          apply miss
          apply Finset.mem_union_left
          simpa [yes] using he
        have no : (value ys g).getLsbD e.val=false := by simpa [positives] using n
        change (xs.getD 39 0 &&& xs.getD 39 0).getLsbD e.val = _
        rw [List.getD_eq_default _ _ lim,no]
        simp
    have advance : List.Forall₂ (agreeAt e.val) (step xs (altered ys g)) (step ys g) :=
      List.rel_append h (.cons bits .nil)
    exact ih _ _ advance (by simp [step] at len ⊢;omega) htail

theorem mixed_edges (gs : List Gate) (i : Nat) (n : gs.length≤26)
    (hit : (gs.foldl step input).getD i 0=goal) : 2 ≤ (dirtySupport input gs).card := by
  let cleanedWord := ((rewriteGates input gs).foldl step input).getD i 0
  have lower := (loss_tradeoff gs i n hit).2
  have all : (Finset.univ : Finset E) ⊆ positives cleanedWord ∪ dirtySupport input gs := by
    intro e _
    by_cases caught : e∈dirtySupport input gs
    · exact Finset.mem_union_right _ caught
    · have self : List.Forall₂ (agreeAt e.val) input input :=
        List.forall₂_of_length_eq_of_get rfl (fun _ _ _ => rfl)
      have len : input.length+gs.length≤40 := by have x : input.length=14 := rfl;omega
      have eq := agree_read _ (agree_run gs input input e self len caught) i
      unfold agreeAt at eq
      rw [hit,target_pos] at eq
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq⟩)
  have size := (Finset.card_le_card all).trans (Finset.card_union_le _ _)
  simp only [Finset.card_univ,Fintype.card_fin] at size
  change (positives cleanedWord).card≤19 at lower
  omega
end HeawoodClean

namespace HeawoodClean
open HeawoodCrossing
def optimalGates : List Gate := [(true, 7, 8), (true, 14, 10), (false, 0, 15), (true, 7, 9), (true, 17, 13), (false, 1, 18), (true, 8, 12), (true, 20, 13), (false, 2, 21), (true, 7, 11), (true, 23, 12), (false, 3, 24), (true, 10, 11), (true, 26, 13), (false, 4, 27), (true, 9, 10), (true, 29, 12), (false, 5, 30), (true, 8, 9), (true, 32, 11), (false, 6, 33), (true, 19, 22), (true, 35, 25), (true, 36, 28), (true, 37, 31), (true, 38, 34), (true, 16, 39)]
theorem optimum : CleanTrace input optimalGates ∧ optimalGates.length=27 ∧
    goal∈optimalGates.foldl step input := by
  constructor
  · have checked : (trace input optimalGates).all (fun e =>
        e.1 || (List.finRange 37).all (fun k => !(e.2.1 &&& e.2.2).getLsbD (rneg k)))=true := by decide +kernel
    intro e he hf k
    have v := List.all_eq_true.mp checked e he
    rw [hf,Bool.false_or] at v
    have ck := List.all_eq_true.mp v k (List.mem_finRange k)
    change (e.2.1 &&& e.2.2).getLsbD (rneg k)=false
    cases hz : (e.2.1 &&& e.2.2).getLsbD (rneg k) <;> simp_all only [Bool.not_true,Bool.false_eq_true]
  · decide +kernel
end HeawoodClean

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
theorem heawood_one_more_gate : have x1 : List (BitVec (59 : ℕ)) := [(95229015649944073 : BitVec (59 : ℕ)), (63038587928642 : BitVec (59 : ℕ)), (256463372304 : BitVec (59 : ℕ)), (4292497062825988 : BitVec (59 : ℕ)), (8521482511360 : BitVec (59 : ℕ)), (14003410187716736 : BitVec (59 : ℕ)), (55389823206179104 : BitVec (59 : ℕ)), (189297016294080519 : BitVec (59 : ℕ)), (155696362464215096 : BitVec (59 : ℕ)), (218994303131713984 : BitVec (59 : ℕ)), (183565875465424384 : BitVec (59 : ℕ)), (229736628136996864 : BitVec (59 : ℕ)), (270286071508729856 : BitVec (59 : ℕ)), (288160007409369088 : BitVec (59 : ℕ))]; have x2 : List ℕ := [(64 : ℕ), (256 : ℕ), (448 : ℕ), (1429 : ℕ), (1557 : ℕ), (2389 : ℕ), (3669 : ℕ), (1494 : ℕ), (1558 : ℕ), (1750 : ℕ), (1942 : ℕ), (2390 : ℕ), (2902 : ℕ), (1688 : ℕ), (1880 : ℕ), (2008 : ℕ)]; ∃ (x3 : List (Bool × Fin (40 : ℕ) × Fin (40 : ℕ))) (x4 : Fin (40 : ℕ)) (x5 : Fin (40 : ℕ)) (x6 : Fin (16 : ℕ)),   x3.length = (26 : ℕ) ∧     (14 : ℕ) ≤ ↑x4 ∧       x4 < x5 ∧         have x7 : ℕ := x2.getD ↑x6 (0 : ℕ);         have x8 : ℕ := x7 % (64 : ℕ);         have x9 : ℕ := x7 / (64 : ℕ);         have x10 : List (BitVec (59 : ℕ)) := List.foldl (fun (x10 : List (BitVec (59 : ℕ))) (x11 : Bool × Fin (40 : ℕ) × Fin (40 : ℕ)) => x10 ++ [if x11.1 = Bool.true then x10.getD ↑x11.2.1 (0 : BitVec (59 : ℕ)) ||| x10.getD ↑x11.2.2 (0 : BitVec (59 : ℕ)) else x10.getD ↑x11.2.1 (0 : BitVec (59 : ℕ)) &&& x10.getD ↑x11.2.2 (0 : BitVec (59 : ℕ))]) x1 x3;         have x11 : BitVec (59 : ℕ) := x10.getD ↑x4 (0 : BitVec (59 : ℕ));         have x12 : BitVec (59 : ℕ) := x10.getD ↑x5 (0 : BitVec (59 : ℕ));         (if x8 < (21 : ℕ) then x11 ||| x12 else x11 &&& x12) = (2097151 : BitVec (59 : ℕ)) ∧ x11.getLsbD x8 ≠ x12.getLsbD x8 ∧ x11.getLsbD x8 = x12.getLsbD x9 ∧ x12.getLsbD x8 = x11.getLsbD x9 := by
  dsimp only
  refine ⟨[(true, 7, 8), (true, 14, 10), (false, 0, 15), (true, 7, 9), (true, 17, 13), (false, 1, 18), (true, 8, 12), (true, 20, 13), (false, 2, 21), (true, 7, 11), (true, 23, 12), (false, 3, 24), (true, 10, 11), (true, 26, 13), (false, 4, 27), (true, 9, 10), (true, 29, 12), (false, 5, 30), (true, 8, 9), (true, 32, 11), (false, 6, 33), (true, 19, 22), (true, 35, 25), (true, 36, 28), (true, 37, 31), (true, 38, 34)], 16, 39, 0, ?_⟩
  decide +kernel

#print axioms HeawoodClean.clean_lower
#print axioms HeawoodClean.must_misfire
#print axioms HeawoodClean.loss_tradeoff
#print axioms HeawoodClean.mixed_edges
#print axioms HeawoodClean.optimum
#print axioms HeawoodCrossing.pair_bound
#print axioms heawood_one_more_gate
