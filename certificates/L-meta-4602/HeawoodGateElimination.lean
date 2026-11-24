import HeawoodCircuitBound

-- Gate elimination for the 59-row Heawood instance.
-- This companion uses the sibling source HeawoodCircuitBound.lean.
-- An AND that is true on any maximal independent set is marked.
-- reader_tradeoff shows that setting all marked gates to zero loses at least three edge rows.
-- If exactly one AND is marked, sole_violation_after_three excludes the first three positions.
-- excluded_union_operands also excludes two binary input disjunctions at any gate position.
-- star_advice and advice_bound are independent quantitative restrictions on arbitrary gate traces.

namespace HeawoodClean
open HeawoodCrossing UnionBudget
def novelCount (xs : List Word) : List Gate → Nat
  | [] => 0
  | g::gs => (if value xs g=0 ∨ value xs g∈xs then 0 else 1) + novelCount (step xs g) gs

set_option maxHeartbeats 900000 in
theorem novel_program (gs : List Gate) (xs : List Word) (s : Pool) (r l t : Nat)
    (B : Budget s r l t) (old : ∀ w∈xs, Ready s w) (cleaned : CleanTrace xs gs) :
    ∃ z r' l' t', Budget z r' l' t' ∧ r'+l'+t'=r+l+t+novelCount xs gs ∧
      ∀ w∈gs.foldl step xs, Ready z w := by
  induction gs generalizing xs s r l t with
  | nil => exact ⟨s,r,l,t,B,by simp [novelCount],old⟩
  | cons g gs ih =>
    have nextClean : CleanTrace (step xs g) gs :=
      fun e he hf => cleaned e (List.Mem.tail _ he) hf
    by_cases free : value xs g=0 ∨ value xs g∈xs
    · have newReady : ∀ w∈step xs g, Ready s w := by
        intro w hw
        rcases List.mem_append.mp hw with h|h
        · exact old _ h
        · have eq : w=value xs g := List.mem_singleton.mp h
          rw [eq]
          rcases free with fq|fm
          · rw [fq];exact ⟨_,zero_wire B⟩
          · exact old _ fm
      obtain ⟨z,R,L,T,done,size,get⟩ := ih _ _ _ _ _ B newReady nextClean
      exact ⟨z,R,L,T,done,by rw [novelCount,ite_eq_left free,zero_add];exact size,get⟩
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
      simp only [novelCount,ite_eq_right free];omega


end HeawoodClean

namespace HeawoodClean
open HeawoodCrossing UnionBudget

abbrev freeAt (xs : List Word) (g : Gate) := value xs g=0 ∨ value xs g∈xs
theorem mark_off {ys g} (h : marked ys g=true) : altered ys g=(false,39,39) := by
  unfold altered
  have off : (g.1 || (List.finRange 37).all (fun r => !(value ys g).getLsbD (rneg r)))=false := by simpa [marked] using h
  simp [off]
theorem mark_on {ys g} (h : marked ys g=false) : altered ys g=g := by
  unfold altered
  have on : (g.1 || (List.finRange 37).all (fun r => !(value ys g).getLsbD (rneg r)))=true := by
    have hh := h
    unfold marked at hh
    cases eq : (g.1 || (List.finRange 37).all (fun r => !(value ys g).getLsbD (rneg r))) <;> simp_all only [Bool.not_false,Bool.true_eq_false]
  simp [on]
theorem mark_dirty {ys g} (h : marked ys g=true) : ¬ clean (value ys g) := by
  intro c
  have yes : (List.finRange 37).all (fun r => !(value ys g).getLsbD (rneg r)) = true :=
    List.all_eq_true.mpr (fun r _ => by simp [c r])
  simp [marked,yes] at h
theorem dead_value {xs : List Word} (lim : xs.length≤39) :
    value xs (false,39,39)=0 := by
  change xs.getD 39 0 &&& xs.getD 39 0=0
  rw [List.getD_eq_default _ _ lim];rfl

def SameOrMarked (x y : Word) := x=y ∨ x=0 ∧ ¬clean y
theorem same_read {xs ys : List Word} (h : List.Forall₂ SameOrMarked xs ys) (i : Nat) :
    SameOrMarked (xs.getD i 0) (ys.getD i 0) := by
  by_cases ok : i<xs.length
  · have ok' : i<ys.length := h.length_eq ▸ ok
    rw [List.getD_eq_getElem _ _ ok,List.getD_eq_getElem _ _ ok'];exact h.get ok ok'
  · have same := h.length_eq
    rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
    exact Or.inl rfl

theorem read_free (xs : List Word) (j : Nat) : xs.getD j 0=0 ∨ xs.getD j 0∈xs := by
  by_cases h : j<xs.length
  · rw [List.getD_eq_getElem _ _ h];exact Or.inr (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)];exact Or.inl rfl

theorem zero_free {xs : List Word} {g : Gate} (h : xs.getD g.2.1.val 0=0 ∨ xs.getD g.2.2.val 0=0) :
    freeAt xs g := by
  have L₀ (x : Word) : combine false 0 x=0 := BitVec.zero_and
  have R₀ (x : Word) : combine false x 0=0 := BitVec.and_zero
  have L₁ (x : Word) : combine true 0 x=x := BitVec.zero_or
  have R₁ (x : Word) : combine true x 0=x := BitVec.or_zero
  unfold freeAt value
  rcases h with l|r
  · rw [l];cases g.1
    · exact Or.inl (L₀ _)
    · rw [L₁];exact read_free _ _
  · rw [r];cases g.1
    · exact Or.inl (R₀ _)
    · rw [R₁];exact read_free _ _

theorem charge_or_match (xs ys : List Word) (gs : List Gate) (len : xs.length+gs.length≤40)
    (rel : List.Forall₂ SameOrMarked xs ys) :
    let cost := novelCount xs (rewriteGates ys gs)+countMarked ys gs
    cost≤gs.length ∧ (cost=gs.length →
      List.Forall₂ SameOrMarked ((rewriteGates ys gs).foldl step xs) (gs.foldl step ys)) := by
  induction gs generalizing xs ys with
  | nil => exact ⟨by simp [novelCount,rewriteGates,countMarked],fun _ => rel⟩
  | cons g gs ih =>
    let h := altered ys g
    have lim : xs.length≤39 := by simp only [List.length_cons] at len;omega
    have ln : (step xs h).length+gs.length≤40 := by simp [step] at len ⊢;omega
    have plain : novelCount (step xs h) (rewriteGates (step ys g) gs)+countMarked (step ys g) gs≤gs.length := by
      have weak (ws : List Word) (ss : List Gate) : novelCount ws ss≤charged ws ss := by
        induction ss generalizing ws with
        | nil => rfl
        | cons k ks ik =>
          simp only [novelCount,charged]
          have q := ik (step ws k)
          by_cases zero : value ws k=0
          · rw [ite_eq_left (Or.inl zero),ite_eq_left zero];omega
          · rw [ite_eq_right zero]
            split <;> omega
      exact le_trans (Nat.add_le_add_right (weak _ _) _) (charge_erased _ _ _ ln)
    have combine_cost (z : Nat) (q : Nat) (localCost : z+q≤1)
        (localRel : z+q=1 → SameOrMarked (value xs h) (value ys g)) :
        z+novelCount (step xs h) (rewriteGates (step ys g) gs)+(q+countMarked (step ys g) gs)≤gs.length+1 ∧
        (z+novelCount (step xs h) (rewriteGates (step ys g) gs)+(q+countMarked (step ys g) gs)=gs.length+1 →
          List.Forall₂ SameOrMarked ((rewriteGates (step ys g) gs).foldl step (step xs h)) (gs.foldl step (step ys g))) := by
      refine ⟨by omega,?_⟩
      intro top
      have next : List.Forall₂ SameOrMarked (step xs h) (step ys g) := List.rel_append rel (.cons (localRel (by omega)) .nil)
      apply (ih (step xs h) (step ys g) ln next).2
      omega
    apply combine_cost (if freeAt xs h then 0 else 1) (if marked ys g then 1 else 0)
    · cases mk : marked ys g with
      | false => split <;> decide
      | true =>
        have zero : value xs h=0 := by dsimp [h];rw [mark_off mk];exact dead_value lim
        rw [ite_eq_left (show freeAt xs h from Or.inl zero)]
        decide
    · intro saturate
      cases mk : marked ys g with
      | true =>
        have zero : value xs h=0 := by dsimp [h];rw [mark_off mk];exact dead_value lim
        exact Or.inr ⟨zero,mark_dirty mk⟩
      | false =>
        have notFree : ¬freeAt xs h := by
          intro free
          simp only [ite_eq_left free,mk] at saturate
          contradiction
        have same : h=g := mark_on mk
        have a := same_read rel g.2.1.val
        have b := same_read rel g.2.2.val
        rw [same] at notFree ⊢
        rcases a with eq|bad
        · rcases b with eq'|bad
          · exact Or.inl (by simp only [value,eq,eq'])
          · exact False.elim (notFree (zero_free (Or.inr bad.1)))
        · exact False.elim (notFree (zero_free (Or.inl bad.1)))
end HeawoodClean
namespace HeawoodClean
open HeawoodCrossing UnionBudget
theorem reader_tradeoff (gs : List Gate) (i : Nat) (n : gs.length≤26)
    (hit : (gs.foldl step input).getD i 0=goal) :
    let w := ((rewriteGates input gs).foldl step input).getD i 0
    4*(positives w).card + 3*countMarked input gs ≤ 3*gs.length ∧ (positives w).card≤18 := by
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
  obtain ⟨z,r,l,t,B,total,lookup⟩ := novel_program _ _ _ _ _ _ startBudget old cs
  have sb := sparse_budget B _ safe (ready_read B lookup i)
  have zeroSome : 0<countMarked input gs := by
    by_contra! hz
    have eq := count_zero_nochange gs input (by omega)
    obtain ⟨e,lost⟩ := lost_positive gs i n hit
    rw [eq,hit,target_pos e] at lost
    contradiction
  have sr : List.Forall₂ SameOrMarked input input :=
    List.forall₂_of_length_eq_of_get rfl (fun _ _ _ => Or.inl rfl)
  obtain ⟨le,tie⟩ := charge_or_match input input gs len sr
  have nt : novelCount input (rewriteGates input gs)+countMarked input gs≠gs.length := by
    intro h
    have q := same_read (tie h) i
    rw [hit] at q
    obtain ⟨e,lost⟩ := lost_positive gs i n hit
    rcases q with eq|notclean
    · rw [eq,target_pos] at lost;contradiction
    · exact notclean.2 target_neg
  dsimp only;constructor <;> omega
end HeawoodClean

namespace HeawoodClean
open HeawoodCrossing
def improvement (T : Group) (x y : Word) : Prop :=
  (∀ e∈T, y.getLsbD e.val=true → x.getLsbD e.val=true) ∧
  (∀ k : Fin 37, x.getLsbD (rneg k)=true → y.getLsbD (rneg k)=true)
theorem imp_refl (T : Group) (x : Word) : improvement T x x := ⟨fun _ _ h => h,fun _ h => h⟩
theorem imp_read {T} {xs ys : List Word} (rel : List.Forall₂ (improvement T) xs ys) (i : Nat) :
    improvement T (xs.getD i 0) (ys.getD i 0) := by
  by_cases hi : i<xs.length
  · have hj : i<ys.length := rel.length_eq ▸ hi
    rw [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj]
    exact rel.get hi hj
  · have len := rel.length_eq
    rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
    exact imp_refl _ _
theorem imp_op {T x y a b} (op : Bool) (h : improvement T x y) (j : improvement T a b) :
    improvement T (combine op x a) (combine op y b) := by
  constructor
  · intro e mem yes
    cases op
    · have both : y.getLsbD e.val=true ∧ b.getLsbD e.val=true := by simpa [combine] using yes
      simp [combine,h.1 e mem both.1,j.1 e mem both.2]
    · have either : y.getLsbD e.val=true ∨ b.getLsbD e.val=true := by simpa [combine] using yes
      rcases either with z|z
      · simp [combine,h.1 e mem z]
      · simp [combine,j.1 e mem z]
  · intro k yes
    cases op
    · have both : x.getLsbD (rneg k)=true ∧ a.getLsbD (rneg k)=true := by simpa [combine] using yes
      simp [combine,h.2 k both.1,j.2 k both.2]
    · have either : x.getLsbD (rneg k)=true ∨ a.getLsbD (rneg k)=true := by simpa [combine] using yes
      rcases either with z|z
      · simp [combine,h.2 k z]
      · simp [combine,j.2 k z]
theorem imp_run {T} (xs ys : List Word) (gs : List Gate)
    (rel : List.Forall₂ (improvement T) xs ys) (orig : CleanTrace ys gs) :
    CleanTrace xs gs ∧ List.Forall₂ (improvement T) (gs.foldl step xs) (gs.foldl step ys) := by
  induction gs generalizing xs ys with
  | nil => exact ⟨by simp [CleanTrace,trace],rel⟩
  | cons g gs ih =>
    have le := imp_op g.1 (imp_read rel g.2.1.val) (imp_read rel g.2.2.val)
    have next : List.Forall₂ (improvement T) (step xs g) (step ys g) := List.rel_append rel (.cons le .nil)
    obtain ⟨ct,rt⟩ := ih _ _ next (fun e he hh => orig e (List.Mem.tail _ he) hh)
    refine ⟨?_,rt⟩
    intro e he hop
    rcases List.mem_cons.mp he with e0|e1
    · subst e
      change g.1=false at hop
      have cleanOrig := orig _ (List.Mem.head _) hop
      intro k
      cases y : (xs.getD g.2.1.val 0 &&& xs.getD g.2.2.val 0).getLsbD (rneg k)
      · rfl
      · have bad := le.2 k (by simpa only [combine,hop,Bool.false_eq_true,↓reduceIte] using y)
        rw [hop] at bad
        exact bad.symm.trans (cleanOrig k)
    · exact ct _ e1 hop
end HeawoodClean

namespace HeawoodClean
open HeawoodCrossing
theorem three_mixed_edges (gs : List Gate) (i : Nat) (n : gs.length≤26)
    (hit : (gs.foldl step input).getD i 0=goal) : 3 ≤ (dirtySupport input gs).card := by
  let cleanedWord := ((rewriteGates input gs).foldl step input).getD i 0
  have lower := (reader_tradeoff gs i n hit).2
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
  change (positives cleanedWord).card≤18 at lower
  omega

theorem bypass (pre tail : List Gate) (h z : Word) (T : Group) (i : Nat)
    (big : 20≤T.card) (imp : improvement T z h) (prior : CleanTrace input pre)
    (free : z=0 ∨ z∈pre.foldl step input)
    (ct : CleanTrace ((pre.foldl step input)++[h]) tail)
    (hit : (tail.foldl step ((pre.foldl step input)++[h])).getD i 0=goal) :
    26≤pre.length+tail.length := by
  let base := pre.foldl step input
  have id : List.Forall₂ (improvement T) base base := List.forall₂_of_length_eq_of_get rfl (fun _ _ _ => imp_refl _ _)
  have rel : List.Forall₂ (improvement T) (base++[z]) (base++[h]) := List.rel_append id (.cons imp .nil)
  obtain ⟨cleaned,outs⟩ := imp_run _ _ tail rel ct
  have old : ∀ w∈input, Ready start w := by
    intro w hw
    obtain ⟨v,rfl⟩ := raw_list w hw
    exact ⟨_,input_wire startBudget v⟩
  obtain ⟨s,r,l,t,B,total,get⟩ := program pre input start 0 0 0 startBudget old prior
  have more : ∀ w∈base++[z], Ready s w := by
    intro w mem
    rcases List.mem_append.mp mem with raw|endval
    · exact get _ raw
    · have eq := List.mem_singleton.mp endval
      subst w
      rcases free with rfl|inBase
      · exact ⟨_,zero_wire B⟩
      · exact get _ inBase
  obtain ⟨next,R,L,K,done,count,lookup⟩ := program _ _ _ _ _ _ B more cleaned
  have endstate := imp_read outs i
  rw [hit] at endstate
  let w := (tail.foldl step (base++[z])).getD i 0
  have safe : clean w := by
    intro k
    cases y : w.getLsbD (rneg k)
    · rfl
    · exact (endstate.2 k y).symm.trans (target_neg k)
  have req : T⊆positives w := fun e he => Finset.mem_filter.mpr ⟨Finset.mem_univ _,endstate.1 e he (target_pos e)⟩
  have sparse := sparse_budget done w safe (ready_read done lookup i)
  have atLeast := big.trans (Finset.card_le_card req)
  omega
end HeawoodClean

namespace HeawoodClean
open HeawoodCrossing UnionBudget
def controls (S : R) (w : Word) := ∀ i j : Nat,
  (∀ u∈S, onRow i u=true → onRow j u=true) → w.getLsbD i=true → w.getLsbD j=true
def supported (S : R) (w : Word) := controls S w ∧ w.getLsbD 58=false

theorem ctrl_raw (u : V) : supported {u} (varWord u) := by
  refine ⟨fun i j h hi => h _ (by simp) hi,?_⟩
  revert u;decide +kernel

theorem ctrl_zero : supported ∅ 0 := by simp [supported,controls]
theorem ctrl_join {a b S T} (op : Bool) (h : supported S a) (k : supported T b) :
    supported (S∪T) (combine op a b) := by
  constructor
  · intro i j rel hi
    have aa := h.1 i j (fun v hv => rel v (Finset.mem_union_left _ hv))
    have bb := k.1 i j (fun v hv => rel v (Finset.mem_union_right _ hv))
    cases op
    · have both : a.getLsbD i=true ∧ b.getLsbD i=true := by simpa [combine] using hi
      simp [combine,aa both.1,bb both.2]
    · have either : a.getLsbD i=true ∨ b.getLsbD i=true := by simpa [combine] using hi
      rcases either with yes|yes
      · simp [combine,aa yes]
      · simp [combine,bb yes]
  · cases op <;> simp only [combine,Bool.false_eq_true,↓reduceIte,BitVec.getLsbD_or,BitVec.getLsbD_and,h.2,k.2] <;> rfl

theorem support_run (xs : List Word) (gs : List Gate) (pool : Family V) (n : Nat)
    (C : cap pool n) (emp : ∅∈pool) (old : ∀ w∈xs, ∃ S∈pool, supported S w) :
    ∃ P : Family V, cap P (n+gs.length) ∧ ∀ w∈gs.foldl step xs, ∃ S∈P,supported S w := by
  induction gs generalizing xs pool n with
  | nil => exact ⟨pool,by simpa using C,old⟩
  | cons g gs ih =>
    have get (i : Nat) : ∃ S∈pool, supported S (xs.getD i 0) := by
      rcases read_free xs i with z|mem
      · exact ⟨_,emp,by rw [z];exact ctrl_zero⟩
      · exact old _ mem
    obtain ⟨A,ma,ha⟩ := get g.2.1.val
    obtain ⟨B,mb,hb⟩ := get g.2.2.val
    let P := insert (A∪B) pool
    have next : ∀ w∈step xs g, ∃ S∈P,supported S w := by
      intro w hw
      rcases List.mem_append.mp hw with mem|newval
      · obtain ⟨S,m,c⟩ := old _ mem
        exact ⟨S,Finset.mem_insert_of_mem m,c⟩
      · have eq := List.mem_singleton.mp newval
        exact ⟨A∪B,Finset.mem_insert_self _ _,eq ▸ ctrl_join g.1 ha hb⟩
    obtain ⟨P',cost,look⟩ := ih _ _ _ (merge C ma mb) (Finset.mem_insert_of_mem emp) next
    exact ⟨P',by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using cost,look⟩

theorem bounded_support (gs : List Gate) (i : Nat) :
    ∃ S : R, S.card≤gs.length+1 ∧ supported S ((gs.foldl step input).getD i 0) := by
  have old : ∀ w∈input,∃ S∈units V,supported S w := by
    intro w hw
    obtain ⟨u,rfl⟩ := raw_list w hw
    exact ⟨{u},(in_units _).mpr (by simp),ctrl_raw u⟩
  obtain ⟨P,c,lookup⟩ := support_run _ gs _ 0 startBudget.lightCost ((in_units _).mpr (by simp)) old
  rcases read_free (gs.foldl step input) i with eq|mem
  · exact ⟨∅,by simp,by rw [eq];exact ctrl_zero⟩
  · obtain ⟨S,m,h⟩ := lookup _ mem
    exact ⟨S,by simpa using one c m,h⟩

theorem degreeN : ∀ u : V, (N u).card=3 := by decide +kernel
theorem pair_row : ∀ u v : V, v∈N u → ∃ e : E, ∀ j : V,
    onRow e.val j=true ↔ j=u ∨ j=v := by decide +kernel

theorem raw_pin_bypass (v : V) (w : Word) (S : R) (small : S.card≤3) (ctrl : supported S w)
    (bad : ¬ clean (varWord v &&& w)) (many : 3≤(positives (varWord v &&& w)).card) :
    improvement Finset.univ (varWord v) (varWord v &&& w) := by
  classical
  have notAll : ¬N v ⊆ S := by
    intro covers
    have same := Finset.eq_of_subset_of_card_le covers (by rw [degreeN];exact small)
    apply bad
    intro k
    cases hv : (varWord v).getLsbD (rneg k)
    · simp [hv]
    · have none (u) (hu : u∈S) : onRow (rneg k) u ≠ true := by
        have neighbor : u∈N v := same ▸ hu
        exact fun yes => ((adj_iff_neg v u).mp (neighbor_iff.mp neighbor) k) ⟨hv,yes⟩
      have off : w.getLsbD (rneg k)=false := by
        cases y : w.getLsbD (rneg k)
        · rfl
        · exact (ctrl.1 _ 58 (fun u hu falseBit => False.elim (none u hu falseBit)) y).symm.trans ctrl.2
      simp [off]
  obtain ⟨u,near,outside⟩ := Finset.not_subset.mp notAll
  obtain ⟨e,pair⟩ := pair_row v u near
  have incl : positives (varWord v &&& w) ⊆ incident v := by
    intro r mem
    have both : (varWord v).getLsbD r.val=true ∧ w.getLsbD r.val=true := by
      simpa [positives] using mem
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,both.1⟩
  have all := Finset.eq_of_subset_of_card_le incl (by rw [regular];exact many)
  have on : e∈incident v := Finset.mem_filter.mpr ⟨Finset.mem_univ _,(pair v).mpr (Or.inl rfl)⟩
  rw [←all] at on
  have we : w.getLsbD e.val=true := (Bool.and_eq_true_iff.mp
    (show ((varWord v).getLsbD e.val && w.getLsbD e.val)=true from by simpa only [BitVec.getLsbD_and] using (Finset.mem_filter.mp on).2)).2
  refine ⟨fun r _ yes => (Bool.and_eq_true_iff.mp (by simpa only [BitVec.getLsbD_and] using yes)).1,?_⟩
  intro k yes
  have wk := ctrl.1 e.val (rneg k) (by
    intro j hj bit
    rcases (pair j).mp bit with rfl|rfl
    · exact yes
    · exact False.elim (outside hj)) we
  simp [wk,yes]
end HeawoodClean

namespace HeawoodClean
open HeawoodCrossing
theorem support_append (a b : List Gate) (xs : List Word) :
    dirtySupport xs (a++b)=dirtySupport xs a ∪ dirtySupport (a.foldl step xs) b := by
  induction a generalizing xs with
  | nil => simp [dirtySupport]
  | cons g gs ih => simp [dirtySupport,ih,Finset.union_assoc]

theorem support_clean (gs : List Gate) (xs : List Word) (ct : CleanTrace xs gs) : dirtySupport xs gs=∅ := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    have tail : CleanTrace (step xs g) gs := fun e he h => ct e (List.Mem.tail _ he) h
    have off : marked xs g=false := by
      by_contra! on
      have bad := mark_dirty (Bool.eq_true_of_not_eq_false on)
      have op : g.1=false := by cases hh : g.1 <;> simp_all [marked]
      have ok := ct (g.1,xs.getD g.2.1.val 0,xs.getD g.2.2.val 0) (List.Mem.head _) op
      exact bad (by simpa only [value,combine,op,Bool.false_eq_true,↓reduceIte] using ok)
    simp [dirtySupport,off,ih _ tail]

theorem free_in (pre : List Gate) (v : V) : varWord v∈pre.foldl step input := by
  have old : varWord v∈input := by
    unfold varWord
    rw [List.getD_eq_getElem _ _ (show v.val < input.length from v.isLt)]
    exact List.getElem_mem _
  have persist (gs : List Gate) (xs : List Word) (h : varWord v∈xs) : varWord v∈gs.foldl step xs := by
    induction gs generalizing xs with
    | nil => exact h
    | cons g gs ih => exact ih (step xs g) (List.mem_append_left _ h)
  exact persist pre input old

structure Candidate (pre tail : List Gate) (g : Gate) (i : Nat) : Prop where
  limit : pre.length+1+tail.length≤26
  cleanPre : CleanTrace input pre
  dirtyGate : marked (pre.foldl step input) g=true
  cleanTail : CleanTrace (step (pre.foldl step input) g) tail
  hit : (tail.foldl step (step (pre.foldl step input) g)).getD i 0=goal

theorem Candidate.many {pre tail g i} (h : Candidate pre tail g i) :
    3≤(positives (value (pre.foldl step input) g)).card := by
  let circuit := pre++g::tail
  have small : circuit.length≤26 := by simpa [circuit,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.limit
  have correct : (circuit.foldl step input).getD i 0=goal := by simpa [circuit,List.foldl_append] using h.hit
  have size := three_mixed_edges circuit i small correct
  simpa only [circuit,support_append,dirtySupport,support_clean _ _ h.cleanPre,support_clean _ _ h.cleanTail,
    h.dirtyGate,↓reduceIte,Finset.empty_union,Finset.union_empty] using size

theorem Candidate.no_copy {pre tail g i} (h : Candidate pre tail g i) {z : Word}
    (avail : z=0 ∨ z ∈ pre.foldl step input) (equal : value (pre.foldl step input) g=z) : False := by
  have imp : improvement Finset.univ z (value (pre.foldl step input) g) := equal ▸ imp_refl _ _
  have too := bypass pre tail _ z Finset.univ i (by decide) imp h.cleanPre avail h.cleanTail h.hit
  have small := h.limit
  omega

theorem Candidate.and_op {pre tail g i} (h : Candidate pre tail g i) : g.1=false := by
  have dirty := h.dirtyGate
  cases op : g.1 <;> simp_all [marked]

theorem Candidate.no_raw {pre tail g i} (h : Candidate pre tail g i) (early : pre.length≤2)
    (v : V) (j : Nat)
    (eq : value (pre.foldl step input) g=varWord v &&& (pre.foldl step input).getD j 0) : False := by
  obtain ⟨S,small,ctrl⟩ := bounded_support pre j
  have bad := mark_dirty h.dirtyGate
  have many := h.many
  rw [eq] at bad many
  have imp := raw_pin_bypass v _ S (by omega) ctrl bad many
  rw [←eq] at imp
  have too := bypass pre tail _ _ Finset.univ i (by decide) imp h.cleanPre (Or.inr (free_in _ _)) h.cleanTail h.hit
  have limit := h.limit
  omega
end HeawoodClean

namespace HeawoodClean
open HeawoodCrossing

def basic (x : Word) : Prop := x=0 ∨ ∃ v : V, x=varWord v
theorem basic_mem {x : Word} (h : x∈input) : basic x := Or.inr (raw_list x h)
theorem basic_extra (extra : List Word) (i : Nat) :
    basic ((input++extra).getD i 0) ∨ (input++extra).getD i 0∈extra := by
  rcases read_free (input++extra) i with z|mem
  · exact Or.inl (Or.inl z)
  · exact (List.mem_append.mp mem).imp_left basic_mem
theorem basic_input (i : Nat) : basic (input.getD i 0) := by
  rcases read_free input i with z|mem
  · exact Or.inl z
  · exact basic_mem mem

theorem literal_pair {a b : Word} (l : basic a) (r : basic b) (proper : ¬basic (a|||b)) :
    ∃ p q : V, p≠q ∧ a|||b=varWord p|||varWord q := by
  rcases l with rfl|⟨p,rfl⟩
  · exact False.elim (proper (by rw [show (0 : Word)|||b=b from BitVec.zero_or];exact r))
  rcases r with rfl|⟨q,rfl⟩
  · have eq : varWord p|||0=varWord p := BitVec.or_zero
    exact False.elim (proper (Or.inr ⟨p,eq⟩))
  by_cases eq : p=q
  · subst q;exact False.elim (proper (Or.inr ⟨p,BitVec.or_self⟩))
  · exact ⟨p,q,eq,rfl⟩

theorem absorption (a b : Word) : a &&& (a|||b)=a ∧ a &&& (b|||a)=a := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp only [BitVec.getLsbD_and,BitVec.getLsbD_or] <;> cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem Candidate.pins {pre tail g i} (h : Candidate pre tail g i) (early : pre.length≤2) :
    let xs := pre.foldl step input
    let a := xs.getD g.2.1.val 0
    let b := xs.getD g.2.2.val 0
    ¬basic a ∧ ¬basic b ∧ a≠b ∧ value xs g=a&&&b := by
  intro xs a b
  have eq : value xs g=a&&&b := by simp only [value,combine,h.and_op,Bool.false_eq_true,↓reduceIte,a,b]
  have bad := mark_dirty h.dirtyGate
  change ¬clean (value xs g) at bad
  have zero : clean 0 := by simp [clean]
  refine ⟨?_,?_,?_,eq⟩
  · rintro (za|⟨v,va⟩)
    · have z : a&&&b=0 := by rw [za];exact BitVec.zero_and
      exact bad ((eq.trans z) ▸ zero)
    · exact h.no_raw early v g.2.2.val (va ▸ eq)
  · rintro (zb|⟨v,vb⟩)
    · have z : a&&&b=0 := by rw [zb];exact BitVec.and_zero
      exact bad ((eq.trans z) ▸ zero)
    · exact h.no_raw early v g.2.1.val ((eq.trans (BitVec.and_comm _ _)).trans (congrArg (fun w => w&&&a) vb))
  · intro same
    exact h.no_copy (read_free xs g.2.1.val) (eq.trans (by rw [←same];exact BitVec.and_self))

theorem shape_two {first second tail g i} (h : Candidate [first,second] tail g i) :
    let f := value input first
    let z := value (step input first) second
    ∃ p q a b : V, p≠q ∧ a≠b ∧ f=varWord p|||varWord q ∧ z=varWord a|||varWord b ∧
      value ([first,second].foldl step input) g=f&&&z := by
  intro f z
  let xs := [first,second].foldl step input
  let a := xs.getD g.2.1.val 0
  let b := xs.getD g.2.2.val 0
  obtain ⟨la,lb,ne,eq⟩ := h.pins (by simp)
  change ¬basic a at la
  change ¬basic b at lb
  change a≠b at ne
  change value xs g=a&&&b at eq
  have decomp : xs=input++[f,z] := by simp [xs,f,z,step,value]
  have choose (j : Nat) (nb : ¬basic (xs.getD j 0)) : xs.getD j 0=f ∨ xs.getD j 0=z := by
    rw [decomp] at nb ⊢
    have inE := (basic_extra [f,z] j).resolve_left nb
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using inE
  have pickA := choose g.2.1.val la
  have pickB := choose g.2.2.val lb
  change a=f ∨ a=z at pickA
  change b=f ∨ b=z at pickB
  have forms : value xs g=f&&&z ∧ ¬basic f ∧ ¬basic z := by
    rcases pickA with af|az <;> rcases pickB with bf|bz
    · exact False.elim (ne (af.trans bf.symm))
    · exact ⟨by rw [eq,af,bz],af ▸ la,bz ▸ lb⟩
    · exact ⟨by rw [eq,az,bf,BitVec.and_comm],bf ▸ lb,az ▸ la⟩
    · exact False.elim (ne (az.trans bz.symm))
  have notClean := mark_dirty h.dirtyGate
  change ¬clean (value xs g) at notClean
  have neg (k : Word) (m : Word) (e : value xs g=k&&&m) : ¬clean k := by
    intro safe
    apply notClean
    rw [e]
    intro r;simp [safe r]
  have uf := neg f z forms.1
  have uz := neg z f (forms.1.trans (BitVec.and_comm _ _))
  have fop : first.1=true := by
    cases op : first.1
    · have c := h.cleanPre (first.1,input.getD first.2.1.val 0,input.getD first.2.2.val 0) (List.Mem.head _) op
      exact False.elim (uf (by simpa only [f,value,combine,op,Bool.false_eq_true,↓reduceIte] using c))
    · rfl
  have zop : second.1=true := by
    cases op : second.1
    · let ps := step input first
      have c := h.cleanPre (second.1,ps.getD second.2.1.val 0,ps.getD second.2.2.val 0)
          (List.Mem.tail _ (List.Mem.head _)) op
      exact False.elim (uz (by simpa only [z,value,combine,op,Bool.false_eq_true,↓reduceIte] using c))
    · rfl
  have F : f=input.getD first.2.1.val 0 ||| input.getD first.2.2.val 0 := by simp only [f,value,combine,fop,↓reduceIte]
  let ps := input++[f]
  let u := ps.getD second.2.1.val 0
  let v := ps.getD second.2.2.val 0
  have Z : z=u|||v := by simp only [z,value,combine,zop,↓reduceIte];rfl
  obtain ⟨p,q,pq,pos⟩ := literal_pair (basic_input _) (basic_input _) (F ▸ forms.2.1)
  have stored : f∈xs := by rw [decomp];exact List.mem_append_right _ (List.Mem.head _)
  have back : value xs g≠f := fun wrong => h.no_copy (Or.inr stored) wrong
  have choose1 (j : Nat) : basic (ps.getD j 0) ∨ ps.getD j 0=f := by
    simpa only [List.mem_singleton] using basic_extra [f] j
  have bu : basic u := (choose1 _).resolve_right (fun bad => back (by change u=f at bad;rw [forms.1,Z,bad];exact (absorption f v).1))
  have bv : basic v := (choose1 _).resolve_right (fun bad => back (by change v=f at bad;rw [forms.1,Z,bad];exact (absorption f u).2))
  obtain ⟨x,y,xy,res⟩ := literal_pair bu bv (Z ▸ forms.2.2)
  exact ⟨p,q,x,y,pq,xy,F.trans pos,Z.trans res,forms.1⟩
end HeawoodClean

namespace HeawoodClean.Cut
open HeawoodCrossing UnionBudget
def strip (D : Group) (P : Family E) := P.image fun s => s \ D
def used (D : Group) (P : Family E) := P.filter fun s => ¬s⊆D

structure Budget (D : Group) (s : Pool) (r l t : Nat) : Prop where
  richCost : cap (strip D s.rich) r
  lightCost : cap s.light l
  claimCost : (used D s.claimed).card ≤ t
  covers : s.claimed ⊆ s.rich
  richSmall : ∀ a : Group, a.card≤1 → a∈s.rich
  lightSmall : ∀ a : R, a.card≤1 → a∈s.light

theorem plain {D s r l t} (b : Budget D s r l t) :
    HeawoodClean.Budget s 21 l s.claimed.card := by
  refine ⟨?_,b.lightCost,le_rfl,b.covers,b.richSmall,b.lightSmall⟩
  intro asks sub
  have h := Finset.card_le_univ (asks.biUnion id)
  simp only [Fintype.card_fin] at h
  omega

theorem addRich {D s r l t} (B : Budget D s r l t) (x y : Group) (hx : x∈s.rich) (hy : y∈s.rich) :
    let z : Pool := {s with rich := insert (x∪y) s.rich}
    Extends s z ∧ Budget D z (r+1) l t := by
  obtain ⟨ext,orig⟩ := HeawoodClean.addRich (plain B) _ _ hx hy
  refine ⟨ext,?_,orig.lightCost,B.claimCost,orig.covers,orig.richSmall,orig.lightSmall⟩
  have hh := merge B.richCost (Finset.mem_image_of_mem (fun s => s \ D) hx)
                               (Finset.mem_image_of_mem (fun s => s \ D) hy)
  simpa only [strip,Finset.image_insert,Finset.union_sdiff_distrib] using hh

theorem addLight {D s r l t} (B : Budget D s r l t) (x y : R) (hx : x∈s.light) (hy : y∈s.light) :
    let z : Pool := {s with light := insert (x∪y) s.light}
    Extends s z ∧ Budget D z r (l+1) t := by
  obtain ⟨ext,orig⟩ := HeawoodClean.addLight (plain B) _ _ hx hy
  exact ⟨ext,B.richCost,orig.lightCost,B.claimCost,orig.covers,orig.richSmall,orig.lightSmall⟩

theorem addBlock {D s r l t} (B : Budget D s r l t) (x : Group) (hx : x∈s.rich) :
    let z : Pool := {s with claimed := insert x s.claimed}
    Extends s z ∧ Budget D z r l (t+1) := by
  obtain ⟨ext,orig⟩ := HeawoodClean.addBlock (plain B) _ hx
  refine ⟨ext,B.richCost,B.lightCost,?_,orig.covers,orig.richSmall,orig.lightSmall⟩
  have sub : used D (insert x s.claimed) ⊆ insert x (used D s.claimed) := by
    intro a ha
    obtain ⟨m,n⟩ := Finset.mem_filter.mp ha
    rcases Finset.mem_insert.mp m with eq|m
    · exact Finset.mem_insert.mpr (Or.inl eq)
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨m,n⟩)
  exact (Finset.card_le_card sub).trans ((Finset.card_insert_le _ _).trans (by have := B.claimCost;omega))
end HeawoodClean.Cut

namespace HeawoodClean.Cut
open HeawoodCrossing UnionBudget
def Advance (D : Group) (s : Pool) (r l t : Nat) (w : Word) : Prop :=
  ∃ z r' l' t', Extends s z ∧ Budget D z r' l' t' ∧ r'+l'+t'=r+l+t+1 ∧ Ready z w
theorem or_step {D s r l t a b X Y} (B : Budget D s r l t) (ha : Wire s a X) (hb : Wire s b Y) :
    Advance D s r l t (a|||b) := by
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

theorem and_step {D s r l t a b X Y} (B : Budget D s r l t) (ha : Wire s a X) (hb : Wire s b Y)
    (safe : clean (a&&&b)) : Advance D s r l t (a&&&b) := by
  have paired := safe_raw ha hb safe
  have thin := thin_side paired
  have rectangle : ∃ T∈s.rich, ∀ e : E, Hits X e.val → Hits Y e.val → e∈T := by
    rcases thin with x|y
    · exact rectangle_one (plain B) hb x paired
    · have sym u (hu : u∈Y) v (hv : v∈X) : adjacent u v=true := by rw [adj_sym];exact paired _ hv _ hu
      obtain ⟨T,m,h⟩ := rectangle_one (plain B) ha y sym
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
end HeawoodClean.Cut

namespace HeawoodClean.Cut
open HeawoodCrossing UnionBudget
theorem bounds {s D r l t} (B : Budget D s r l t) (w : Word) (safe : clean w)
    (h : Ready s w) (T : Group) (correct : T ⊆ positives w) :
    (T \ D).card ≤ r+t ∧ T.card ≤ 3*(l+1) := by
  obtain ⟨X,wire⟩ := h
  have emp : X=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨k,hk⟩ := raw_alive v
    have yes := wire.rawSound _ ⟨v,hv,hk⟩
    rw [safe k] at yes
    contradiction
  subst X
  let wants := strip D (used D s.claimed)
  have sub : wants ⊆ strip D s.rich := Finset.image_subset_image (by
    intro x hx;exact B.covers (Finset.mem_filter.mp hx).1)
  have area := B.richCost wants sub
  have count := Finset.card_image_le (s:=used D s.claimed) (f:=fun s => s \ D)
  have cap : wants.card≤t := count.trans B.claimCost
  have reach : T \ D ⊆ wants.biUnion id := by
    intro e mem
    obtain ⟨he,hd⟩ := Finset.mem_sdiff.mp mem
    have on := (Finset.mem_filter.mp (correct he)).2
    have b : e∈blocks s := by simpa [Hits] using wire.origin e on
    obtain ⟨group,claimed,hg⟩ := Finset.mem_biUnion.mp b
    have keep : group ∈ used D s.claimed := Finset.mem_filter.mpr ⟨claimed,fun incl => hd (incl hg)⟩
    exact Finset.mem_biUnion.mpr ⟨group \ D,Finset.mem_image_of_mem _ keep,Finset.mem_sdiff.mpr ⟨hg,hd⟩⟩
  obtain ⟨P,hP,dom⟩ := wire.cover (by simp)
  have covered : T ⊆ P.biUnion incident := by
    intro e he
    obtain ⟨u,hu,b⟩ := dom e (Finset.mem_filter.mp (correct he)).2
    exact Finset.mem_biUnion.mpr ⟨_,hu,Finset.mem_filter.mpr ⟨Finset.mem_univ _,b⟩⟩
  have light := (Finset.card_le_card covered).trans (covered_card P)
  have size := one B.lightCost hP
  exact ⟨(Finset.card_le_card reach).trans (by omega),by omega⟩

end HeawoodClean.Cut

namespace HeawoodClean.Cut
open HeawoodCrossing UnionBudget
def seed (D : Group) : Pool :=
  ⟨(Finset.univ : Group).powerset.filter (fun A => (A \ D).card≤1), units V, {D}⟩
theorem rich_seed {D A : Group} : A∈(seed D).rich ↔ (A \ D).card≤1 := by simp [seed]
theorem seed_zero (D : Group) : Budget D (seed D) 0 0 0 := by
  constructor
  · apply small
    intro A h
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp h
    exact rich_seed.mp hs
  · exact startBudget.lightCost
  · simp [used,seed]
  · intro a ha
    have eq : a=D := Finset.mem_singleton.mp ha
    rw [eq];exact rich_seed.mpr (by simp)
  · intro A h
    exact rich_seed.mpr ((Finset.card_le_card Finset.sdiff_subset).trans h)
  · exact startBudget.lightSmall

theorem free_input (D : Group) (w : Word) (hw : w∈input) : Ready (seed D) w := by
  obtain ⟨v,rfl⟩ := raw_list w hw
  exact ⟨_,input_wire (plain (seed_zero D)) _⟩

theorem seeded_word {D : Group} (w : Word) (inside : positives w ⊆ D) (v : V)
    (dom : Dom w {v}) : Ready (seed D) w := by
  have B := seed_zero D
  refine ⟨∅,by simp [Hits],?_,fun c sub => B.richSmall _ (star_small _ _ sub (by simp)),?_⟩
  · intro e on
    right
    exact Finset.mem_biUnion.mpr ⟨D,Finset.mem_singleton_self _,inside (Finset.mem_filter.mpr ⟨Finset.mem_univ _,on⟩)⟩
  · exact fun _ => ⟨{v},B.lightSmall _ (by simp),dom⟩

theorem seeded_pair {D : Group} (u v c : V) (uv : u≠v) (left : adjacent c u=true)
    (right : adjacent c v=true) (covered : star c {u,v} ⊆ D) :
    Ready (seed D) (varWord u ||| varWord v) := by
  refine ⟨{u,v},?_,?_,?_,?_⟩
  · intro r hit
    obtain ⟨j,hj,on⟩ := hit
    simp only [Finset.mem_insert,Finset.mem_singleton] at hj
    simp only [BitVec.getLsbD_or,Bool.or_eq_true]
    rcases hj with rfl|rfl
    · exact Or.inl on
    · exact Or.inr on
  · intro e hit
    have two : onRow e.val u=true ∨ onRow e.val v=true := by simpa [onRow] using hit
    rcases two with y|y
    · exact Or.inl ⟨u,by simp,y⟩
    · exact Or.inl ⟨v,by simp,y⟩
  · intro d sub
    have pc : ({u,v} : R) ⊆ N c := Finset.insert_subset (neighbor_iff.mpr left)
        (Finset.singleton_subset_iff.mpr (neighbor_iff.mpr right))
    have eq := unique_center (X:={u,v}) (by simp [uv]) sub pc
    subst d
    exact rich_seed.mpr (by simp [Finset.sdiff_eq_empty_iff_subset.mpr covered])
  · intro low
    simp [uv] at low
end HeawoodClean.Cut

namespace HeawoodClean.Cut
open HeawoodCrossing UnionBudget
def atom (u v : V) : Group := positives (varWord u &&& varWord v)
theorem atom_mem {u v : V} {e : E} :
    e∈atom u v ↔ onRow e.val u=true ∧ onRow e.val v=true := by simp [atom,positives,onRow]
theorem atomic : ∀ u v : V, u≠v → (atom u v).card≤1 := by decide +kernel
theorem nonedge_empty : ∀ u v : V, u≠v → adjacent u v=false → atom u v=∅ := by decide +kernel

end HeawoodClean.Cut

namespace HeawoodClean
open HeawoodCrossing
open Cut (atom atom_mem atomic nonedge_empty)
theorem cheap_repair (pre tail : List Gate) (h z : Word) (i : Nat)
    (preOK : CleanTrace input pre) (available : z=0 ∨ z∈pre.foldl step input)
    (loss : (positives h \ positives z).card≤1)
    (neg : ∀ k : Fin 37, z.getLsbD (rneg k)=true → h.getLsbD (rneg k)=true)
    (ct : CleanTrace ((pre.foldl step input)++[h]) tail)
    (hit : (tail.foldl step ((pre.foldl step input)++[h])).getD i 0=goal) :
    26≤pre.length+tail.length := by
  let T := (Finset.univ : Group) \ (positives h \ positives z)
  have size := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (positives h \ positives z))
  change T.card+(positives h \ positives z).card=21 at size
  have imp : improvement T z h := by
    refine ⟨?_,neg⟩
    intro e he hot
    have hh : e∈positives h := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hot⟩
    have zz : e∈positives z := by
      by_contra notz
      exact (Finset.mem_sdiff.mp he).2 (Finset.mem_sdiff.mpr ⟨hh,notz⟩)
    exact (Finset.mem_filter.mp zz).2
  exact bypass pre tail h z T i (by omega) imp preOK available ct hit

theorem shared_literal (v a b : V) (ab : a≠b) :
    let h := (varWord v ||| varWord a) &&& (varWord v ||| varWord b)
    (positives h \ positives (varWord v)).card≤1 ∧
    ∀ k : Fin 37, (varWord v).getLsbD (rneg k)=true → h.getLsbD (rneg k)=true := by
  intro h
  constructor
  · have sub : positives h \ positives (varWord v) ⊆ atom a b := by
      intro e he
      obtain ⟨yes,no⟩ := Finset.mem_sdiff.mp he
      have off : (varWord v).getLsbD e.val=false := by simpa [positives] using no
      have on := (Finset.mem_filter.mp yes).2
      apply atom_mem.mpr
      simpa [h,off,onRow] using on
    exact (Finset.card_le_card sub).trans (atomic a b ab)
  · intro k on;simp [h,on]

theorem four_union (p q a b : V) :
    positives ((varWord p ||| varWord q) &&& (varWord a ||| varWord b)) ⊆
    (atom p a ∪ atom p b) ∪ (atom q a ∪ atom q b) := by
  intro e h
  simp only [Finset.mem_union,atom_mem]
  have yes : (onRow e.val p=true ∨ onRow e.val q=true) ∧
      (onRow e.val a=true ∨ onRow e.val b=true) := by simpa [onRow,positives] using h
  rcases yes with ⟨p1|q1,a1|b1⟩
  · exact Or.inl (Or.inl ⟨p1,a1⟩)
  · exact Or.inl (Or.inr ⟨p1,b1⟩)
  · exact Or.inr (Or.inl ⟨q1,a1⟩)
  · exact Or.inr (Or.inr ⟨q1,b1⟩)
theorem atom_cost (u v : V) (uv : u≠v) : (atom u v).card ≤ if adjacent u v then 1 else 0 := by
  cases z : adjacent u v
  · simp [nonedge_empty u v uv z]
  · exact atomic u v uv

end HeawoodClean

namespace HeawoodClean.Cut
open HeawoodCrossing UnionBudget
def proxy (T : Group) (s : Pool) (w : Word) : Prop := ∃ z, improvement T z w ∧ Ready s z
def adviceCost (A : Finset Word) (xs : List Word) : List Gate → Nat
  | [] => 0
  | g::gs => (if value xs g ∈ A then 0 else 1) + adviceCost A (step xs g) gs
def permitted (A : Finset Word) (xs : List Word) (gs : List Gate) : Prop :=
  ∀ e∈trace xs gs, e.1=false → e.2.1 &&& e.2.2 ∉ A → clean (e.2.1 &&& e.2.2)

theorem carry {T s z w} (ext : Extends s z) (h : proxy T s w) : proxy T z w := by
  obtain ⟨v,le,X,ready⟩ := h
  exact ⟨v,le,X,widen ext ready⟩
set_option maxHeartbeats 600000 in
theorem simulate (A : Finset Word) (T D : Group) (gs : List Gate) (xs : List Word)
    (s : Pool) (r l t : Nat) (B : Budget D s r l t)
    (free : ∀ w∈A, proxy T s w) (old : ∀ w∈xs, proxy T s w)
    (allOK : permitted A xs gs) :
    ∃ z R L K, Budget D z R L K ∧ R+L+K=r+l+t+adviceCost A xs gs ∧
      ∀ w∈gs.foldl step xs, proxy T z w := by
  induction gs generalizing xs s r l t with
  | nil => exact ⟨s,r,l,t,B,by simp [adviceCost],old⟩
  | cons g gs ih =>
    have ct : permitted A (step xs g) gs := fun e he hh => allOK e (List.Mem.tail _ he) hh
    by_cases given : value xs g∈A
    · have next : ∀ w∈step xs g, proxy T s w := by
        intro w hw
        rcases List.mem_append.mp hw with prev|cur
        · exact old _ prev
        · exact (List.mem_singleton.mp cur) ▸ free _ given
      obtain ⟨z,R,L,K,done,size,look⟩ := ih _ _ _ _ _ B free next ct
      exact ⟨z,R,L,K,done,by rw [adviceCost,ite_eq_left given,zero_add];exact size,look⟩
    · have get (j : Nat) : proxy T s (xs.getD j 0) := by
        by_cases hj : j<xs.length
        · rw [List.getD_eq_getElem _ _ hj];exact old _ (List.getElem_mem hj)
        · rw [List.getD_eq_default _ _ (by omega)]
          exact ⟨0,imp_refl _ _,∅,zero_wire (plain B)⟩
      obtain ⟨u,up,X,wu⟩ := get g.2.1.val
      obtain ⟨v,vp,Y,wv⟩ := get g.2.2.val
      let w := combine g.1 u v
      have improve : improvement T w (value xs g) := imp_op g.1 up vp
      have advance : Advance D s r l t w := by
        dsimp [w]
        cases op : g.1 with
        | true => exact or_step B wu wv
        | false =>
          have oq : xs.getD g.2.1.val 0 &&& xs.getD g.2.2.val 0 ∉ A := by
            simpa only [value,combine,op,Bool.false_eq_true,↓reduceIte] using given
          have ok := allOK (g.1,xs.getD g.2.1.val 0,xs.getD g.2.2.val 0) (List.Mem.head _) op oq
          apply and_step B wu wv
          intro k
          cases y : (u&&&v).getLsbD (rneg k)
          · rfl
          · have orig := improve.2 k (by simpa only [w,combine,op,Bool.false_eq_true,↓reduceIte] using y)
            simp only [value,combine,op,Bool.false_eq_true,↓reduceIte] at orig
            exact orig.symm.trans (ok k)
      obtain ⟨z,R,L,K,ext,bud,sum,now⟩ := advance
      have next : ∀ y∈step xs g,proxy T z y := by
        intro y hy
        rcases List.mem_append.mp hy with prev|cur
        · exact carry ext (old _ prev)
        · obtain rfl := List.mem_singleton.mp cur
          exact ⟨w,improve,now⟩
      obtain ⟨z',R',L',K',done,n,look⟩ := ih _ _ _ _ _ bud (fun y hy => carry ext (free y hy)) next ct
      refine ⟨z',R',L',K',done,?_,look⟩
      rw [adviceCost,ite_eq_right given];omega

theorem advice_bound (A : Finset Word) (T D : Group) (gs : List Gate) (i : Nat)
    (s : Pool) (r l t : Nat) (B : Budget D s r l t) (free : ∀ w∈A,proxy T s w)
    (perm : permitted A input gs) (hit : (gs.foldl step input).getD i 0=goal) :
    3*(T \ D).card+T.card ≤ 3*(r+l+t+adviceCost A input gs+1) := by
  have start : ∀ w∈input,proxy T s w := by
    intro w hw
    obtain ⟨v,rfl⟩ := raw_list w hw
    exact ⟨_,imp_refl _ _,_,input_wire (plain B) v⟩
  obtain ⟨z,R,L,K,done,n,look⟩ := simulate _ _ _ _ _ _ _ _ _ B free start perm
  have mem : goal∈gs.foldl step input := by
    by_cases ok : i<(gs.foldl step input).length
    · rw [←hit,List.getD_eq_getElem _ _ ok];exact List.getElem_mem ok
    · rw [List.getD_eq_default _ _ (by omega)] at hit
      exact False.elim ((by decide : (0 : Word)≠goal) hit)
  obtain ⟨w,improve,ready⟩ := look _ mem
  have safe : clean w := by
    intro k
    cases y : w.getLsbD (rneg k)
    · rfl
    · exact (improve.2 k y).symm.trans (target_neg k)
  have required : T ⊆ positives w := fun e he => Finset.mem_filter.mpr ⟨Finset.mem_univ _,improve.1 e he (target_pos e)⟩
  obtain ⟨area,cover⟩ := bounds done _ safe ready _ required
  omega
end HeawoodClean.Cut

namespace HeawoodClean.Cut
open HeawoodCrossing UnionBudget
theorem path_advice (p q a b : V) (pq : p≠q) (ab : a≠b)
    (pa : adjacent p a=true) (pb : adjacent p b=true) (qa : adjacent q a=true)
    (qb : adjacent q b=false) (neq : q≠b)
    (gs : List Gate) (i : Nat) :
    let f := varWord p ||| varWord q
    let g := varWord a ||| varWord b
    let A : Finset Word := {f,g,f&&&g}
    permitted A input gs → (gs.foldl step input).getD i 0=goal → 24≤adviceCost A input gs := by
  intro f g A perm hit
  let D := atom p a ∪ atom p b ∪ atom q a
  let T := (Finset.univ : Group) \ atom q a
  let h := varWord p &&& g
  let xs := input++[f,g,h]
  have ap : adjacent a p=true := by rw [adj_sym];exact pa
  have aq : adjacent a q=true := by rw [adj_sym];exact qa
  have ir : ∀ v : V, adjacent v v=false := by decide +kernel
  have pne : p≠a := by rintro rfl;rw [ir] at pa;contradiction
  have pnb : p≠b := by rintro rfl;rw [ir] at pb;contradiction
  have qna : q≠a := by rintro rfl;rw [ir] at qa;contradiction
  have miss := nonedge_empty q b neq qb
  have ar : (atom p a).card≤1 := atomic _ _ pne
  have br := atomic _ _ pnb
  have cr := atomic _ _ qna
  have dc : D.card≤3 := by
    have one := Finset.card_union_le (atom p a) (atom p b)
    have two := Finset.card_union_le (atom p a ∪ atom p b) (atom q a)
    dsimp [D];omega
  have tc : 20≤T.card := by
    have e := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (atom q a))
    change T.card+(atom q a).card=21 at e
    omega
  have td : 18≤(T \ D).card := by
    have qsub : atom q a ⊆ D := Finset.subset_union_right
    have eq : T \ D = (Finset.univ : Group) \ D := by
      ext e
      simp only [T,Finset.mem_sdiff,Finset.mem_univ,true_and]
      exact ⟨fun h => h.2,fun h => ⟨fun bad => h (qsub bad),h⟩⟩
    have card := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
    rw [eq]
    change (Finset.univ \ D).card+D.card=21 at card
    omega
  have sf : star a {p,q} ⊆ D := by
    intro e he
    obtain ⟨aa,u,hu,on⟩ := star_mem.mp he
    simp only [Finset.mem_insert,Finset.mem_singleton] at hu
    rcases hu with rfl|rfl
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (atom_mem.mpr ⟨on,aa⟩))
    · exact Finset.mem_union_right _ (atom_mem.mpr ⟨on,aa⟩)
  have sg : star p {a,b} ⊆ D := by
    intro e he
    obtain ⟨pp,u,hu,on⟩ := star_mem.mp he
    simp only [Finset.mem_insert,Finset.mem_singleton] at hu
    rcases hu with rfl|rfl
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (atom_mem.mpr ⟨pp,on⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (atom_mem.mpr ⟨pp,on⟩))
  have hpos (e : E) : e∈positives h ↔ onRow e.val p=true ∧ (onRow e.val a=true ∨ onRow e.val b=true) := by
    simp [h,g,positives,onRow]
  have hd : positives h ⊆ D := by
    intro e he
    obtain ⟨pp,aa|bb⟩ := (hpos e).mp he
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (atom_mem.mpr ⟨pp,aa⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (atom_mem.mpr ⟨pp,bb⟩))
  have old : ∀ w∈xs, Ready (seed D) w := by
    intro w hw
    rcases List.mem_append.mp hw with hw|hw
    · exact free_input D w hw
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl|rfl
      · exact seeded_pair p q a pq ap aq sf
      · exact seeded_pair a b p ab pa pb sg
      · apply seeded_word _ hd p
        intro e yes
        exact ⟨p,by simp,((hpos e).mp (Finset.mem_filter.mpr ⟨Finset.mem_univ _,yes⟩)).1⟩
  have bridge : improvement T h (f&&&g) := by
    constructor
    · intro e he hot
      have both : (onRow e.val p=true ∨ onRow e.val q=true) ∧
          (onRow e.val a=true ∨ onRow e.val b=true) := by simpa [f,g,onRow] using hot
      have pp : onRow e.val p=true := by
        rcases both.1 with yes|qq
        · exact yes
        · rcases both.2 with aa|bb
          · exact False.elim ((Finset.mem_sdiff.mp he).2 (atom_mem.mpr ⟨qq,aa⟩))
          · have m : e∈atom q b := atom_mem.mpr ⟨qq,bb⟩
            rw [miss] at m;exact False.elim (Finset.notMem_empty _ m)
      exact (Finset.mem_filter.mp ((hpos e).mpr ⟨pp,both.2⟩)).2
    · intro k hk
      have both : (varWord p).getLsbD (rneg k)=true ∧ g.getLsbD (rneg k)=true := by simpa [h] using hk
      simp [f,both.1,both.2]
  have fp : proxy T (seed D) f := ⟨f,imp_refl _ _,old _ (List.mem_append_right _ (by simp))⟩
  have gp : proxy T (seed D) g := ⟨g,imp_refl _ _,old _ (List.mem_append_right _ (by simp))⟩
  have hp : proxy T (seed D) (f&&&g) := ⟨h,bridge,old _ (List.mem_append_right _ (by simp))⟩
  have free : ∀ w∈A,proxy T (seed D) w := by
    intro w hw
    simp only [A,Finset.mem_insert,Finset.mem_singleton] at hw
    rcases hw with rfl|rfl|rfl
    · exact fp
    · exact gp
    · exact hp
  have lower := advice_bound A T D gs i (seed D) 0 0 0 (seed_zero D) free perm hit
  omega
end HeawoodClean.Cut

namespace HeawoodClean.Cut
open HeawoodCrossing
def produced (xs : List Word) : List Gate → List Word
  | [] => []
  | g::gs => value xs g :: produced (step xs g) gs
theorem produced_fold (xs : List Word) (gs : List Gate) :
    gs.foldl step xs=xs++produced xs gs := by
  induction gs generalizing xs with
  | nil => simp [produced]
  | cons g gs ih => simp [produced,step,value,ih]
theorem produced_append (xs : List Word) (p q : List Gate) :
    produced xs (p++q)=produced xs p ++ produced (p.foldl step xs) q := by
  induction p generalizing xs with
  | nil => rfl
  | cons g p ih => simp [produced,ih]

theorem count_advice (A : Finset Word) (xs : List Word) (gs : List Gate) :
    (A ∩ (produced xs gs).toFinset).card+adviceCost A xs gs≤gs.length := by
  classical
  induction gs generalizing xs with
  | nil => simp [produced,adviceCost]
  | cons g gs ih =>
    let S := (produced (step xs g) gs).toFinset
    let x := value xs g
    have tail := ih (step xs g)
    change (A∩S).card+_≤_ at tail
    change (A∩(x::produced (step xs g) gs).toFinset).card+((if x∈A then 0 else 1)+_)≤gs.length+1
    rw [List.toFinset_cons]
    by_cases keep : x∈A
    · rw [ite_eq_left keep]
      have inc : A∩insert x S ⊆ insert x (A∩S) := by
        intro y hy
        obtain ⟨ay,mem⟩ := Finset.mem_inter.mp hy
        rcases Finset.mem_insert.mp mem with eq|sy
        · exact Finset.mem_insert.mpr (Or.inl eq)
        · exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨ay,sy⟩)
      have card := (Finset.card_le_card inc).trans (Finset.card_insert_le _ _)
      change (A∩insert x S).card+_ ≤ _
      omega
    · rw [ite_eq_right keep]
      have eq : A∩insert x S=A∩S := by
        ext y
        simp only [Finset.mem_inter,Finset.mem_insert]
        aesop
      change (A∩insert x S).card+_ ≤ _
      rw [eq];omega

theorem trace_cat (xs : List Word) (p q : List Gate) :
    trace xs (p++q)=trace xs p ++ trace (p.foldl step xs) q := by
  induction p generalizing xs with
  | nil => rfl
  | cons g p ih => simp [trace,ih]

theorem permits_one {pre tail g i} (h : Candidate pre tail g i) (A : Finset Word)
    (mem : value (pre.foldl step input) g ∈ A) : permitted A input (pre++g::tail) := by
  intro e he op skip
  rw [trace_cat] at he
  rcases List.mem_append.mp he with early|next
  · exact h.cleanPre e early op
  · rcases List.mem_cons.mp next with eq|later
    · subst e
      apply False.elim (skip ?_)
      change g.1=false at op
      simpa only [value,combine,op,Bool.false_eq_true,↓reduceIte] using mem
    · exact h.cleanTail _ later op

theorem named_three {pre tail g i} (h : Candidate pre tail g i) (f z : Word)
    (distinct : f≠z) (f₁ : f∈pre.foldl step input) (z₁ : z∈pre.foldl step input)
    (f₀ : f∉input) (z₀ : z∉input) :
    let w := value (pre.foldl step input) g
    let A : Finset Word := {f,z,w}
    adviceCost A input (pre++g::tail) ≤ 23 := by
  intro w A
  let prog := pre++g::tail
  have fw : w≠f := fun eq => h.no_copy (Or.inr f₁) eq
  have zw : w≠z := fun eq => h.no_copy (Or.inr z₁) eq
  have appear (v : Word) (atPre : v∈pre.foldl step input) (nonraw : v∉input) :
      v∈produced input prog := by
    rw [produced_fold] at atPre
    exact (show produced input prog=produced input pre++produced (pre.foldl step input) (g::tail) from produced_append _ _ _) ▸
      List.mem_append_left _ ((List.mem_append.mp atPre).resolve_left nonraw)
  have contains : A ⊆ (produced input prog).toFinset := by
    intro v hv
    simp only [A,Finset.mem_insert,Finset.mem_singleton] at hv
    apply List.mem_toFinset.mpr
    rcases hv with rfl|rfl|rfl
    · exact appear _ f₁ f₀
    · exact appear _ z₁ z₀
    · dsimp [prog];rw [produced_append]
      exact List.mem_append_right _ (List.Mem.head _)
  have three : A.card=3 := by simp [A,distinct,Ne.symm fw,Ne.symm zw]
  have count := count_advice A input prog
  rw [Finset.inter_eq_left.mpr contains,three] at count
  have n : prog.length≤26 := by simpa [prog,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.limit
  change adviceCost A input prog≤23
  omega
end HeawoodClean.Cut

namespace HeawoodClean
open HeawoodCrossing
open Cut (atom atom_mem atomic nonedge_empty)
theorem rectangle_advice (p q a b : V) (pq : p≠q) (ab : a≠b)
    (pa : p≠a) (pb : p≠b) (qa : q≠a) (qb : q≠b)
    (gs : List Gate) (i : Nat) :
    let f := varWord p ||| varWord q
    let g := varWord a ||| varWord b
    let h := f&&&g
    let A : Finset Word := {f,g,h}
    3≤(positives h).card → Cut.permitted A input gs → (gs.foldl step input).getD i 0=goal → 24≤Cut.adviceCost A input gs := by
  intro f g h A many ct hit
  have m := (Finset.card_le_card (four_union p q a b)).trans (Finset.card_union_le _ _)
  have l := Finset.card_union_le (atom p a) (atom p b)
  have r := Finset.card_union_le (atom q a) (atom q b)
  have x1 := atom_cost p a pa
  have x2 := atom_cost p b pb
  have x3 := atom_cost q a qa
  have x4 := atom_cost q b qb
  have atLeast : 3≤(if adjacent p a then 1 else 0)+(if adjacent p b then 1 else 0)+
      (if adjacent q a then 1 else 0)+(if adjacent q b then 1 else 0) := by
    change 3≤(positives ((varWord p ||| varWord q) &&& (varWord a ||| varWord b))).card at many
    omega
  have cert (P Q A B : V) (pp : P≠Q) (aa : A≠B) (v1 : adjacent P A=true) (v2 : adjacent P B=true)
      (v3 : adjacent Q A=true) (v4 : adjacent Q B=false) (v5 : Q≠B)
      (F : f=varWord P ||| varWord Q) (G : g=varWord A ||| varWord B) :
      24≤Cut.adviceCost {f,g,h} input gs := by
    have res := Cut.path_advice P Q A B pp aa v1 v2 v3 v4 v5 gs i
    rw [←F,←G] at res
    exact res ct hit
  have fr : f=varWord q ||| varWord p := BitVec.or_comm _ _
  have gr : g=varWord b ||| varWord a := BitVec.or_comm _ _
  cases e1 : adjacent p a <;> cases e2 : adjacent p b <;>
    cases e3 : adjacent q a <;> cases e4 : adjacent q b <;>
    simp only [e1,e2,e3,e4,Bool.false_eq_true,↓reduceIte] at atLeast <;> try omega
  · exact cert q p b a pq.symm ab.symm e4 e3 e2 e1 pa fr gr
  · exact cert q p a b pq.symm ab e3 e4 e1 e2 pb fr rfl
  · exact cert p q b a pq ab.symm e2 e1 e4 e3 qa rfl gr
  · exact cert p q a b pq ab e1 e2 e3 e4 qb rfl rfl
  · have nope := no_square p q a b pq ab e1 e2 e3
    rw [e4] at nope
    contradiction
end HeawoodClean

namespace HeawoodClean
open HeawoodCrossing
theorem union_new : ∀ p q : V, p≠q → varWord p ||| varWord q ∉ input := by
  decide +kernel

theorem excluded_union_operands {pre tail g i} (C : Candidate pre tail g i)
    (p q a b : V)
    (left : (pre.foldl step input).getD g.2.1.val 0 = varWord p|||varWord q)
    (right : (pre.foldl step input).getD g.2.2.val 0 = varWord a|||varWord b) : False := by
  let f := varWord p|||varWord q
  let z := varWord a|||varWord b
  let w := value (pre.foldl step input) g
  have box : w=f&&&z := by simp only [w,value,combine,C.and_op,Bool.false_eq_true,↓reduceIte,left,right,f,z]
  have enough := C.many
  change 3≤(positives w).card at enough
  have incr (u : V) (v : Word) (S : R) (card : S.card≤3) (ctrl : supported S v) (eq : w=varWord u &&& v) : False := by
    have bad := mark_dirty C.dirtyGate
    change ¬clean w at bad
    rw [eq] at bad enough
    have imp := raw_pin_bypass u v S card ctrl bad enough
    rw [←eq] at imp
    have too := bypass pre tail w (varWord u) Finset.univ i (by decide) imp C.cleanPre (Or.inr (free_in _ _)) C.cleanTail C.hit
    have n := C.limit
    omega
  have support (x y : V) : supported ({x}∪{y}) (varWord x|||varWord y) := ctrl_join true (ctrl_raw _) (ctrl_raw _)
  have size (x y : V) : (({x} : R)∪{y}).card≤3 := by
    exact (Finset.card_union_le _ _).trans (by simp)
  by_cases pq : p=q
  · subst q
    exact incr p z _ (size a b) (support a b) (by simpa only [f,BitVec.or_self] using box)
  by_cases ab : a=b
  · subst b
    exact incr a f _ (size p q) (support p q) (by rw [box];unfold z;rw [BitVec.or_self,BitVec.and_comm])
  have fraw := union_new p q pq
  have zraw := union_new a b ab
  have fnz : f≠0 := by
    intro zero
    have h : (varWord p).getLsbD (rneg (Classical.choose (raw_alive p)))=true := Classical.choose_spec (raw_alive p)
    have h1 : f.getLsbD (rneg (Classical.choose (raw_alive p)))=true := by simp [f,h]
    simp [zero] at h1
  have znz : z≠0 := by
    intro zero
    have h : (varWord a).getLsbD (rneg (Classical.choose (raw_alive a)))=true := Classical.choose_spec (raw_alive a)
    have h1 : z.getLsbD (rneg (Classical.choose (raw_alive a)))=true := by simp [z,h]
    simp [zero] at h1
  have mf : f∈pre.foldl step input := by
    have v := read_free (pre.foldl step input) g.2.1.val
    rw [left] at v
    exact v.resolve_left fnz
  have mz : z∈pre.foldl step input := by
    have v := read_free (pre.foldl step input) g.2.2.val
    rw [right] at v
    exact v.resolve_left znz
  have diff : f≠z := by
    intro eq
    have same : w=f := by rw [box,←eq];exact BitVec.and_self
    exact C.no_copy (Or.inr mf) same
  have share (x u v : V) (ff : f=varWord x|||varWord u) (zz : z=varWord x|||varWord v) : False := by
    by_cases same : u=v
    · exact diff (ff.trans (same.symm ▸ zz.symm))
    · obtain ⟨loss,neg⟩ := shared_literal x u v same
      have eq : w=(varWord x|||varWord u)&&&(varWord x|||varWord v) := by rw [box,ff,zz]
      rw [←eq] at loss neg
      have lim := cheap_repair pre tail w (varWord x) i C.cleanPre (Or.inr (free_in _ _)) loss neg C.cleanTail C.hit
      have total := C.limit
      omega
  have fr : f=varWord q|||varWord p := BitVec.or_comm _ _
  have zr : z=varWord b|||varWord a := BitVec.or_comm _ _
  by_cases pa : p=a
  · subst a;exact share p q b rfl rfl
  by_cases pb : p=b
  · subst b;exact share p q a rfl zr
  by_cases qa : q=a
  · subst a;exact share q p b fr rfl
  by_cases qb : q=b
  · subst b;exact share q p a fr zr
  let A : Finset Word := {f,z,w}
  let gs := pre++g::tail
  have correct : (gs.foldl step input).getD i 0=goal := by simpa [gs,List.foldl_append] using C.hit
  have perm : Cut.permitted A input gs := Cut.permits_one C A (by simp [A,w])
  have top := Cut.named_three C f z diff mf mz fraw zraw
  change Cut.adviceCost A input gs≤23 at top
  dsimp only [A] at perm top
  rw [box] at perm top
  have count := rectangle_advice p q a b pq ab pa pb qa qb gs i (box ▸ enough) perm correct
  change 24≤Cut.adviceCost {f,z,f&&&z} input gs at count
  omega
end HeawoodClean

namespace HeawoodClean
open HeawoodCrossing
theorem up_to_two (pre tail : List Gate) (g : Gate) (i : Nat) (small : pre.length≤1)
    (h : Candidate pre tail g i) : False := by
  obtain ⟨la,lb,ne,_⟩ := h.pins (by omega)
  cases pre with
  | nil => exact la (basic_input _)
  | cons k ks =>
    have eq : ks=[] := by apply List.length_eq_zero_iff.mp;simp only [List.length_cons] at small;omega
    subst ks
    let w := value input k
    have both (j : Nat) (nb : ¬basic ((input++[w]).getD j 0)) : (input++[w]).getD j 0=w :=
      List.mem_singleton.mp ((basic_extra [w] j).resolve_left nb)
    exact ne ((both _ la).trans (both _ lb).symm)

theorem sole_third (first second : Gate) (tail : List Gate) (g : Gate) (i : Nat)
    (h : Candidate [first,second] tail g i) : False := by
  let f := value input first
  let z := value (step input first) second
  let H := value ([first,second].foldl step input) g
  obtain ⟨p,q,a,b,pq,ab,F,Z,box⟩ := shape_two h
  change f=varWord p|||varWord q at F
  change z=varWord a|||varWord b at Z
  change H=f&&&z at box
  let xs := [first,second].foldl step input
  have decomp : xs=input++[f,z] := by simp [xs,f,z,step,value]
  obtain ⟨la,lb,ne,_⟩ := h.pins (by simp)
  have options (j : Nat) (notRaw : ¬basic (xs.getD j 0)) : xs.getD j 0=f ∨ xs.getD j 0=z := by
    rw [decomp] at notRaw ⊢
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using ((basic_extra [f,z] j).resolve_left notRaw)
  rcases options g.2.1.val la with l|l <;> rcases options g.2.2.val lb with r|r
  · exact ne (l.trans r.symm)
  · exact excluded_union_operands h p q a b (l.trans F) (r.trans Z)
  · exact excluded_union_operands h a b p q (l.trans Z) (r.trans F)
  · exact ne (l.trans r.symm)

theorem sole_violation_after_three (pre tail : List Gate) (g : Gate) (i : Nat)
    (candidate : Candidate pre tail g i) : 3≤pre.length := by
  by_contra! early
  by_cases tiny : pre.length≤1
  · exact up_to_two pre tail g i tiny candidate
  · cases pre with
    | nil => simp at tiny
    | cons first rest =>
      cases rest with
      | nil => simp at tiny
      | cons second rest =>
        have endAt : rest=[] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons] at early
          omega
        subst rest
        exact sole_third first second tail g i candidate
end HeawoodClean

namespace HeawoodClean.Cut
open HeawoodCrossing
def largeOrAt (v : V) (w : Word) : Prop :=
  ∃ X : R, 2≤(X∩N v).card ∧ ∀ r : Nat, w.getLsbD r=true ↔ Hits X r

theorem largeOr_ready {v : V} {w : Word} (ok : largeOrAt v w) :
    Ready (seed (incident v)) w := by
  obtain ⟨X,big,word⟩ := ok
  refine ⟨X,fun r => (word r).mpr,fun e yes => Or.inl ((word e.val).mp yes),?_,?_⟩
  · intro c sub
    have eq := unique_center (X:=X∩N v) big
        ((Finset.inter_subset_left : X∩N v ⊆ X).trans sub) Finset.inter_subset_right
    subst c
    have all : star v X ⊆ incident v := by
      intro e mem
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(star_mem.mp mem).1⟩
    exact rich_seed.mpr (by simp [Finset.sdiff_eq_empty_iff_subset.mpr all])
  · intro small
    have le := Finset.card_le_card (Finset.inter_subset_left : X∩N v ⊆ X)
    omega

theorem onStar_proxy (v : V) (w : Word) (supported : positives w ⊆ incident v) :
    proxy Finset.univ (seed (incident v)) w := by
  let z := varWord v &&& goal
  have sub : positives z ⊆ incident v := by
    intro e mem
    have bit : (varWord v).getLsbD e.val=true := by simpa [positives,z,target_pos e] using mem
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,bit⟩
  have dom : Dom z {v} := by
    intro e yes
    exact ⟨v,by simp,(Finset.mem_filter.mp (sub (Finset.mem_filter.mpr ⟨Finset.mem_univ _,yes⟩))).2⟩
  refine ⟨z,⟨?_,?_⟩,seeded_word z sub v dom⟩
  · intro e _ yes
    have on : (varWord v).getLsbD e.val=true :=
      (Finset.mem_filter.mp (supported (Finset.mem_filter.mpr ⟨Finset.mem_univ _,yes⟩))).2
    simp [z,on,target_pos e]
  · intro k yes
    simp [z,target_neg k] at yes

theorem star_advice (v : V) (A : Finset Word) (gs : List Gate) (i : Nat)
    (free : ∀ w∈A, positives w⊆incident v ∨ largeOrAt v w)
    (perm : permitted A input gs) (hit : (gs.foldl step input).getD i 0=goal) :
    24≤adviceCost A input gs := by
  have all : ∀ w∈A,proxy Finset.univ (seed (incident v)) w := by
    intro w hw
    rcases free w hw with star|disj
    · exact onStar_proxy v w star
    · exact ⟨w,imp_refl _ _,largeOr_ready disj⟩
  have low := advice_bound A Finset.univ (incident v) gs i (seed (incident v)) 0 0 0 (seed_zero _) all perm hit
  have count := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (incident v))
  rw [regular v] at count
  simp only [Finset.card_univ,Fintype.card_fin] at low count
  omega
end HeawoodClean.Cut

namespace HeawoodClean.Cut
open HeawoodCrossing UnionBudget
set_option maxHeartbeats 900000 in
theorem novel_program {D : Group} (gs : List Gate) (xs : List Word) (s : Pool) (r l t : Nat)
    (B : Budget D s r l t) (old : ∀ w∈xs, Ready s w) (cleaned : CleanTrace xs gs) :
    ∃ z r' l' t', Budget D z r' l' t' ∧ r'+l'+t'=r+l+t+novelCount xs gs ∧
      ∀ w∈gs.foldl step xs, Ready z w := by
  induction gs generalizing xs s r l t with
  | nil => exact ⟨s,r,l,t,B,by simp [novelCount],old⟩
  | cons g gs ih =>
    have nextClean : CleanTrace (step xs g) gs :=
      fun e he hf => cleaned e (List.Mem.tail _ he) hf
    by_cases free : value xs g=0 ∨ value xs g∈xs
    · have newReady : ∀ w∈step xs g, Ready s w := by
        intro w hw
        rcases List.mem_append.mp hw with h|h
        · exact old _ h
        · have eq : w=value xs g := List.mem_singleton.mp h
          rw [eq]
          rcases free with fq|fm
          · rw [fq];exact ⟨_,zero_wire (plain B)⟩
          · exact old _ fm
      obtain ⟨z,R,L,T,done,size,get⟩ := ih _ _ _ _ _ B newReady nextClean
      exact ⟨z,R,L,T,done,by rw [novelCount,ite_eq_left free,zero_add];exact size,get⟩
    · obtain ⟨X,hX⟩ := ready_read (plain B) old g.2.1.val
      obtain ⟨Y,hY⟩ := ready_read (plain B) old g.2.2.val
      have advance : Advance D s r l t (value xs g) := by
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
      simp only [novelCount,ite_eq_right free];omega



end HeawoodClean.Cut

namespace HeawoodClean.Cut
open HeawoodCrossing UnionBudget

theorem clean_count0 (gs : List Gate) (xs : List Word) (ct : CleanTrace xs gs) : countMarked xs gs=0 := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    have tail : CleanTrace (step xs g) gs := fun e he h => ct e (List.Mem.tail _ he) h
    have off : marked xs g=false := by
      by_contra! on
      have bad := mark_dirty (Bool.eq_true_of_not_eq_false on)
      have op : g.1=false := by cases hh : g.1 <;> simp_all [marked]
      have ok := ct (g.1,xs.getD g.2.1.val 0,xs.getD g.2.2.val 0) (List.Mem.head _) op
      exact bad (by simpa only [value,combine,op,Bool.false_eq_true,↓reduceIte] using ok)
    simp [countMarked,off,ih _ tail]

def coverFloor (T : Group) (k : Nat) : Prop :=
  ∀ X : R, (∀ e∈T, Hits X e.val) → k≤X.card

theorem floor_budget {D s r l t T w k} (B : Budget D s r l t)
    (ready : Ready s w) (safe : clean w) (keep : T⊆positives w) (floor : coverFloor T k) :
    k≤l+1 := by
  obtain ⟨X,h⟩ := ready
  have none : X=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    obtain ⟨j,hj⟩ := raw_alive u
    have yes := h.rawSound _ ⟨u,hu,hj⟩
    rw [safe j] at yes
    contradiction
  subst X
  obtain ⟨P,hP,dom⟩ := h.cover (by simp)
  exact (floor P (fun e he => dom e (Finset.mem_filter.mp (keep he)).2)).trans (one B.lightCost hP)

theorem zero_cut {pre tail g i} (C : Candidate pre tail g i) (T D : Group)
    (noHot : Disjoint T (positives (value (pre.foldl step input) g)))
    (s : Pool) (r l t : Nat) (B : Budget D s r l t)
    (init : ∀ w∈pre.foldl step input, Ready s w) (cover : Nat) (valid : coverFloor T cover) :
    (T \ D).card+cover ≤ r+l+t+tail.length := by
  let base := pre.foldl step input
  let h := value base g
  let xs := base++[0]
  let ys := step base g
  have init_eq (A : Word → Word → Prop) (rf : ∀ x,A x x) : List.Forall₂ A base base :=
    List.forall₂_of_length_eq_of_get rfl (fun _ _ _ => rf _)
  have imp0 : improvement T 0 h := by
    constructor
    · intro e he yes
      exact False.elim (Finset.disjoint_left.mp noHot he (Finset.mem_filter.mpr ⟨Finset.mem_univ _,yes⟩))
    · intro k no;simp at no
  have rel : List.Forall₂ (improvement T) xs ys := List.rel_append (init_eq _ (imp_refl T)) (.cons imp0 .nil)
  obtain ⟨ct,relEnd⟩ := imp_run xs ys tail rel C.cleanTail
  have also : ∀ z∈xs, Ready s z := by
    intro z hz
    rcases List.mem_append.mp hz with raw|zero
    · exact init _ raw
    · have eq : z=0 := List.mem_singleton.mp zero
      rw [eq];exact ⟨_,zero_wire (plain B)⟩
  obtain ⟨endPool,R,L,K,done,total,look⟩ := novel_program tail xs s r l t B also ct
  let w := (tail.foldl step xs).getD i 0
  have order := imp_read relEnd i
  change improvement T w ((tail.foldl step ys).getD i 0) at order
  have hit : (tail.foldl step ys).getD i 0=goal := C.hit
  rw [hit] at order
  have safe : clean w := by
    intro k;cases e : w.getLsbD (rneg k)
    · rfl
    · exact (order.2 k e).symm.trans (target_neg k)
  have keep : T ⊆ positives w := fun e he => Finset.mem_filter.mpr ⟨Finset.mem_univ _,order.1 e he (target_pos e)⟩
  obtain ⟨area,light⟩ := bounds done w safe (ready_read (plain done) look i) T keep
  have exactCover := floor_budget done (ready_read (plain done) look i) safe keep valid
  have lim := C.limit
  have len : xs.length+tail.length≤40 := by
    have sizes (ss : List Gate) (vs : List Word) : (ss.foldl step vs).length=vs.length+ss.length := by
      induction ss generalizing vs with
      | nil => simp
      | cons k rest ih => simp [ih,step,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    change (base++[0]).length+tail.length≤40
    simp only [List.length_append,List.length_singleton,base,sizes]
    have n : input.length=14 := rfl
    omega
  have preRel : List.Forall₂ SameOrMarked xs ys := List.rel_append
    (init_eq _ (fun x => Or.inl rfl)) (.cons (Or.inr ⟨rfl,mark_dirty C.dirtyGate⟩) .nil)
  obtain ⟨maxCost,equal⟩ := charge_or_match xs ys tail len preRel
  have nothing := clean_count0 tail ys C.cleanTail
  have eq := count_zero_nochange tail ys nothing
  simp only [nothing,eq,Nat.add_zero] at maxCost equal
  have less : novelCount xs tail<tail.length := by
    by_contra! saturated
    have same := same_read (equal (by omega)) i
    change SameOrMarked w ((tail.foldl step ys).getD i 0) at same
    rw [hit] at same
    have out : w=goal := same.resolve_right (fun z => z.2 target_neg)
    have before : ∀ v∈input,Ready start v := by
      intro v hv;obtain ⟨u,rfl⟩ := raw_list v hv
      exact ⟨_,input_wire startBudget u⟩
    obtain ⟨P,R₁,L₁,K₁,preB,pc,ready⟩ := HeawoodClean.program pre input start 0 0 0 startBudget before C.cleanPre
    have avail : ∀ v∈xs,Ready P v := by
      intro v hv
      rcases List.mem_append.mp hv with e|e
      · exact ready v e
      · have z : v=0 := List.mem_singleton.mp e
        rw [z];exact ⟨_,zero_wire preB⟩
    obtain ⟨Q,R₂,L₂,K₂,postB,qc,fin⟩ := HeawoodClean.program tail xs P R₁ L₁ K₁ preB avail ct
    have atEnd : Ready Q w := ready_read postB fin i
    rw [out] at atEnd
    have lower := output_lower postB atEnd
    omega
  omega
end HeawoodClean.Cut

#print axioms HeawoodClean.reader_tradeoff
#print axioms HeawoodClean.three_mixed_edges
#print axioms HeawoodClean.Cut.advice_bound
#print axioms HeawoodClean.excluded_union_operands
#print axioms HeawoodClean.sole_violation_after_three
#print axioms HeawoodClean.Cut.star_advice
#print axioms HeawoodClean.Cut.zero_cut
