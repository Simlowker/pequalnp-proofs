import PEqualNP.Outside.L_meta_9526
import PEqualNP.Outside.L_meta_11970
import PEqualNP.Library.LRAT.Link2

/-!
# Exact circuit cost of duplicating an essential input

In the project's fan-in-two AND/OR/NOT model, replace an essential input by the
AND or OR of two inputs. The minimum size increases by one at every fixed budget
of NOT gates (`split_budget`). After any sequence of `d` splits the increase is
exactly `d` (`expansion_budget`).

For the seven-vertex graph in L-meta-11970/11971 the split reduces its edge function
to the cone over the five-vertex path. `exact_core` and `exact_posted` derive the
optima 10 and 11 from the explicit unsatisfiability hypothesis for `Graph.formula`.
The README explains how to reproduce that part independently with a SAT solver and
an LRAT checker. The computation is external to the Lean kernel.

Credits: hilelyos's restriction and circuit remapping infrastructure (L-meta-9526),
Leg0shii's binary lower bound and monotone upper witness (L-meta-11970, PR 16070),
and the project's LRAT encoding and soundness theorem in `Library.LRAT.Link2`.
-/


namespace Simlowker.Twins11971
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9526

-- Splitting an input into two inputs combined by OR or AND.
def combine (conj a b : Bool) : Bool := if conj then a && b else a || b

def merge {n : Nat} (p : Fin n) (conj : Bool) (x : Fin (n+1) → Bool) (i : Fin n) : Bool :=
  if i = p then combine conj (x p.castSucc) (x (Fin.last n)) else x i.castSucc

def prep {n : Nat} (p : Fin n) (c : Bool) : Gate :=
  ⟨if c then .and else .or, [p.val,n]⟩

def port {n : Nat} (p i : Fin n) : Fin ((n+1)+1) :=
  if i = p then Fin.last (n+1) else i.castSucc.castSucc

def splitCircuit {n : Nat} (p : Fin n) (c : Bool) (C : Circuit) : Circuit :=
  ⟨prep p c :: (remap n ((n+1)+1) (port p) C).gates,(remap n ((n+1)+1) (port p) C).output⟩

theorem prep_eval {n : Nat} (p : Fin n) (c : Bool) (x : Fin (n+1) → Bool) :
    step (List.ofFn x) (prep p c) =
      List.ofFn (Fin.snoc x (combine c (x p.castSucc) (x (Fin.last n)))) := by
  rw [ofFn_snoc]
  have hp : (List.ofFn x).getD p.val false = x p.castSucc := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
  have hn : (List.ofFn x).getD n false = x (Fin.last n) := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
  unfold step
  apply congrArg (fun b => List.ofFn x ++ [b])
  cases c <;> simp only [prep,List.map_cons,List.map_nil,hp,hn] <;> simp [GateOp.eval,combine]

theorem split_eval {n : Nat} (p : Fin n) (c : Bool) (C : Circuit) (x : Fin (n+1) → Bool) :
    (splitCircuit p c C).eval (List.ofFn x) = C.eval (List.ofFn (merge p c x)) := by
  let z : Fin ((n+1)+1) → Bool := Fin.snoc x (combine c (x p.castSucc) (x (Fin.last n)))
  have hz : z ∘ port p = merge p c x := by
    funext i
    by_cases eq : i = p
    · subst i; simp [z,port,merge]
    · simp [z,port,merge,eq]
  have h := (rel_fold n ((n+1)+1) (port p) C.gates _ _ (rel_init n _ (port p) z)).2.2 C.output
  rw [hz] at h
  change (((C.gates.map (relGate n ((n+1)+1) (port p))).foldl step
    (step (List.ofFn x) (prep p c))).getD (wmap n ((n+1)+1) (port p) C.output) false) = _
  rw [prep_eval]
  exact h

theorem split_size {n : Nat} (p : Fin n) (c : Bool) (C : Circuit) :
    (splitCircuit p c C).size = C.size + 1 := by simp [splitCircuit,remap,Circuit.size]

theorem split_legal {n : Nat} (p : Fin n) (c : Bool) (C : Circuit) (ok : FanInTwo C) :
    FanInTwo (splitCircuit p c C) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | h
  · cases c <;> simp [prep]
  · obtain ⟨g₀,mem,rfl⟩ := List.mem_map.mp h
    exact ⟨(ok _ mem).1,by simpa [relGate] using (ok _ mem).2⟩

theorem split_mono {n : Nat} (p : Fin n) (c : Bool) (C : Circuit) (ok : Monotone2 C) :
    Monotone2 (splitCircuit p c C) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | h
  · cases c <;> simp [prep]
  · obtain ⟨g₀,mem,rfl⟩ := List.mem_map.mp h
    exact ⟨(ok _ mem).1,by simpa [relGate] using (ok _ mem).2⟩

theorem neutral {n : Nat} (p : Fin n) (c : Bool) (x : Fin n → Bool) :
    merge p c (Fin.snoc x c) = x := by
  funext i
  by_cases eq : i = p
  · subst i; cases c <;> simp [merge,combine]
  · simp [merge,eq]

theorem split_essential {n : Nat} (p : Fin n) (c : Bool) (f : BFn n)
    (dep : ∃ x, f (Function.update x p (!x p)) ≠ f x) :
    ∃ y : Fin (n+1) → Bool, f (merge p c (Function.update y (Fin.last n) (!y (Fin.last n)))) ≠
      f (merge p c y) := by
  obtain ⟨x,hx⟩ := dep
  let x₀ := Function.update x p c
  let x₁ := Function.update x p (!c)
  have diff : f x₁ ≠ f x₀ := by
    by_cases hp : x p = c
    · have e : x₀ = x := by simp [x₀,← hp]
      simpa [x₁,e,hp] using hx
    · have hp' : x p = !c := by cases h : x p <;> cases c <;> simp_all
      have e : x₁ = x := by simp [x₁,← hp']
      have flip : (!x p) = c := by simp [hp']
      simpa [x₀,e,flip] using hx.symm
  refine ⟨Fin.snoc x₀ c,?_⟩
  rw [neutral]
  apply (fun eq => diff eq) ∘ ?_
  intro eq
  have changed : merge p c (Function.update (Fin.snoc x₀ c) (Fin.last n)
      (!(Fin.snoc x₀ c : Fin (n+1) → Bool) (Fin.last n))) = x₁ := by
    funext i
    have distinct : i.castSucc ≠ Fin.last n := Fin.castSucc_ne_last i
    have dp : p.castSucc ≠ Fin.last n := Fin.castSucc_ne_last p
    by_cases h : i = p
    · subst i; cases c <;> simp [merge,combine,x₀,x₁,Function.update_of_ne,dp]
    · simp [merge,x₀,x₁,h,Function.update_of_ne,distinct]
  rwa [changed] at eq

theorem exact_split {n : Nat} (p : Fin n) (c : Bool) (f : BFn n)
    (dep : ∃ x, f (Function.update x p (!x p)) ≠ f x) (s : Nat) :
    HasCircuitSize (n+1) (fun y => f (merge p c y)) s ↔
      ∃ t, t+1 ≤ s ∧ HasCircuitSize n f t := by
  constructor
  · intro h
    obtain ⟨x,hx⟩ := dep
    obtain ⟨t,ht,hc⟩ := gate_elim_one n (fun y => f (merge p c y)) c s (split_essential p c f ⟨x,hx⟩)
      ⟨Function.update x p (!x p),x,by simpa only [neutral] using hx⟩ h
    exact ⟨t,ht,by simpa only [neutral] using hc⟩
  · rintro ⟨t,ht,C,ok,cost,comp⟩
    exact ⟨splitCircuit p c C,split_legal p c C ok,by rw [split_size]; omega,
      fun x => (split_eval p c C x).trans (comp _)⟩
end Simlowker.Twins11971

namespace Simlowker.Twins11971
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9526

def opNeg : GateOp → Bool | .not => true | _ => false
def isNeg (g : Gate) : Bool := opNeg g.op
def Fits (n : Nat) (f : BFn n) (s k : Nat) : Prop := ∃ C : Circuit,
  FanInTwo C ∧ C.size ≤ s ∧ C.gates.countP isNeg ≤ k ∧ ∀ x, C.eval (List.ofFn x) = f x

theorem fits_mono {n : Nat} {f : BFn n} {s s' k : Nat} (h : Fits n f s k) (le : s ≤ s') :
    Fits n f s' k := by
  obtain ⟨C,ok,cost,neg,eval⟩ := h
  exact ⟨C,ok,cost.trans le,neg,eval⟩

theorem normal_neg (g : Gate) : isNeg (normGate g) = isNeg g := by
  rcases g with ⟨op,ins⟩
  cases op <;> rfl

theorem simplify_fee (op : GateOp) (m : ℕ) (vals : List Stat) :
   ((simplify op m vals).1.toList).countP isNeg ≤ (opNeg op).toNat := by
  cases op <;> rcases vals with _ | ⟨a,_ | ⟨b,_ | ⟨d,r⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
    simp [simplify,simpAnd,simpOr,simpNot,isNeg,opNeg]

theorem elim_fee (n : Nat) (gs : List Gate) (acc : List Stat × List Gate) :
    (elim n gs acc).2.countP isNeg ≤ acc.2.countP isNeg + gs.countP isNeg := by
  induction gs generalizing acc with
  | nil => simp [elim]
  | cons g gs ih =>
    rw [elim_cons]
    have tail := ih (elimStep n acc g)
    have fee := simplify_fee g.op (n+acc.2.length) (g.inputs.map fun i => acc.1.getD i (.inl false))
    apply tail.trans
    simp only [elimStep,List.countP_append,List.countP_cons]
    cases b : isNeg g <;> simp <;>
      (change opNeg g.op = _ at b; simp [b] at fee; omega)

theorem split_fee {n : Nat} (p : Fin n) (c : Bool) (C : Circuit) :
    (splitCircuit p c C).gates.countP isNeg = C.gates.countP isNeg := by
  cases c <;> simp [splitCircuit,remap,prep,List.countP_map,Function.comp_def,relGate,isNeg,opNeg] <;> rfl
theorem restrict_bounded (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (k : Nat) (h : Fits (n+1) f s k) :
    ∃ s', s' + 1 ≤ s ∧ Fits n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' k := by
  obtain ⟨C, ok, hsz, hneg, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length + 1 ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    have fee := elim_fee n gs (initStats n b,[])
    have keep : acc.2.countP isNeg ≤ k := by
      rw [← hacc] at fee
      simp only [List.countP_nil,Nat.zero_add,hgs,List.countP_map] at fee
      simpa only [Function.comp_def,normal_neg] using fee.trans (by simpa only [Function.comp_def,normal_neg] using hneg)
    refine ⟨acc.2.length, hlen, ⟨acc.2, j⟩, elim_ok n gs _ (by simp), le_refl _, keep, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this


theorem split_budget {n : Nat} (p : Fin n) (c : Bool) (f : BFn n)
    (dep : ∃ x, f (Function.update x p (!x p)) ≠ f x) (s k : Nat) :
    Fits (n+1) (fun y => f (merge p c y)) s k ↔ ∃ t, t+1 ≤ s ∧ Fits n f t k := by
  constructor
  · intro h
    obtain ⟨x,hx⟩ := dep
    obtain ⟨t,ht,hc⟩ := restrict_bounded n (fun y => f (merge p c y)) c s (split_essential p c f ⟨x,hx⟩)
      ⟨Function.update x p (!x p),x,by simpa only [neutral] using hx⟩ k h
    exact ⟨t,ht,by simpa only [neutral] using hc⟩
  · rintro ⟨t,ht,C,ok,size,fee,ev⟩
    exact ⟨splitCircuit p c C,split_legal p c C ok,by rw [split_size]; omega,
      by rwa [split_fee],fun x => (split_eval p c C x).trans (ev _)⟩

def saving {n : Nat} (f : BFn n) (k : Nat) := ∃ s, Fits n f s k ∧ ¬ Fits n f s 0

theorem saving_iff {n : Nat} (p : Fin n) (c : Bool) (f : BFn n)
    (dep : ∃ x, f (Function.update x p (!x p)) ≠ f x) (k : Nat) :
    saving (fun y => f (merge p c y)) k ↔ saving f k := by
  constructor
  · rintro ⟨s,hs,no⟩
    obtain ⟨t,ht,hk⟩ := (split_budget p c f dep s k).mp hs
    exact ⟨t,hk,fun hz => no ((split_budget p c f dep s 0).mpr ⟨t,ht,hz⟩)⟩
  · rintro ⟨s,hs,no⟩
    refine ⟨s+1,(split_budget p c f dep _ k).mpr ⟨s,le_rfl,hs⟩,?_⟩
    intro hz
    obtain ⟨t,ht,hh⟩ := (split_budget p c f dep _ 0).mp hz
    exact no (fits_mono hh (by omega))
end Simlowker.Twins11971

namespace Simlowker.Twins11971
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9526

/-- A sequence of AND or OR splits, each at an input on which the current function depends. -/
inductive Expansion {n : Nat} (f : BFn n) : {m : Nat} → BFn m → Nat → Prop
  | base : Expansion f f 0
  | split {m d : Nat} {g : BFn m} (prev : Expansion f g d) (p : Fin m) (c : Bool)
      (dep : ∃ x, g (Function.update x p (!x p)) ≠ g x) :
      Expansion f (fun x => g (merge p c x)) (d+1)

/-- After d splits the minimum shifts by exactly d at every fixed negation budget. -/
theorem expansion_budget {n m d : Nat} {f : BFn n} {g : BFn m} (h : Expansion f g d)
    (s k : Nat) : Fits m g s k ↔ ∃ t, t+d ≤ s ∧ Fits n f t k := by
  induction h generalizing s with
  | base =>
    constructor
    · exact fun hh => ⟨s,by omega,hh⟩
    · rintro ⟨t,le,hh⟩
      exact fits_mono hh (by omega)
  | @split m d g prev p c dep ih =>
    rw [split_budget p c g dep s k]
    constructor
    · rintro ⟨u,hu,hg⟩
      obtain ⟨t,ht,hf⟩ := (ih u).mp hg
      exact ⟨t,by omega,hf⟩
    · rintro ⟨t,ht,hf⟩
      exact ⟨t+d,by omega,(ih (t+d)).mpr ⟨t,le_rfl,hf⟩⟩

end Simlowker.Twins11971


namespace Simlowker.Twins11971.Graph
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9526
open PEqualNP.Outside.L_meta_11970 (posted)

def core (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 4 && x 5)

def order : Fin 7 → Fin 7 := ![1,3,6,0,4,2,5]
def undo : Fin 7 → Fin 7 := ![3,0,5,1,4,6,2]
def split (x : Fin 7 → Bool) := core (merge (3 : Fin 6) false x)

theorem to_split : ∀ x : Fin 7 → Bool, posted (x ∘ order) = split x := by decide +kernel
theorem from_split : ∀ x : Fin 7 → Bool, split (x ∘ undo) = posted x := by decide +kernel
theorem core_dep : ∃ x, core (Function.update x 3 (!x 3)) ≠ core x :=
  ⟨fun i => decide (i.val=4),by decide +kernel⟩

theorem fits_map {n m s k : Nat} (π : Fin n → Fin m) (f : BFn n) (h : Fits n f s k) :
    Fits m (fun x => f (x ∘ π)) s k := by
  obtain ⟨C,ok,cost,fee,ev⟩ := h
  refine ⟨remap n m π C,?_,?_,?_,?_⟩
  · intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact ⟨(ok _ ha).1,by simpa [relGate] using (ok _ ha).2⟩
  · simpa [remap,Circuit.size] using cost
  · change (C.gates.map (relGate n m π)).countP isNeg ≤ k
    rw [List.countP_map]; exact fee
  · intro x
    exact ((rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output).trans (ev _)

theorem posted_budget (s k : Nat) :
    Fits 7 posted s k ↔ ∃ t, t+1 ≤ s ∧ Fits 6 core t k := by
  constructor
  · intro h
    have mapped := fits_map order posted h
    rw [show (fun x : Fin 7 → Bool => posted (x ∘ order)) = split from funext to_split] at mapped
    exact (split_budget 3 false core core_dep s k).mp mapped
  · intro h
    have hs := (split_budget 3 false core core_dep s k).mpr h
    have mapped := fits_map undo split hs
    rwa [show (fun x : Fin 7 → Bool => split (x ∘ undo)) = posted from funext from_split] at mapped

theorem neg_false_iff (g : Gate) : isNeg g = false ↔ g.op ≠ GateOp.not := by
  rcases g with ⟨op,ins⟩; cases op <;> simp [isNeg,opNeg]

theorem mono_of_zero (C : Circuit) (leg : FanInTwo C) (nz : C.gates.countP isNeg ≤ 0) :
    Monotone2 C := by
  intro g hg
  obtain ⟨ops,a⟩ := leg g hg
  have ne : g.op ≠ GateOp.not := by
    apply (neg_false_iff g).mp
    cases e : isNeg g
    · rfl
    · have h := List.countP_pos_iff.mpr ⟨g,hg,e⟩
      omega
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops ⊢
  exact ⟨ops.imp_right (fun h => h.resolve_right ne),a⟩

def rows : List Nat := [3,6,9,10,12,18,21,24,32,33,34,36,40,48]
open PEqualNP.Library.LRAT PEqualNP.Library.LRAT.Link in
def formula := enc2 6 9 (rowFun 6 core) rows

open PEqualNP.Library.LRAT PEqualNP.Library.LRAT.Link in
theorem mono_core_lower (unsat : ¬ FormulaSat formula) (t : Nat) (h : Fits 6 core t 0) : 10 ≤ t := by
  obtain ⟨C,ok,sz,nz,ev⟩ := h
  have := lower_of_unsat2 6 9 core rows (by intro r hr; simp [rows] at hr; omega) unsat C (mono_of_zero C ok nz) ev
  omega

open PEqualNP.Outside.L_meta_11970 in
theorem neg_capacity (gs : List Gate) :
    gs.countP (fun g => !Model.isNot g) + gs.countP isNeg = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rcases g with ⟨op,ins⟩
    cases op <;> simp [List.countP_cons,isNeg,opNeg,Model.isNot] at * <;> omega

open PEqualNP.Library.LRAT PEqualNP.Outside.L_meta_11970 in
theorem exact_posted (unsat : ¬ FormulaSat formula) (s : Nat) : HasCircuitSize 7 posted s ↔ 11 ≤ s := by
  constructor
  · rintro ⟨C,ok,sz,ev⟩
    by_cases no : C.gates.countP isNeg ≤ 0
    · have hb := (posted_budget s 0).mp ⟨C,ok,sz,no,ev⟩
      obtain ⟨t,hs,hh⟩ := hb
      have := mono_core_lower unsat t hh
      omega
    · have fee := binaryLower (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb) C.gates C.output ok ev
      have := neg_capacity C.gates
      change C.gates.length ≤ s at sz
      omega
  · intro hs
    refine ⟨⟨mono,17⟩,?_,hs,monoEval⟩
    intro g hg
    obtain ⟨op,a⟩ := monoShape g hg
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    exact ⟨op.imp_right Or.inl,a⟩

def ten : Circuit := ⟨[⟨.or,[1,4]⟩,⟨.and,[6,5]⟩,⟨.or,[4,2]⟩,⟨.or,[8,5]⟩,
  ⟨.and,[3,9]⟩,⟨.or,[1,5]⟩,⟨.or,[0,2]⟩,⟨.and,[11,12]⟩,⟨.or,[7,10]⟩,⟨.or,[14,13]⟩],15⟩

theorem ten_ok : Monotone2 ten ∧ FanInTwo ten := by simp [ten,Monotone2,FanInTwo]
theorem ten_eval : ∀ x : Fin 6 → Bool, ten.eval (List.ofFn x) = core x := by decide +kernel

open PEqualNP.Library.LRAT in
theorem exact_core (unsat : ¬ FormulaSat formula) (s : Nat) : HasCircuitSize 6 core s ↔ 10 ≤ s := by
  constructor
  · intro h
    have hs := (exact_split 3 false core core_dep (s+1)).mpr ⟨s,le_rfl,h⟩
    have hm := remap_size undo split (s+1) hs
    rw [show (fun y : Fin 7 → Bool => split (y ∘ undo)) = posted from funext from_split] at hm
    have := (exact_posted unsat (s+1)).mp hm
    omega
  · exact fun h => ⟨ten,ten_ok.2,h,ten_eval⟩
end Simlowker.Twins11971.Graph

namespace Simlowker.Twins11971.Graph
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9526
open PEqualNP.Library.LRAT

/-- Every AND/OR expansion of the six-vertex core has exact cost 10+d at every NOT budget. -/
theorem family_exact {m d : Nat} {g : BFn m} (h : Expansion core g d)
    (unsat : ¬ FormulaSat formula) (s k : Nat) : Fits m g s k ↔ 10+d ≤ s := by
  rw [expansion_budget h s k]
  constructor
  · rintro ⟨t,ht,C,ok,cost,_,ev⟩
    have lower := (exact_core unsat t).mp ⟨C,ok,cost,ev⟩
    omega
  · intro hs
    refine ⟨10,hs,ten,ten_ok.2,le_rfl,?_,ten_eval⟩
    exact Nat.zero_le k
end Simlowker.Twins11971.Graph
