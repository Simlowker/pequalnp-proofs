import PEqualNP.Outside.L_meta_12691
import PEqualNP.Outside.L_meta_9526

-- Essential-input splitting with a fixed NOT budget, from Simlowker L-meta-11971.
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



namespace Simlowker.OrTwins12692
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Simlowker.Twins11971
abbrev G := Bool × Nat × Nat
def cores : List (List G) := [
  [(true,2,3),(false,2,3),(false,0,4),(false,0,5),(true,1,6),(true,4,8),(true,7,9),(false,10,11)],
  [(true,2,3),(false,2,3),(false,0,4),(false,0,5),(true,1,7),(true,4,8),(true,6,9),(false,10,11)],
  [(true,2,3),(false,2,3),(true,1,6),(true,0,7),(false,0,7),(false,5,9),(true,4,10),(false,8,11)],
  [(true,2,3),(false,2,3),(true,1,6),(true,0,7),(false,5,7),(false,0,9),(true,4,10),(false,8,11)],
  [(true,2,3),(false,2,3),(false,0,4),(false,0,5),(true,1,6),(true,4,8),(false,9,10),(true,7,11)],
  [(true,2,3),(false,2,3),(false,0,4),(false,0,5),(true,6,7),(true,4,8),(true,1,9),(false,10,11)],
  [(true,2,3),(false,2,3),(true,1,6),(true,0,7),(false,0,7),(false,4,8),(false,5,9),(true,10,11)],
  [(true,2,3),(false,2,3),(true,1,6),(true,0,7),(false,5,7),(false,4,8),(false,0,9),(true,10,11)],
  [(true,2,3),(false,2,3),(true,1,6),(false,4,7),(false,5,7),(true,0,8),(true,4,9),(false,10,11)],
  [(true,2,3),(false,2,3),(true,1,6),(false,4,7),(false,5,7),(true,4,9),(false,0,10),(true,8,11)],
  [(true,2,3),(false,2,3),(false,0,5),(true,1,6),(true,0,8),(false,7,8),(false,4,9),(true,10,11)],
  [(true,2,3),(false,2,3),(false,0,5),(true,1,6),(true,0,8),(false,7,8),(true,4,10),(false,9,11)]]
def circuit (gs : List G) : Circuit :=
  ⟨gs.map (fun g => ⟨if g.1 then .and else .or,[g.2.1,g.2.2]⟩), 4+gs.length⟩

def core (x : Fin 5 → Bool) : Bool :=
  (x 4 && (x 0 || (x 2 && x 3))) || ((x 1 && (x 2 || x 3)) && (x 0 || x 4))
set_option maxRecDepth 10000 in
theorem all_witnesses : cores.Nodup ∧ cores.length=12 ∧ cores.all (fun gs =>
    decide (gs.length=8 ∧ ∀ x : Fin 5 → Bool,(circuit gs).eval (List.ofFn x)=core x))=true := by decide +kernel

theorem size_lower (s : Nat) (h : HasCircuitSize 5 core s) : 8 ≤ s := by
  apply PEqualNP.Outside.L_meta_12691.base s
  obtain ⟨C,ok,sz,ev⟩ := h
  refine ⟨C,ok,sz,fun x => (ev x).trans ?_⟩
  revert x
  decide +kernel

theorem size_for_every_expansion {n d : Nat} {g : (Fin n → Bool) → Bool}
    (h : Expansion core g d) (s k : Nat) : Fits n g s k ↔ 8+d ≤ s := by
  rw [expansion_budget h s k]
  constructor
  · rintro ⟨t,le,C,ok,sz,_,ev⟩
    have lo := size_lower t ⟨C,ok,sz,ev⟩
    omega
  · intro le
    let C := circuit (cores.getD 0 [])
    have ok : FanInTwo C := by simp [C,circuit,cores,FanInTwo]
    have ev : ∀ x : Fin 5 → Bool,C.eval (List.ofFn x)=core x := by decide +kernel
    exact ⟨8,le,C,ok,le_rfl,by exact Nat.zero_le k,ev⟩

-- Replacing selected occurrences of a single wire by its OR with a fresh input.
-- When the new input is zero the network is unchanged. At one, each selected
-- port becomes the word of 32 ones on the five old inputs.
abbrev W := BitVec 32
def columns : List W := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
def uses (gs : List G) (v : Nat) : List Nat := Id.run do
  let mut result := []
  for (g,j) in gs.zipIdx do
    if g.2.1=v then result := result ++ [2*j]
    if g.2.2=v then result := result ++ [2*j+1]
  if 4+gs.length=v then result := result ++ [2*gs.length]
  return result

def value (gs : List G) (ports : List Nat) : W := Id.run do
  let mut words := columns
  for (g,j) in gs.zipIdx do
    let a := if ports.contains (2*j) then (-1 : W) else words.getD g.2.1 0
    let b := if ports.contains (2*j+1) then (-1 : W) else words.getD g.2.2 0
    words := words ++ [if g.1 then a &&& b else a ||| b]
  return if ports.contains (2*gs.length) then -1 else words.getD (4+gs.length) 0
def validSites (gs : List G) : List (Nat × List Nat) := (List.range (5+gs.length)).flatMap fun v =>
  ((uses gs v).sublists.filter fun ss => !ss.isEmpty && value gs ss == 0xfeeafeea).map fun ss => (v,ss)
def sites : List (List (Nat × List Nat)) := [
[(4,[5, 10])],
  [(4,[5, 10])],
  [(4,[12])],
  [(4,[12])],
  [(4,[5, 10])],
  [(4,[5, 10])],
  [(4,[10]),(8,[11]),(10,[14])],
  [(4,[10]),(8,[11]),(10,[14])],
  [(4,[6, 12])],
  [(4,[6, 10])],
  [(4,[12]),(9,[13]),(11,[15])],
  [(4,[12])]]
theorem attachment_table : cores.map validSites=sites := by decide +kernel
theorem two_tables : ∀ x : Fin 5 → Bool,
    (0xfeea8880 : Nat).testBit (∑ i : Fin 5, if x i then 2^i.val else 0)=core x ∧
    (0xfeeafeea : Nat).testBit (∑ i : Fin 5, if x i then 2^i.val else 0)=core (Function.update x 4 true) := by decide +kernel

-- The three mixed cores have one OR of z and H, with H = a AND b AND (c OR d).
def wireValues (gs : List G) : List W := gs.foldl (fun ws g =>
  let a := ws.getD g.2.1 0
  let b := ws.getD g.2.2 0
  ws ++ [if g.1 then a &&& b else a ||| b]) columns
def marked (gs : List G) (h joint : Nat) : Bool :=
  let edges := uses gs h
  let code := gs.getD (joint-5) (true,0,0)
  decide (code=(false,4,h) ∧ uses gs 4=[2*(joint-5)] ∧ edges=[2*(joint-5)+1] ∧
    (uses gs joint).length=1 ∧
    (wireValues gs).getD h 0 = 0x88808880 ∧
    (wireValues gs).getD joint 0 = 0xffff8880)
theorem marked_cores : marked (cores.getD 6 []) 8 10=true ∧
    marked (cores.getD 7 []) 8 10=true ∧ marked (cores.getD 10 []) 9 11=true := by decide +kernel
end Simlowker.OrTwins12692
#print axioms Simlowker.OrTwins12692.all_witnesses
#print axioms Simlowker.OrTwins12692.size_for_every_expansion
#print axioms Simlowker.OrTwins12692.attachment_table
#print axioms Simlowker.OrTwins12692.two_tables
#print axioms Simlowker.OrTwins12692.marked_cores

namespace Simlowker.OrTwins12692
open Simlowker.Twins11971
def port4 (d : Nat) : Fin (5+d) := ⟨4,by omega⟩
def block : (d : Nat) → (Fin (5+d) → Bool) → Bool
  | 0 => core
  | d+1 => fun x => block d (merge (port4 d) false x)
def probe (d : Nat) (b : Bool) (i : Fin (5+d)) := decide (i.val=0) || (decide (i.val=4) && b)
theorem merge_probe (d : Nat) (b : Bool) : merge (port4 d) false (probe (d+1) b)=probe d b := by
  funext i
  have h4 : 5+d ≠ 4 := by omega
  by_cases h : i=port4 d
  · subst i
    simp [merge,probe,port4,combine,h4]
  · simp [merge,h,probe]
theorem block_probe (d : Nat) (b : Bool) : block d (probe d b)=b := by
  induction d with
  | zero => cases b <;> decide +kernel
  | succ d ih => simpa only [block,merge_probe] using ih
theorem block_expansion (d : Nat) : Expansion core (block d) d := by
  induction d with
  | zero => exact Expansion.base
  | succ d ih =>
    apply Expansion.split ih (port4 d) false
    refine ⟨probe d false,?_⟩
    have update : Function.update (probe d false) (port4 d) (!(probe d false (port4 d)))=probe d true := by
      funext i
      by_cases h : i=port4 d
      · subst i; simp [probe,port4]
      · have ne : i.val ≠ 4 := by intro eq; apply h; exact Fin.ext eq
        simp [Function.update_of_ne h,probe,ne]
    rw [update,block_probe,block_probe]
    decide
theorem exact_block_cost (d s k : Nat) : Fits (5+d) (block d) s k ↔ 8+d ≤ s :=
  size_for_every_expansion (block_expansion d) s k
end Simlowker.OrTwins12692
#print axioms Simlowker.OrTwins12692.exact_block_cost
