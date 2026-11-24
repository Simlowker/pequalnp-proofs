import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace L171


def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi


theorem foldl_step_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl step w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton, foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_step_length, Nat.min_eq_left ht.le]


def deps (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.head?.toList
  | _ => g.inputs

theorem eval_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ i ∈ deps g, f i = f' i) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  obtain ⟨op, l⟩ := g
  cases op with
  | not =>
    cases l with
    | nil => rfl
    | cons a l =>
      simp only [deps, List.head?_cons, Option.toList_some, List.mem_singleton, forall_eq] at h
      simp [GateOp.eval, h]
  | _ =>
    simp only [deps] at h
    rw [List.map_congr_left h]

theorem getD_eraseIdx_lt (l : List Bool) (p i : ℕ) (hi : i < p) :
    (l.eraseIdx p).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_lt hi]

theorem getD_eraseIdx_ge (l : List Bool) (p i : ℕ) (hi : p ≤ i) :
    (l.eraseIdx p).getD i false = l.getD (i + 1) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_ge hi]


def ren (p r i : ℕ) : ℕ := if i < p then i else if i = p then r else i - 1

def renG (p r : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (ren p r)⟩


def del (G : List Gate) (t p r : ℕ) : List Gate := G.take t ++ (G.drop (t + 1)).map (renG p r)

theorem deps_renG (p r : ℕ) (g : Gate) : deps (renG p r g) = (deps g).map (ren p r) := by
  obtain ⟨op, l⟩ := g
  cases op <;> cases l <;> simp [deps, renG]

theorem del_foldl_aux (W : List Bool) (p r : ℕ) (hr : r < p ∨ W.length ≤ r) :
    ∀ (L : List Gate) (v : List Bool), L.foldl step v = W → p < v.length →
      (∀ g ∈ L, p ∈ deps g → W.getD p false = W.getD r false) →
      (L.map (renG p r)).foldl step (v.eraseIdx p) = W.eraseIdx p := by
  intro L
  induction L with
  | nil =>
    intro v hW _ _
    simp only [List.foldl_nil] at hW
    subst hW
    rfl
  | cons g L ih =>
    intro v hW hp hv
    rw [List.foldl_cons] at hW
    rw [List.map_cons, List.foldl_cons]
    have hvW : ∀ i, i < v.length → v.getD i false = W.getD i false := fun i hi => by
      rw [← hW, foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton]; omega)]
      exact (getD_append_lt _ _ _ hi).symm
    have hWlen : v.length + 1 + L.length = W.length := by
      have := congrArg List.length hW
      rw [foldl_step_length] at this
      simp only [step, List.length_append, List.length_singleton] at this
      omega
    have hstep : step (v.eraseIdx p) (renG p r g) = (step v g).eraseIdx p := by
      simp only [step, renG, List.map_map]
      rw [List.eraseIdx_append_of_lt_length hp]
      congr 2
      apply eval_congr
      intro i hi
      simp only [Function.comp, ren]
      split_ifs with h1 h2
      · exact getD_eraseIdx_lt _ _ _ h1
      · subst h2
        rcases hr with hr | hr
        · rw [getD_eraseIdx_lt _ _ _ hr, hvW _ (by omega), hvW _ hp]
          exact (hv g (by simp) hi).symm
        · rw [getD_of_length_le _ _ (by rw [List.length_eraseIdx_of_lt hp]; omega), hvW _ hp,
            hv g (by simp) hi, getD_of_length_le _ _ hr]
      · rw [getD_eraseIdx_ge _ _ _ (by omega), Nat.sub_add_cancel (by omega)]
    rw [hstep]
    exact ih _ hW (by simp only [step, List.length_append, List.length_singleton]; omega)
      (fun g' hg' => hv g' (List.mem_cons_of_mem _ hg'))

theorem del_foldl (G : List Gate) (x : List Bool) (t r : ℕ) (ht : t < G.length)
    (hr : r < x.length + t ∨ x.length + G.length ≤ r)
    (hv : ∀ g ∈ G.drop (t + 1), x.length + t ∈ deps g →
      (G.foldl step x).getD (x.length + t) false = (G.foldl step x).getD r false) :
    (del G t (x.length + t) r).foldl step x = (G.foldl step x).eraseIdx (x.length + t) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by simp
  have hWlen : (G.foldl step x).length = x.length + G.length := foldl_step_length _ _
  have hW' : (G.drop (t + 1)).foldl step (step ((G.take t).foldl step x) G[t]) = G.foldl step x := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hlen : ((G.take t).foldl step x).length = x.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  have hv0 : (G.take t).foldl step x = (step ((G.take t).foldl step x) G[t]).eraseIdx (x.length + t) := by
    simp only [step]
    rw [List.eraseIdx_append_of_length_le (by omega)]
    simp [hlen]
  unfold del
  rw [List.foldl_append, hv0]
  exact del_foldl_aux _ (x.length + t) r (by rwa [hWlen]) _ _ hW'
    (by simp only [step, List.length_append, List.length_singleton, hlen]; omega) hv

theorem del_eval (G : List Gate) (o : ℕ) (x : List Bool) (t r : ℕ) (ht : t < G.length)
    (hr : r < x.length + t ∨ x.length + G.length ≤ r)
    (hv : ∀ g ∈ G.drop (t + 1), x.length + t ∈ deps g →
      (G.foldl step x).getD (x.length + t) false = (G.foldl step x).getD r false)
    (ho : o = x.length + t → (G.foldl step x).getD (x.length + t) false = (G.foldl step x).getD r false) :
    Circuit.eval ⟨del G t (x.length + t) r, ren (x.length + t) r o⟩ x = Circuit.eval ⟨G, o⟩ x := by
  simp only [Circuit.eval, wires_eq]
  rw [del_foldl G x t r ht hr hv]
  unfold ren
  split_ifs with h1 h2
  · exact getD_eraseIdx_lt _ _ _ h1
  · subst h2
    rcases hr with hr | hr
    · rw [getD_eraseIdx_lt _ _ _ hr]
      exact (ho rfl).symm
    · rw [getD_of_length_le _ _ (by rw [List.length_eraseIdx_of_lt (by rw [foldl_step_length]; omega), foldl_step_length]; omega),
        ho rfl, getD_of_length_le _ _ (by rw [foldl_step_length]; exact hr)]
  · rw [getD_eraseIdx_ge _ _ _ (by omega), Nat.sub_add_cancel (by omega)]

theorem del_length (G : List Gate) (t p r : ℕ) (ht : t < G.length) :
    (del G t p r).length = G.length - 1 := by
  simp only [del, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

theorem fanInTwo_del (G : List Gate) (o : ℕ) (t p r o' : ℕ) (h : FanInTwo ⟨G, o⟩) :
    FanInTwo ⟨del G t p r, o'⟩ := by
  simp only [FanInTwo] at h ⊢
  intro g hg
  simp only [del, List.mem_append, List.mem_map] at hg
  rcases hg with hg | ⟨g', hg', rfl⟩
  · exact h g (List.mem_of_mem_take hg)
  · obtain ⟨h1, h2⟩ := h g' (List.mem_of_mem_drop hg')
    exact ⟨h1, by simpa [renG] using h2⟩


def src : Gate := ⟨GateOp.and, []⟩


def plus (C : Circuit) : Circuit := ⟨src :: C.gates, C.output⟩

theorem ofFn_snoc {n : ℕ} (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp [Fin.snoc_castSucc, Fin.snoc_last]

theorem plus_foldl (C : Circuit) {n : ℕ} (y : Fin n → Bool) :
    (plus C).gates.foldl step (List.ofFn y) = C.gates.foldl step (List.ofFn (Fin.snoc y true)) := by
  simp only [plus, List.foldl_cons, step, src, GateOp.eval, List.map_nil, List.all_nil, ofFn_snoc]

theorem plus_circuitFun (C : Circuit) (n : ℕ) :
    circuitFun n (plus C) = fun y => circuitFun (n + 1) C (Fin.snoc y true) := by
  funext y
  simp only [circuitFun, Circuit.eval, wires_eq, plus_foldl]
  rfl

theorem plus_fanInTwo (C : Circuit) (h : FanInTwo C) : FanInTwo (plus C) := by
  simp only [FanInTwo] at h ⊢
  intro g hg
  simp only [plus, List.mem_cons] at hg
  rcases hg with rfl | hg
  · simp [src]
  · exact h g hg

theorem plus_size (C : Circuit) : (plus C).size = C.size + 1 := by
  simp [plus, Circuit.size]

theorem plus_getD_src (C : Circuit) {n : ℕ} (y : Fin n → Bool) :
    ((plus C).gates.foldl step (List.ofFn y)).getD n false = true := by
  rw [plus_foldl, ofFn_snoc, foldl_step_getD _ _ _ (by simp), List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp)]
  simp

theorem foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl step w).length) :
    (G.foldl step w).getD i false = ((G.take t).foldl step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact foldl_step_getD _ _ _ hi


theorem gate_value (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i =>
        if i < w.length + t then (G.foldl step w).getD i false else false) := by
  rw [foldl_step_getD_gate G w t ht]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : ((G.take t).foldl step w).length = w.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  split_ifs with h
  · exact (foldl_take_getD G w t i (by rw [hlen]; exact h)).symm
  · exact getD_of_length_le _ _ (by rw [hlen]; omega)

theorem del_getElem_lt (G : List Gate) (t p r t' : ℕ) (h : t' < t) (ht : t < G.length) :
    (del G t p r)[t']'(by rw [del_length G t p r ht]; omega) = G[t']'(by omega) := by
  simp only [del]
  rw [List.getElem_append_left (by simp [List.length_take]; omega), List.getElem_take]

theorem del_getElem_ge (G : List Gate) (t p r t' : ℕ) (h : t ≤ t') (ht : t' + 1 < G.length) :
    (del G t p r)[t']'(by rw [del_length G t p r (by omega)]; omega) = renG p r (G[t' + 1]'ht) := by
  simp only [del]
  rw [List.getElem_append_right (by simp [List.length_take]; omega), List.getElem_map, List.getElem_drop]
  congr 2
  simp [List.length_take]
  omega


end L171
end PEqualNP.Outside

namespace PetersenCompanions4225

def edges : List (Nat × Nat) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
def edge (r : Nat) : Bool := edges.any (fun e => r.testBit e.1 && r.testBit e.2)
def sensitive (v r : Nat) : Bool := !r.testBit v && !edge r && edge (r ||| 2^v)
def critical (v : Nat) := (List.range 512).filter (sensitive v)
def selected : List Nat := [4,6,7]

end PetersenCompanions4225

namespace PetersenCompanions4225
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def bitInput (r : Nat) (i : Fin 9) := r.testBit i.val
def wire (C : Circuit) (r i : Nat) := (C.wires (List.ofFn (bitInput r))).getD i false
def Before (C : Circuit) := ∀ j : Fin C.size, ∀ t∈(C.gates.get j).inputs, t<9+j.val

open PEqualNP.Outside.L171 in
theorem raw (C : Circuit) (r i : Nat) (hi : i<9) : wire C r i=r.testBit i := by
  change (C.gates.foldl step (List.ofFn (bitInput r))).getD i false=_
  rw [foldl_step_getD _ _ _ (by simpa using hi)]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi,↓reduceDIte,Option.getD_some,bitInput]
open PEqualNP.Outside.L171 in
theorem beyond (C : Circuit) (r i : Nat) (h : 9+C.size ≤ i) : wire C r i=false := by
  apply getD_of_length_le
  rw [wires_eq,foldl_step_length,List.length_ofFn];exact h
open PEqualNP.Outside.L171 in
theorem gateValue (C : Circuit) (before : Before C) (r : Nat) (j : Fin C.size) :
    wire C r (9+j.val) = (C.gates.get j).op.eval ((C.gates.get j).inputs.map (wire C r)) := by
  have eq := gate_value C.gates (List.ofFn (bitInput r)) j.val j.isLt
  simp only [List.length_ofFn] at eq
  refine eq.trans ?_
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [before j i hi,ite_true,wire,wires_eq]
theorem matching (C : Circuit) (before : Before C) (v : Fin 9) (j : Fin C.size) (a b : Nat)
    (sameRaw : ∀ i<9, i≠v.val → a.testBit i=b.testBit i)
    (sameGate : wire C a (9+j.val)=wire C b (9+j.val))
    (only : ∀ t : Fin C.size, v.val∈(C.gates.get t).inputs → t=j)
    (i : Nat) (ne : i≠v.val) : wire C a i=wire C b i := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases small : i<9
    · rw [raw _ _ _ small,raw _ _ _ small]
      exact sameRaw _ small ne
    by_cases big : 9+C.size ≤ i
    · rw [beyond _ _ _ big,beyond _ _ _ big]
    let q : Fin C.size := ⟨i-9,by omega⟩
    have eq : 9+q.val=i := by dsimp [q]; omega
    rw [←eq]
    by_cases who : q=j
    · simpa only [who] using sameGate
    · rw [gateValue C before a q,gateValue C before b q]
      congr 1
      apply List.map_congr_left
      intro t ht
      exact ih _ (eq ▸ before q t ht) (by rintro rfl; exact who (only q ht))

set_option maxRecDepth 3500 in
theorem companion_off (C : Circuit) (before : Before C) (spec : ∀ r, wire C r C.output=edge r)
    (v : Fin 9) (hv : v.val∈selected) (rd : Fin C.size)
    (only : ∀ t : Fin C.size, v.val∈(C.gates.get t).inputs ↔ t=rd)
    (isOr : (C.gates.get rd).op=.or) (w : Nat) (hw : w∈(C.gates.get rd).inputs)
    (r : Nat) (hr : r∈critical v.val) : wire C r w=false := by
  have vi := (only rd).mpr rfl
  have out : C.output≠v.val := by
    intro e
    have atv := spec (2^v.val)
    rw [e,raw C _ _ v.isLt,Nat.testBit_two_pow_self] at atv
    have single : ∀ i : Fin 9, edge (2^i.val)=false := by decide +kernel
    rw [single] at atv
    contradiction
  have rr := (List.mem_filter.mp hr).2
  change (!r.testBit v.val && !edge r && edge (r ||| 2^v.val))=true at rr
  simp only [Bool.and_eq_true_iff,Bool.not_eq_true'] at rr
  cases low : wire C r w with
  | false => rfl
  | true =>
    let high := r ||| 2^v.val
    have one : wire C high v.val=true := by simp [raw C _ _ v.isLt,high,Nat.testBit_or,Nat.testBit_two_pow_self]
    have pass (q k : Nat) (hk : k∈(C.gates.get rd).inputs) (hit : wire C q k=true) :
        wire C q (9+rd.val)=true := by
      rw [gateValue C before q rd,isOr]
      exact List.any_eq_true.mpr ⟨true,List.mem_map.mpr ⟨k,hk,hit⟩,rfl⟩
    have output := matching C before v rd r high (by
      intro i hi ne
      simp [high,Nat.testBit_or,Ne.symm ne]) ((pass r w hw low).trans (pass high v.val vi one).symm)
      (fun t h => (only t).mp h) C.output out
    rw [spec,spec,rr.1.2,rr.2] at output
    exact output.symm

end PetersenCompanions4225

namespace PetersenCompanions4225
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem prefixMatching (C : Circuit) (before : Before C) (v : Fin 9) (rd : Fin C.size) (a b : Nat)
    (sameRaw : ∀ i<9, i≠v.val → a.testBit i=b.testBit i)
    (only : ∀ t : Fin C.size, v.val∈(C.gates.get t).inputs → t=rd)
    (i : Nat) (hi : i<9+rd.val) (ne : i≠v.val) : wire C a i=wire C b i := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases small : i<9
    · rw [raw _ _ _ small,raw _ _ _ small]; exact sameRaw _ small ne
    let t : Fin C.size := ⟨i-9,by have := rd.isLt; omega⟩
    have eq : 9+t.val=i := by dsimp [t]; omega
    have lt : t.val<rd.val := by omega
    rw [←eq,gateValue C before a t,gateValue C before b t]
    congr 1
    apply List.map_congr_left
    intro k hk
    have ki := eq ▸ before t k hk
    exact ih k ki (by omega) (by
      rintro rfl
      have e := only t hk
      exact (Nat.ne_of_lt lt) (congrArg Fin.val e))

theorem independent_companion (C : Circuit) (before : Before C) (v : Fin 9) (rd : Fin C.size)
    (only : ∀ t : Fin C.size, v.val∈(C.gates.get t).inputs ↔ t=rd)
    {w} (ne : w≠v.val) (hw : w∈(C.gates.get rd).inputs) (r : Nat) :
    wire C r w=wire C (r ||| 2^v.val) w :=
  prefixMatching C before v rd _ _ (by intro i hi hv; simp [Nat.testBit_or,Ne.symm hv])
    (fun t h => (only t).mp h) _ (before _ _ hw) ne

def forbidden (v : Nat) := critical v ++ (critical v).map (fun r => r ||| 2^v)

set_option maxRecDepth 3500 in
theorem forbidden_counts : selected.map (fun v => ((forbidden v).toFinset).card) = [44,44,44] := by decide +kernel

theorem forbidden_off (C : Circuit) (before : Before C) (spec : ∀ r, wire C r C.output=edge r)
    (v : Fin 9) (hv : v.val∈selected) (rd : Fin C.size)
    (only : ∀ t : Fin C.size, v.val∈(C.gates.get t).inputs ↔ t=rd)
    (isOr : (C.gates.get rd).op=.or) (w : Nat) (ne : w≠v.val) (hw : w∈(C.gates.get rd).inputs)
    (r : Nat) (hr : r∈forbidden v.val) : wire C r w=false := by
  rcases List.mem_append.mp hr with h|h
  · exact companion_off C before spec v hv rd only isOr w hw _ h
  · obtain ⟨m,hm,rfl⟩ := List.mem_map.mp h
    rw [←independent_companion C before v rd only ne hw]
    exact companion_off C before spec v hv rd only isOr w hw _ hm

end PetersenCompanions4225
namespace PetersenCompanions4225
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def allForbidden : Nat → List Nat
  | 4 => [1, 5, 8, 9, 10, 40, 42, 65, 69, 72, 73, 104, 129, 136, 137, 138, 193, 200, 201, 257, 261, 385, 17, 21, 24, 25, 26, 56, 58, 81, 85, 88, 89, 120, 145, 152, 153, 154, 209, 216, 217, 273, 277, 401]
  | 6 => [2, 10, 18, 34, 42, 50, 130, 138, 146, 256, 257, 258, 260, 261, 272, 274, 276, 384, 385, 386, 400, 402, 66, 74, 82, 98, 106, 114, 194, 202, 210, 320, 321, 322, 324, 325, 336, 338, 340, 448, 449, 450, 464, 466]
  | 7 => [4, 5, 20, 32, 34, 36, 40, 42, 48, 50, 52, 68, 69, 84, 96, 100, 104, 112, 116, 260, 261, 276, 132, 133, 148, 160, 162, 164, 168, 170, 176, 178, 180, 196, 197, 212, 224, 228, 232, 240, 244, 388, 389, 404]
  | _ => []

set_option maxRecDepth 4000 in
theorem allForbidden_eq : ∀ v ∈ selected, allForbidden v=forbidden v := by decide +kernel

end PetersenCompanions4225

namespace PetersenCompanions4225
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


def CommonReader (C : Circuit) (w : Nat) (v : Fin 9) : Prop :=
  ∃ j : Fin C.size, (∀ t : Fin C.size, v.val ∈ (C.gates.get t).inputs ↔ t=j) ∧
    (C.gates.get j).op=.or ∧ w≠v.val ∧ w∈(C.gates.get j).inputs

def coreRow (r : Nat) := r &&& 303
def put (v : Nat) (r : Nat) (b : Bool) := if b then r ||| 2^v else r

theorem common_put {C w} (before : Before C) {v : Fin 9} (h : CommonReader C w v)
    (r : Nat) (b : Bool) : wire C (put v.val r b) w = wire C r w := by
  obtain ⟨j,only,_,ne,hw⟩ := h
  cases b with
  | false => rfl
  | true => exact (independent_companion C before v j only ne hw r).symm

set_option maxRecDepth 4000 in
theorem rebuild_core : ∀ r : Fin 512,
    put 7 (put 6 (put 4 (coreRow r) (r.val.testBit 4)) (r.val.testBit 6)) (r.val.testBit 7) = r.val := by
  decide +kernel

abbrev ThreeReaders (C : Circuit) (w : Nat) :=
  CommonReader C w 4 ∧ CommonReader C w 6 ∧ CommonReader C w 7

theorem common_core {C w} (before : Before C) (h : ThreeReaders C w) (r : Fin 512) :
    wire C r w = wire C (coreRow r) w := by
  calc wire C r w = wire C (put 7 (put 6 (put 4 (coreRow r) (r.val.testBit 4)) (r.val.testBit 6)) (r.val.testBit 7)) w := congrArg (fun n => wire C n w) (rebuild_core r).symm
       _ = _ := (common_put before h.2.2 _ _).trans ((common_put before h.2.1 _ _).trans (common_put before h.1 _ _))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 900000 in
theorem independent_rows : ∀ r : Fin 512, coreRow r.val ≠ 0 → edge (coreRow r.val)=false →
    coreRow r.val ∈ allForbidden 4 ∨ coreRow r.val ∈ allForbidden 6 ∨ coreRow r.val ∈ allForbidden 7 := by decide +kernel

theorem common_zero {C w} (before : Before C) (spec : ∀ r, wire C r C.output=edge r)
    (h : ThreeReaders C w) (r : Fin 512) (nz : coreRow r ≠ 0) (ind : edge (coreRow r)=false) :
    wire C r w=false := by
  rw [common_core before h]
  have off {v : Fin 9} (hv : v.val∈selected) (reader : CommonReader C w v)
      (bad : coreRow r ∈ allForbidden v.val) : wire C (coreRow r) w=false := by
    obtain ⟨j,only,isOr,ne,hw⟩ := reader
    exact forbidden_off C before spec v hv j only isOr w ne hw _ ((allForbidden_eq v hv) ▸ bad)
  rcases independent_rows r nz ind with a|b|c
  · exact off (by decide) h.1 a
  · exact off (by decide) h.2.1 b
  · exact off (by decide) h.2.2 c

set_option maxRecDepth 4000 in
theorem core_edge_target : ∀ r : Fin 512, edge (coreRow r.val)=true → edge r.val=true := by decide +kernel

theorem common_implies_output {C w} (before : Before C) (spec : ∀ r, wire C r C.output=edge r)
    (h : ThreeReaders C w) (empty : wire C 0 w=false) (r : Fin 512) (high : wire C r w=true) :
    wire C r C.output=true := by
  by_cases e : coreRow r = 0
  · rw [common_core before h,e,empty] at high; contradiction
  cases ce : edge (coreRow r) with
  | true => exact (spec _).trans (core_edge_target r ce)
  | false => rw [common_zero before spec h r e ce] at high; contradiction

end PetersenCompanions4225

namespace PetersenGuard
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L171

def val (C : Circuit) (x : List Bool) (i : Nat) := (C.gates.foldl step x).getD i false

def dropGate (n : Nat) (C : Circuit) (t r : Nat) : Circuit :=
  ⟨del C.gates t (n+t) r, ren (n+t) r C.output⟩

theorem early (C : Circuit) {n t r i} (ht : t<C.size) (hi : i<n+t)
    (x : List Bool) (hx : x.length=n) : val (dropGate n C t r) x i=val C x i := by
  change t<C.gates.length at ht
  have len : ((C.gates.take t).foldl step x).length=n+t := by
    rw [foldl_step_length,hx,List.length_take,Nat.min_eq_left ht.le]
  unfold val dropGate del
  rw [List.foldl_append,foldl_step_getD _ _ _ (len ▸ hi)]
  exact (foldl_take_getD C.gates x t i (len ▸ hi)).symm

def dropList (n : Nat) (C : Circuit) : List (Nat × Nat) → Circuit
  | [] => C
  | (t,r)::ds => dropList n (dropGate n C t r) ds

theorem guarded_drop {n guard : Nat} (ds : List (Nat × Nat)) (C : Circuit)
    (fan : FanInTwo C) (order : ds.Pairwise (fun a b => b.1<a.1))
    (valid : ∀ d ∈ ds, d.1<C.size ∧ d.2<n ∧ guard<n+d.1)
    (agree : ∀ d ∈ ds, ∀ x : List Bool, x.length=n → val C x guard=false →
      val C x (n+d.1)=val C x d.2) :
    let D := dropList n C ds
    FanInTwo D ∧ D.size+ds.length=C.size ∧
      ∀ x : List Bool, x.length=n → val D x guard=val C x guard ∧
      (val C x guard=false → D.eval x=C.eval x) := by
  induction ds generalizing C with
  | nil => exact ⟨fan,by simp [dropList],fun _ _ => ⟨rfl, fun _ => rfl⟩⟩
  | cons d ds ih =>
    obtain ⟨t,r⟩ := d
    obtain ⟨later,ord⟩ := List.pairwise_cons.mp order
    obtain ⟨ht,hr,hguard⟩ := valid (t,r) (by simp)
    let B := dropGate n C t r
    have len : B.size=C.size-1 := del_length _ _ _ _ ht
    have hf : FanInTwo B := fanInTwo_del _ _ _ _ _ _ fan
    have earlier (i) (h : i<n+t) (x : List Bool) (hx : x.length=n) :
        val B x i=val C x i := early C ht h x hx
    have stepOK (x : List Bool) (hx : x.length=n) (low : val C x guard=false) :
        B.eval x=C.eval x := by
      have same := agree (t,r) (by simp) x hx low
      change (C.gates.foldl step x).getD (n+t) false=(C.gates.foldl step x).getD r false at same
      have H := del_eval C.gates C.output x t r ht (Or.inl (by omega))
        (fun _ _ _ => by simpa only [hx] using same) (fun _ => by simpa only [hx] using same)
      change (Circuit.mk (del C.gates t (n+t) r) (ren (n+t) r C.output)).eval x=C.eval x
      simpa only [hx] using H
    obtain ⟨outFan,outLen,outVal⟩ := ih B hf ord (by
      intro d hd
      obtain ⟨u,v,g⟩ := valid d (List.mem_cons_of_mem _ hd)
      have l := later d hd
      exact ⟨by rw [len]; dsimp only at *; omega,v,g⟩) (by
      intro d hd x hx low
      obtain ⟨_,v,_⟩ := valid d (List.mem_cons_of_mem _ hd)
      have l := later d hd
      dsimp only at l
      rw [earlier _ (by omega) x hx,earlier _ (by omega) x hx]
      exact agree d (List.mem_cons_of_mem _ hd) x hx ((earlier _ hguard x hx).symm.trans low))
    refine ⟨outFan,?_,?_⟩
    · change (dropList n B ds).size+(ds.length+1)=C.size
      omega
    · intro x hx
      obtain ⟨g,o⟩ := outVal x hx
      exact ⟨g.trans (earlier _ hguard x hx), fun low =>
        (o ((earlier _ hguard x hx).trans low)).trans (stepOK x hx low)⟩

end PetersenGuard
namespace PetersenGuard
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L171

def addGate (n : Nat) (C : Circuit) (g : Gate) : Circuit :=
  ⟨C.gates++[g],n+C.size⟩

theorem add_size (n C g) : (addGate n C g).size=C.size+1 := by simp [addGate,Circuit.size]

theorem add_fan {n C g} (h : FanInTwo C) (ok : g.op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    FanInTwo (addGate n C g) := by
  intro a ha
  rcases List.mem_append.mp ha with ha|ha
  · exact h _ ha
  · simpa using (List.mem_singleton.mp ha ▸ ok : a.op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ a.inputs.length≤2)

theorem add_value (n C g) (x : List Bool) (hx : x.length=n) :
    (addGate n C g).eval x=g.op.eval (g.inputs.map (val C x)) := by
  have hn := foldl_step_length C.gates x
  rw [hx] at hn
  change ((C.gates++[g]).foldl step x).getD (n+C.size) false=_
  rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
  simp only [step,Circuit.size,←hn,List.getD_eq_getElem?_getD,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]
  rfl

theorem add_early (n C g) (x : List Bool) (hx : x.length=n) (i) (hi : i<n+C.size) :
    val (addGate n C g) x i=val C x i := by
  unfold val addGate
  rw [List.foldl_append,foldl_step_getD]
  rw [foldl_step_length,hx]; exact hi

def clip (n : Nat) (C : Circuit) := if C.output<n+C.size then C.output else n+C.size+2

theorem clipped (n C g) (x : List Bool) (hx : x.length=n) :
    val (addGate n C g) x (clip n C)=C.eval x := by
  unfold clip
  split_ifs with h
  · exact add_early _ _ _ _ hx _ h
  · change ((addGate n C g).gates.foldl step x).getD _ false=(C.gates.foldl step x).getD _ false
    rw [getD_of_length_le,getD_of_length_le]
    · rw [foldl_step_length,hx]; exact Nat.le_of_not_gt h
    · rw [foldl_step_length,hx]
      have a := add_size n C g
      change n+(addGate n C g).size≤n+C.size+2
      omega

def fixPos (n : Nat) (C : Circuit) (w : Nat) := addGate n C ⟨.or,[C.output,w]⟩
def fixNeg (n : Nat) (C : Circuit) (w : Nat) :=
  addGate n (addGate n C ⟨.not,[w]⟩) ⟨.and,[clip n C,n+C.size]⟩

theorem fix_pos (n C w) (x : List Bool) (hx : x.length=n) :
    (fixPos n C w).eval x=(C.eval x || val C x w) := by
  rw [fixPos,add_value _ _ _ _ hx]
  simp [GateOp.eval,val,Circuit.eval,wires_eq]

theorem fix_neg (n C w) (x : List Bool) (hx : x.length=n) :
    (fixNeg n C w).eval x=(C.eval x && !val C x w) := by
  rw [fixNeg,add_value _ _ _ _ hx]
  have inv : val (addGate n C ⟨.not,[w]⟩) x (n+C.size)= !val C x w := by
    change (addGate n C ⟨.not,[w]⟩).eval x=_
    rw [add_value _ _ _ _ hx]; rfl
  simp [GateOp.eval,clipped _ _ _ _ hx,inv]

theorem min_guard {n w} (C : Circuit) (minimal : IsMinimalCircuit n C) (ds : List (Nat × Nat))
    (order : ds.Pairwise (fun a b => b.1<a.1))
    (valid : ∀ d ∈ ds, d.1<C.size ∧ d.2<n ∧ w<n+d.1)
    (agree : ∀ d ∈ ds, ∀ x : List Bool, x.length=n → val C x w=false →
      val C x (n+d.1)=val C x d.2)
    (sign : Bool) (count : (if sign then 1 else 2)<ds.length)
    (constant : ∀ x : Fin n → Bool, val C (List.ofFn x) w=true → circuitFun n C x=sign) : False := by
  let D := dropList n C ds
  obtain ⟨hfan,hlen,hvals⟩ := guarded_drop ds C minimal.1 order valid agree
  cases sign with
  | true =>
    have f : FanInTwo (fixPos n D w) := add_fan hfan (by simp)
    have same : circuitFun n (fixPos n D w)=circuitFun n C := by
      funext x
      obtain ⟨g,o⟩ := hvals (List.ofFn x) (by simp)
      change (fixPos n D w).eval _=_
      rw [fix_pos _ _ _ _ (by simp)]
      cases e : val C (List.ofFn x) w with
      | false => rw [g,e,Bool.or_false];exact o e
      | true => rw [g,e,Bool.or_true];exact (constant x e).symm
    have le := minimal.2 _ f same
    have l : (fixPos n D w).size=D.size+1 := add_size _ _ _
    change D.size+ds.length=C.size at hlen
    simp at count
    omega
  | false =>
    have f : FanInTwo (fixNeg n D w) := add_fan (add_fan hfan (by simp)) (by simp)
    have same : circuitFun n (fixNeg n D w)=circuitFun n C := by
      funext x
      obtain ⟨g,o⟩ := hvals (List.ofFn x) (by simp)
      change (fixNeg n D w).eval _=_
      rw [fix_neg _ _ _ _ (by simp)]
      cases e : val C (List.ofFn x) w with
      | false => rw [g,e];simp only [Bool.not_false,Bool.and_true];exact o e
      | true => rw [g,e];simp only [Bool.not_true,Bool.and_false];exact (constant x e).symm
    have le := minimal.2 _ f same
    have l : (fixNeg n D w).size=D.size+2 := by simp [fixNeg,add_size]
    change D.size+ds.length=C.size at hlen
    simp at count
    omega

end PetersenGuard
namespace PetersenCompanions4225
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem rowLists (x : List Bool) (hx : x.length=9) :
    ∃ r : Fin 512, List.ofFn (bitInput r.val)=x := by
  let b := BitVec.ofBoolListLE x
  have bound : b.toNat < 512 := by simpa only [hx] using b.isLt
  refine ⟨⟨b.toNat,bound⟩, List.ext_getElem (by simp [hx]) ?_⟩
  intro i h k
  simp only [List.getElem_ofFn,bitInput]
  have e : b.getLsbD i=x.getD i false := BitVec.getLsbD_ofBoolListLE
  change b.toNat.testBit i=x.getD i false at e
  simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem k,Option.getD_some] using e

theorem pair_layout (l : List Nat) (a b : Nat) (ne : a≠b) (la : a∈l) (lb : b∈l)
    (len : l.length≤2) : l=[a,b] ∨ l=[b,a] := by
  cases l with
  | nil => simp at la
  | cons i l =>
    cases l with
    | nil => simp_all
    | cons j tail =>
      have h : tail=[] := List.length_eq_zero_iff.mp (by change tail.length+1+1≤2 at len; omega)
      subst tail
      simp only [List.mem_cons,List.not_mem_nil,or_false] at la lb
      rcases la with rfl|rfl <;> rcases lb with h|h <;> simp_all

theorem descending_three (a b c : Nat × Nat) (ab : a.1≠b.1) (ac : a.1≠c.1) (bc : b.1≠c.1) :
    ∃ ds : List (Nat × Nat), ds.Pairwise (fun x y => y.1<x.1) ∧ ds.length=3 ∧
    ∀ d, d∈ds ↔ d=a ∨ d=b ∨ d=c := by
  have go (x y z : Nat × Nat) (xy : y.1<x.1) (yz : z.1<y.1)
      (perm : ∀ d, (d=x ∨ d=y ∨ d=z) ↔ (d=a ∨ d=b ∨ d=c)) :
      ∃ ds : List (Nat × Nat), ds.Pairwise (fun x y => y.1<x.1) ∧ ds.length=3 ∧
      ∀ d, d∈ds ↔ d=a ∨ d=b ∨ d=c :=
    ⟨[x,y,z],by simp [xy,yz,lt_trans yz xy],rfl,fun d => by simpa using perm d⟩
  by_cases h : a.1<b.1 <;> by_cases i : a.1<c.1 <;> by_cases j : b.1<c.1 <;> first
    | omega
    | exact go a b c (by omega) (by omega) (by tauto)
    | exact go a c b (by omega) (by omega) (by tauto)
    | exact go b a c (by omega) (by omega) (by tauto)
    | exact go b c a (by omega) (by omega) (by tauto)
    | exact go c a b (by omega) (by omega) (by tauto)
    | exact go c b a (by omega) (by omega) (by tauto)

def GuardEntry (C : Circuit) (w : Nat) (d : Nat × Nat) : Prop :=
  d.1<C.size ∧ d.2<9 ∧ w<9+d.1 ∧
    ∀ r : Fin 512, wire C r w=false → wire C r (9+d.1)=wire C r d.2

theorem reader_entry {C v w} (before : Before C) (fan : FanInTwo C) (hr : CommonReader C w v) :
    ∃ j : Fin C.size, GuardEntry C w (j.val,v.val) ∧
      ((C.gates.get j).inputs=[v.val,w] ∨ (C.gates.get j).inputs=[w,v.val]) := by
  obtain ⟨j,only,isOr,ne,hw⟩ := hr
  have two := pair_layout _ _ _ ne.symm ((only j).mpr rfl) hw (fan _ (List.get_mem _ _)).2
  refine ⟨j,⟨j.isLt,v.isLt,before j w hw,?_⟩,two⟩
  intro r low
  change wire C r (9+j.val)=wire C r v.val
  rw [gateValue C before r j,isOr]
  rcases two with eq|eq <;> simp [eq,GateOp.eval,low]

theorem different_entries (a b w : Nat) (ne : a≠b) (l : List Nat)
    (x : l=[a,w] ∨ l=[w,a]) (y : l=[b,w] ∨ l=[w,b]) : False := by
  rcases x with h|h <;> rcases y with k|k <;> simp_all

theorem reader_list {C w} (before : Before C) (fan : FanInTwo C) (h : ThreeReaders C w) :
    ∃ ds : List (Nat × Nat), ds.Pairwise (fun a b => b.1<a.1) ∧ ds.length=3 ∧
      ∀ d∈ds, GuardEntry C w d := by
  obtain ⟨ja,ea,la⟩ := reader_entry before fan h.1
  obtain ⟨jb,eb,lb⟩ := reader_entry before fan h.2.1
  obtain ⟨jc,ec,lc⟩ := reader_entry before fan h.2.2
  have ab : ja.val≠jb.val := by intro e; obtain rfl := Fin.ext e; exact different_entries _ _ _ (by decide) _ la lb
  have ac : ja.val≠jc.val := by intro e; obtain rfl := Fin.ext e; exact different_entries _ _ _ (by decide) _ la lc
  have bc : jb.val≠jc.val := by intro e; obtain rfl := Fin.ext e; exact different_entries _ _ _ (by decide) _ lb lc
  obtain ⟨ds,ord,n,mem⟩ := descending_three (ja.val,4) (jb.val,6) (jc.val,7) ab ac bc
  refine ⟨ds,ord,n,?_⟩
  intro d hd
  rcases (mem d).mp hd with rfl|rfl|rfl
  · exact ea
  · exact eb
  · exact ec

end PetersenCompanions4225
namespace PetersenCompanions4225
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem both_outputs {C w} (before : Before C) (minC : IsMinimalCircuit 9 C) (h : ThreeReaders C w)
    (sg : Bool) : ∃ r : Fin 512, wire C r w=true ∧ wire C r C.output=sg := by
  by_contra! none
  obtain ⟨ds,order,count,ok⟩ := reader_list before minC.1 h
  apply PetersenGuard.min_guard C minC ds order (w:=w) (fun d hd =>
    ⟨(ok d hd).1,(ok d hd).2.1,(ok d hd).2.2.1⟩) ?_ (!sg) (by cases sg <;> simp [count]) ?_
  · intro d hd x hx low
    obtain ⟨r,rfl⟩ := rowLists x hx
    exact (ok d hd).2.2.2 r low
  · intro x high
    obtain ⟨r,e⟩ := rowLists (List.ofFn x) (by simp)
    have yes : wire C r w=true := by
      change PetersenGuard.val C (List.ofFn (bitInput r.val)) w=true
      rw [e]; exact high
    have no := none r yes
    change C.eval (List.ofFn x)=_
    rw [←e]
    change wire C r C.output=_
    cases sg <;> cases k : wire C r C.output <;> simp_all

set_option maxRecDepth 4000 in
theorem empty_core_false : ∀ r : Fin 512, coreRow r.val=0 → edge r.val=false := by decide +kernel

theorem common_signature {C w} (before : Before C) (minC : IsMinimalCircuit 9 C)
    (spec : ∀ r, wire C r C.output=edge r) (h : ThreeReaders C w) :
    wire C 0 w=true ∧
    (∀ i ∈ ([0,1,2,3,5,8] : List Nat), wire C (2^i) w=false) ∧
    ∃ r : Fin 512, coreRow r.val=r.val ∧ edge r.val=true ∧ wire C r w=true := by
  obtain ⟨a,ha,na⟩ := both_outputs before minC h false
  obtain ⟨b,hb,pb⟩ := both_outputs before minC h true
  have empty : wire C 0 w=true := by
    cases e : wire C 0 w with
    | true => rfl
    | false => have c := common_implies_output before spec h e a ha; simp_all
  refine ⟨empty,?_,?_⟩
  · intro i hi
    have single (i : Nat) (small : 2^i<512) (nz : coreRow (2^i)≠0) (off : edge (coreRow (2^i))=false) :
        wire C (2^i) w=false := common_zero before spec h ⟨2^i,small⟩ nz off
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> apply single <;> decide
  · have nz : coreRow b.val≠0 := by
      intro z
      have := (spec b).trans (empty_core_false b z)
      simp_all
    have pos : edge (coreRow b.val)=true := by
      cases e : edge (coreRow b.val) with
      | true => rfl
      | false => have := common_zero before spec h b nz e; simp_all
    have lim : ∀ r : Fin 512, coreRow r.val<512 ∧ coreRow (coreRow r.val)=coreRow r.val := by decide +kernel
    exact ⟨⟨coreRow b,(lim b).1⟩,(lim b).2,pos,(common_core before h b).symm.trans hb⟩

end PetersenCompanions4225

namespace PetersenSelector
def mask : Nat := 4095
def base : List Nat := [0,15,240,255,3840,3855,4080,4095,546,1092,2184]
def target : Nat := 2114

def next (vs : List Nat) (y : Nat) := ∃ a ∈ vs, ∃ b ∈ vs,
  y=(a &&& b) ∨ y=(a ||| b) ∨ y=(mask ^^^ a)

def gen (vs : List Nat) := (vs.map (fun a => mask ^^^ a)) ++
  vs.flatMap (fun a => vs.flatMap fun b => [a &&& b,a ||| b])

theorem mem_gen {vs y} (h : next vs y) : y ∈ gen vs := by
  obtain ⟨a,ha,b,hb,e|e|e⟩ := h
  · simp only [gen,List.mem_append,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false]
    exact Or.inr ⟨a,ha,b,hb,Or.inl e⟩
  · simp only [gen,List.mem_append,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false]
    exact Or.inr ⟨a,ha,b,hb,Or.inr e⟩
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨a,ha,e.symm⟩)

def last (vs : List Nat) (c : Nat) : Bool :=
  c==target || (mask ^^^ c)==target || vs.any fun d => (c &&& d)==target || (c ||| d)==target

theorem last_hit {vs c} (h : next (c::vs) target) :
    last vs c=true ∨ target ∈ gen vs := by
  obtain ⟨a,ha,b,hb,ops⟩ := h
  rcases List.mem_cons.mp ha with rfl|a'
  · rcases List.mem_cons.mp hb with rfl|b'
    · left;rcases ops with e|e|e <;> simp_all [last,Nat.and_self,Nat.or_self]
    · left
      rcases ops with e|e|e
      · exact Bool.or_eq_true_iff.mpr (Or.inr (List.any_eq_true.mpr ⟨b,b',by simp [e]⟩))
      · exact Bool.or_eq_true_iff.mpr (Or.inr (List.any_eq_true.mpr ⟨b,b',by simp [e]⟩))
      · simp [last,e]
  · rcases List.mem_cons.mp hb with rfl|b'
    · rcases ops with e|e|e
      · left; exact Bool.or_eq_true_iff.mpr (Or.inr (List.any_eq_true.mpr ⟨a,a',by simp [←e,Nat.and_comm]⟩))
      · left; exact Bool.or_eq_true_iff.mpr (Or.inr (List.any_eq_true.mpr ⟨a,a',by simp [←e,Nat.or_comm]⟩))
      · right; exact mem_gen ⟨a,a',a,a',Or.inr (Or.inr e)⟩
    · right; exact mem_gen ⟨a,a',b,b',ops⟩

def audit (vs : List Nat) : Bool := !((gen vs).any (last vs))

theorem no_last_two {vs} (h : audit vs=true) {c} (step : next vs c) :
    ¬next (c::vs) target := by
  intro finalStep
  have ok (y) (hy : y∈gen vs) : last vs y=false := by
    by_contra! bad
    have yes : (gen vs).any (last vs)=true := List.any_eq_true.mpr ⟨y,hy,by simpa using bad⟩
    simp [audit,yes] at h
  rcases last_hit finalStep with fail|direct
  · simp [ok c (mem_gen step)] at fail
  · have invalid := ok target direct
    simp [last] at invalid

end PetersenSelector
namespace PetersenSelector
def first : List Nat := [0, 2, 4, 8, 15, 32, 34, 64, 68, 128, 136, 240, 255, 512, 514, 544, 546, 559, 754, 767, 1024, 1028, 1088, 1092, 1103, 1268, 1279, 1638, 1911, 2048, 2056, 2176, 2184, 2191, 2296, 2303, 2730, 3003, 3276, 3549, 3840, 3855, 3874, 3887, 3908, 3919, 3976, 3983, 4080, 4082, 4084, 4088, 4095]
theorem first_ok : ∀ a ∈ gen base, a ∈ first := by decide +kernel
def tested (a : Nat) := ((gen (a::base)).eraseDups).all fun b => audit (b::a::base)
end PetersenSelector
namespace PetersenSelector
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_0 : tested 0=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_15 : tested 15=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_68 : tested 68=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_255 : tested 255=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_546 : tested 546=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_1024 : tested 1024=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_1103 : tested 1103=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_1911 : tested 1911=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_2184 : tested 2184=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_2730 : tested 2730=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_3840 : tested 3840=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_3908 : tested 3908=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_4080 : tested 4080=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_4095 : tested 4095=true := by decide +kernel
end PetersenSelector
namespace PetersenSelector
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_2 : tested 2=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_32 : tested 32=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_128 : tested 128=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_512 : tested 512=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_559 : tested 559=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_1028 : tested 1028=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_1268 : tested 1268=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_2048 : tested 2048=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_2191 : tested 2191=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_3003 : tested 3003=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_3855 : tested 3855=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_3919 : tested 3919=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_4082 : tested 4082=true := by decide +kernel
end PetersenSelector
namespace PetersenSelector
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_4 : tested 4=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_34 : tested 34=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_136 : tested 136=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_514 : tested 514=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_754 : tested 754=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_1088 : tested 1088=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_1279 : tested 1279=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_2056 : tested 2056=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_2296 : tested 2296=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_3276 : tested 3276=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_3874 : tested 3874=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_3976 : tested 3976=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_4084 : tested 4084=true := by decide +kernel
end PetersenSelector
namespace PetersenSelector
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_8 : tested 8=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_64 : tested 64=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_240 : tested 240=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_544 : tested 544=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_767 : tested 767=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_1092 : tested 1092=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_1638 : tested 1638=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_2176 : tested 2176=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_2303 : tested 2303=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_3549 : tested 3549=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_3887 : tested 3887=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_3983 : tested 3983=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem tested_4088 : tested 4088=true := by decide +kernel
end PetersenSelector
namespace PetersenSelector
theorem mux_impossible {a b c} (g1 : next base a) (g2 : next (a::base) b) (g3 : next (b::a::base) c) : ¬next (c::b::a::base) target := by
  have h := first_ok a (mem_gen g1)
  have good : tested a=true := by
    simp only [first,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact tested_0
    · exact tested_2
    · exact tested_4
    · exact tested_8
    · exact tested_15
    · exact tested_32
    · exact tested_34
    · exact tested_64
    · exact tested_68
    · exact tested_128
    · exact tested_136
    · exact tested_240
    · exact tested_255
    · exact tested_512
    · exact tested_514
    · exact tested_544
    · exact tested_546
    · exact tested_559
    · exact tested_754
    · exact tested_767
    · exact tested_1024
    · exact tested_1028
    · exact tested_1088
    · exact tested_1092
    · exact tested_1103
    · exact tested_1268
    · exact tested_1279
    · exact tested_1638
    · exact tested_1911
    · exact tested_2048
    · exact tested_2056
    · exact tested_2176
    · exact tested_2184
    · exact tested_2191
    · exact tested_2296
    · exact tested_2303
    · exact tested_2730
    · exact tested_3003
    · exact tested_3276
    · exact tested_3549
    · exact tested_3840
    · exact tested_3855
    · exact tested_3874
    · exact tested_3887
    · exact tested_3908
    · exact tested_3919
    · exact tested_3976
    · exact tested_3983
    · exact tested_4080
    · exact tested_4082
    · exact tested_4084
    · exact tested_4088
    · exact tested_4095
  apply fun h => no_last_two h g3
  exact List.all_eq_true.mp good b (List.mem_eraseDups.mpr (mem_gen g2))
end PetersenSelector
namespace PetersenSelector

def reaches : Nat → List Nat → Nat → Prop
  | 0,vs,t => t∈vs
  | k+1,vs,t => ∃ y, next vs y ∧ reaches k (y::vs) t

theorem repeated {vs y} (h : y∈vs) : next vs y :=
  ⟨y,h,y,h,Or.inl (Nat.and_self _).symm⟩

theorem pad {k vs t} (r : reaches k vs t) : reaches (k+1) vs t := by
  induction k generalizing vs with
  | zero => exact ⟨t,repeated r,List.mem_cons_self⟩
  | succ k ih =>
    obtain ⟨y,step,r⟩ := r
    exact ⟨y,step,ih r⟩

theorem pad_to {k m vs t} (r : reaches k vs t) (sm : k ≤ m) : reaches m vs t := by
  induction sm with
  | refl => exact r
  | step _ ih => exact pad ih

theorem no_selector {k} (bound : k≤4) : ¬reaches k base target := by
  intro r
  obtain ⟨a,ha,b,hb,c,hc,d,hd,final⟩ := pad_to r bound
  have m : target ∈ d::c::b::a::base := final
  rcases List.mem_cons.mp m with e|prev
  · exact mux_impossible ha hb hc (e ▸ hd)
  · exact mux_impossible ha hb hc (repeated prev)

end PetersenSelector

namespace PetersenSuffix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PetersenCompanions4225 PetersenSelector

def rows : List Nat := [1,17,65,129,2,18,66,130,4,20,68,132]
def pack (rs : List Nat) (f : Nat → Bool) := rs.foldr (fun r n => Nat.bit (f r) n) 0
def col (C : Circuit) (i : Nat) := pack rows (fun r => wire C r i)

theorem pack_congr (rs : List Nat) (f g : Nat → Bool) (same : ∀ r∈rs, f r=g r) :
    pack rs f=pack rs g := by
  induction rs with
  | nil => simp [pack]
  | cons a rs ih =>
    change Nat.bit (f a) (pack rs f)=Nat.bit (g a) (pack rs g)
    rw [same a List.mem_cons_self,ih (fun r h => same r (List.mem_cons_of_mem _ h))]

theorem pack_and (rs : List Nat) (f g : Nat → Bool) :
    pack rs (fun r => f r && g r)=pack rs f &&& pack rs g := by
  induction rs with
  | nil => simp [pack]
  | cons a rs ih => simp [pack,List.foldr_cons,Nat.land_bit] at ih ⊢; rw [ih]

theorem pack_or (rs : List Nat) (f g : Nat → Bool) :
    pack rs (fun r => f r || g r)=pack rs f ||| pack rs g := by
  induction rs with
  | nil => simp [pack]
  | cons a rs ih => simp [pack,List.foldr_cons,Nat.lor_bit] at ih ⊢; rw [ih]

theorem pack_not (rs : List Nat) (f : Nat → Bool) :
    pack rs (fun r => !f r)=pack rs (fun _ => true) ^^^ pack rs f := by
  induction rs with
  | nil => simp [pack]
  | cons a rs ih =>
    simp only [pack,List.foldr_cons,Nat.xor_bit] at ih ⊢
    rw [ih]; cases f a  <;>  rfl

theorem raw_col (C : Circuit) (i : Fin 9) : col C i ∈ base := by
  have e : col C i=pack rows (fun r => r.testBit i) :=
    pack_congr _ _ _ (fun _ _ => raw _ _ _ i.isLt)
  rw [e]; exact (show ∀ j : Fin 9, pack rows (fun r => r.testBit j)∈base by decide +kernel) i

theorem output_col {C : Circuit} (spec : ∀ r,wire C r C.output=edge r) : col C C.output=target :=
  (pack_congr _ _ _ (fun r _ => spec r)).trans (by decide +kernel)

theorem out_of_range (C : Circuit) (i) (hi : 9+C.size ≤ i) : col C i=0 :=
  (pack_congr _ _ (fun _ => false) (fun _ _ => beyond _ _ _ hi)).trans (by decide +kernel)

def Shape (g : Gate) : Prop := (g.op=.not ∧ g.inputs.length=1) ∨
    ((g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2)

theorem compute {C : Circuit} (before : Before C) (j : Fin C.size) (shape : Shape (C.gates.get j))
    {vs : List Nat} (haveWire : ∀ i∈(C.gates.get j).inputs, col C i∈vs) :
    PetersenSelector.next vs (col C (9+j.val)) := by
  obtain ⟨op,n⟩|⟨op,n⟩ := shape
  · obtain ⟨a,la⟩ := List.length_eq_one_iff.mp n
    have val (r) : wire C r (9+j.val)= !wire C r a := by rw [gateValue C before r j,op,la];rfl
    have ha := haveWire a (by simp [la])
    refine ⟨col C a,ha,col C a,ha,Or.inr (Or.inr ?_)⟩
    exact (pack_congr rows _ _ (fun r _ => val r)).trans (pack_not rows _)
  · obtain ⟨a,b,ls⟩ := List.length_eq_two.mp n
    refine ⟨col C a,haveWire a (by simp [ls]),col C b,haveWire b (by simp [ls]),?_⟩
    rcases op with op|op
    · left
      have val (r) : wire C r (9+j.val)=(wire C r a && wire C r b) := by rw [gateValue C before r j,op,ls];simp [GateOp.eval]
      exact (pack_congr rows _ _ (fun r _ => val r)).trans (pack_and rows _ _)
    · right;left
      have val (r) : wire C r (9+j.val)=(wire C r a || wire C r b) := by rw [gateValue C before r j,op,ls];simp [GateOp.eval]
      exact (pack_congr rows _ _ (fun r _ => val r)).trans (pack_or rows _ _)

end PetersenSuffix
namespace PetersenSuffix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PetersenCompanions4225 PetersenSelector

def Own (C : Circuit) (v : Fin 9) (j : Fin C.size) := ∀ t : Fin C.size, v.val∈(C.gates.get t).inputs → t=j

theorem reader_data {C v w} (before : Before C) (fan : FanInTwo C) (hr : CommonReader C w v) :
    ∃ j : Fin C.size, Own C v j ∧ GuardEntry C w (j.val,v.val) ∧
      ((C.gates.get j).inputs=[v.val,w] ∨ (C.gates.get j).inputs=[w,v.val]) := by
  obtain ⟨j,e,ls⟩ := reader_entry before fan hr
  obtain ⟨t,only,_⟩ := hr
  have h := (only j).mp (by rcases ls with a|a  <;>  simp [a])
  exact ⟨j,fun i m => ((only i).mp m).trans h.symm,e,ls⟩

theorem row_data : ∀ r∈rows, r < 512 ∧ coreRow r≠0 ∧ edge (coreRow r)=false ∧
    (coreRow r=1 ∨ coreRow r=2 ∨ coreRow r=4) ∧
    (r=coreRow r ∨ r=coreRow r ||| 16 ∨ r=coreRow r ||| 64 ∨ r=coreRow r ||| 128) := by decide +kernel

theorem reader_col {C w} (before : Before C) (spec : ∀ r, wire C r C.output=edge r) (h : ThreeReaders C w)
    (v : Fin 9) (j : Fin C.size) (e : GuardEntry C w (j.val,v.val)) : col C (9+j.val) ∈ base := by
  have eq : col C (9+j.val)=col C v := by
    apply pack_congr
    intro r hr
    obtain ⟨lt,nz,ind,_⟩ := row_data r hr
    exact e.2.2.2 ⟨r,lt⟩ (common_zero before spec h ⟨r,lt⟩ nz ind)
  exact eq ▸ raw_col C v

theorem early_col {C : Circuit} (before : Before C) {j4 j6 j7 : Fin C.size}
    (a : Own C 4 j4) (b : Own C 6 j6) (c : Own C 7 j7) (i : Nat)
    (i4 : i < 9+j4.val) (i6 : i < 9+j6.val) (i7 : i < 9+j7.val) : col C i∈base := by
  by_cases rawBit : i < 9
  · exact raw_col C ⟨i,rawBit⟩
  have stable (v : Fin 9) (j : Fin C.size) (own : Own C v j) (hi : i < 9+j.val) (r : Nat) :
      wire C r i=wire C (r ||| 2^v.val) i :=
    prefixMatching C before v j _ _ (by intro t _ ne; simp [Nat.testBit_or,Ne.symm ne]) own i hi
      (by have := v.isLt;omega)
  let sample (r : Nat) := if coreRow r=1 then wire C 1 i else if coreRow r=2 then wire C 2 i else wire C 4 i
  have equal : col C i=pack rows sample := by
    apply pack_congr
    intro r hr
    obtain ⟨_,_,_,which,form⟩ := row_data r hr
    have s : wire C r i=wire C (coreRow r) i := by
      rcases form with f|f|f|f
      · exact congrArg (fun m => wire C m i) f
      · exact (congrArg (fun m => wire C m i) f).trans (stable 4 j4 a i4 _).symm
      · exact (congrArg (fun m => wire C m i) f).trans (stable 6 j6 b i6 _).symm
      · exact (congrArg (fun m => wire C m i) f).trans (stable 7 j7 c i7 _).symm
    rw [s]
    rcases which with eq|eq|eq  <;>  simp [sample,eq]
  rw [equal]
  exact (show ∀ a b c : Bool, pack rows (fun r => if coreRow r=1 then a else if coreRow r=2 then b else c)∈base by decide +kernel) _ _ _

end PetersenSuffix
namespace PetersenSuffix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PetersenCompanions4225 PetersenSelector

def remaining (a b c j : Nat) := (if j ≤ a then 1 else 0)+(if j ≤ b then 1 else 0)+(if j ≤ c then 1 else 0)

theorem remaining_skip {a b c j} (ab : a≠b) (ac : a≠c) (bc : b≠c) (hit : j=a ∨ j=b ∨ j=c) :
    remaining a b c j=remaining a b c (j+1)+1 := by
  unfold remaining;split_ifs  <;>  omega

theorem remaining_keep {a b c j} (miss : ¬(j=a ∨ j=b ∨ j=c)) :
    remaining a b c j=remaining a b c (j+1) := by
  unfold remaining;split_ifs  <;>  omega

theorem compile_suffix {C : Circuit} (before : Before C) (spec : ∀ r,wire C r C.output=edge r)
    (norm : ∀ t : Fin C.size, Shape (C.gates.get t)) (a b c : Fin C.size)
    (ab : a≠b) (ac : a≠c) (bc : b≠c)
    (easy : ∀ t : Fin C.size, (t=a ∨ t=b ∨ t=c) → col C (9+t.val)∈base)
    (j count : Nat) (endAt : j+count=C.size)
    (vs : List Nat) (raws : ∀ z∈base,z∈vs) (prior : ∀ i < 9+j,col C i∈vs) :
    ∃ k, k+remaining a.val b.val c.val j=count ∧ reaches k vs target := by
  induction count generalizing j vs with
  | zero =>
    have e : C.size=j := by omega
    have h : remaining a.val b.val c.val j=0 := by
      have := a.isLt;have := b.isLt;have := c.isLt
      simp only [remaining];split_ifs  <;>  omega
    refine ⟨0,by omega,?_⟩
    change target ∈ vs
    rw [←output_col spec]
    by_cases ok : C.output < 9+j
    · exact prior _ ok
    · rw [out_of_range C _ (by omega)]
      exact raws 0 (by decide)
  | succ count ih =>
    let t : Fin C.size := ⟨j,by omega⟩
    have end' : (j+1)+count=C.size := by omega
    by_cases hit : t=a ∨ t=b ∨ t=c
    · have step := raws _ (easy t hit)
      have old : ∀ i < 9+(j+1),col C i∈vs := by
        intro i hi
        by_cases early : i < 9+j
        · exact prior _ early
        · have eq : i=9+t.val := by dsimp [t];omega
          exact eq ▸ step
      obtain ⟨k,n,h⟩ := ih _ end' vs raws old
      have r : remaining a.val b.val c.val j=remaining a.val b.val c.val (j+1)+1 :=
        remaining_skip (fun e => ab (Fin.ext e)) (fun e => ac (Fin.ext e)) (fun e => bc (Fin.ext e)) (by
          rcases hit with ht|ht|ht
          · exact Or.inl (congrArg Fin.val ht)
          · exact Or.inr (Or.inl (congrArg Fin.val ht))
          · exact Or.inr (Or.inr (congrArg Fin.val ht)))
      exact ⟨k,by omega,h⟩
    · have step := compute before t (norm t) (vs:=vs) (fun i hi => prior i (before t i hi))
      let y := col C (9+t.val)
      have old : ∀ i < 9+(j+1),col C i∈y::vs := by
        intro i hi
        by_cases early : i < 9+j
        · exact List.mem_cons_of_mem _ (prior _ early)
        · have eq : i=9+t.val := by dsimp [t];omega
          rw [eq];exact List.mem_cons_self
      obtain ⟨k,n,h⟩ := ih _ end' (y::vs) (fun z hz => List.mem_cons_of_mem _ (raws z hz)) old
      have r : remaining a.val b.val c.val j=remaining a.val b.val c.val (j+1) :=
        remaining_keep (by
          rintro (r|r|r)
          · exact hit (Or.inl (Fin.ext r))
          · exact hit (Or.inr (Or.inl (Fin.ext r)))
          · exact hit (Or.inr (Or.inr (Fin.ext r))))
      exact ⟨k+1,by omega,y,step,h⟩

theorem earliest_bound {C w} (before : Before C) (fan : FanInTwo C)
    (spec : ∀ r,wire C r C.output=edge r) (norm : ∀ t : Fin C.size, Shape (C.gates.get t))
    (s : ThreeReaders C w) : ∃ j : Fin C.size, w < 9+j.val ∧ j.val+8 ≤ C.size := by
  obtain ⟨a,oa,ea,la⟩ := reader_data before fan s.1
  obtain ⟨b,ob,eb,lb⟩ := reader_data before fan s.2.1
  obtain ⟨c,oc,ec,lc⟩ := reader_data before fan s.2.2
  have ab : a≠b := by rintro rfl;exact different_entries _ _ _ (by decide) _ la lb
  have ac : a≠c := by rintro rfl;exact different_entries _ _ _ (by decide) _ la lc
  have bc : b≠c := by rintro rfl;exact different_entries _ _ _ (by decide) _ lb lc
  let j := min a (min b c)
  have ja : j ≤ a := min_le_left _ _
  have jb : j ≤ b := le_trans (min_le_right _ _) (min_le_left _ _)
  have jc : j ≤ c := le_trans (min_le_right _ _) (min_le_right _ _)
  have va : j.val ≤ a.val := ja
  have vb : j.val ≤ b.val := jb
  have vc : j.val ≤ c.val := jc
  have readers : ∀ t : Fin C.size, t=a ∨ t=b ∨ t=c → col C (9+t.val)∈base := by
    rintro t (rfl|rfl|rfl)
    · exact reader_col before spec s 4 _ ea
    · exact reader_col before spec s 6 _ eb
    · exact reader_col before spec s 7 _ ec
  obtain ⟨k,n,r⟩ := compile_suffix before spec norm a b c ab ac bc readers j.val (C.size-j.val)
    (by have := j.isLt;omega) base (fun _ h => h)
    (fun i hi => early_col before oa ob oc i (by omega) (by omega) (by omega))
  have lim : 4 < k := by by_contra! bad;exact no_selector bad r
  have rem : remaining a.val b.val c.val j.val=3 := by simp [remaining,va,vb,vc]
  refine ⟨j,?_,by omega⟩
  change w < 9+(min a.val (min b.val c.val))
  have x := ea.2.2.1;have y := eb.2.2.1;have z := ec.2.2.1
  change w < 9+a.val at x;change w < 9+b.val at y;change w < 9+c.val at z
  omega

end PetersenSuffix
open PetersenSuffix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PetersenCompanions4225
set_option maxRecDepth 12000 in
theorem PetersenCertificate.common_reader_cut : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.IsMinimalCircuit 9 C → PEqualNP.MetaComplexity.circuitFun 9 C=(fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List Nat).any (fun k => x (Fin.ofNat 9 (k/9)) && x (Fin.ofNat 9 (k%9)))) → (∀ j : Fin C.size, let g := C.gates.get j
        (∀ i∈g.inputs, i < 9+j.val) ∧ (g.op=PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length=1 ∨ g.op≠PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length=2)) →
    ∀ J : Fin 9 → Fin C.size, (∀ v∈([4,6,7] : List (Fin 9)), (∀ j : Fin C.size, v.val∈(C.gates.get j).inputs ↔ j=J v) ∧
        (C.gates.get (J v)).op=PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ w : Nat, (∀ v∈([4,6,7] : List (Fin 9)), w≠v.val ∧ w∈(C.gates.get (J v)).inputs) → let Y := fun r : Nat => (C.wires (List.ofFn (fun i : Fin 9 => r.testBit i.val))).getD w false
      w ≤ C.size ∧ Y 0=true ∧ (∀ i∈([0,1,2,3,5,8] : List Nat), Y (2^i)=false) ∧
        ∃ r : Fin 512, r.val &&& 303=r.val ∧ r.val≠0 ∧ Y r.val=true := by
  intro C minC funC norm J mark w com
  have before : Before C := fun j => (norm j).1
  have spec (r) : wire C r C.output=edge r := by
    have h := congrFun funC (bitInput r)
    exact h
  have shape (j : Fin C.size) : Shape (C.gates.get j) := by
    obtain ⟨gop,_⟩ := minC.1 _ (List.get_mem _ j)
    rcases (norm j).2 with h|⟨isNot,n⟩
    · exact Or.inl h
    · right;refine ⟨?_,n⟩
      simpa [Set.mem_insert_iff,Set.mem_singleton_iff,isNot] using gop
  have rd (v : Fin 9) (hv : v∈([4,6,7] : List (Fin 9))) : CommonReader C w v :=
    ⟨J v,(mark v hv).1,(mark v hv).2,(com v hv).1,(com v hv).2⟩
  have allThree : ThreeReaders C w := ⟨rd 4 (by decide),rd 6 (by decide),rd 7 (by decide)⟩
  obtain ⟨j,early,bound⟩ := earliest_bound before minC.1 spec shape allThree
  obtain ⟨zero,single,r,proj,positive,hi⟩ := common_signature before minC spec allThree
  refine ⟨by omega,zero,single,r,proj,?_,hi⟩
  intro eq
  rw [eq] at positive
  exact (by decide : edge 0 ≠ true) positive
