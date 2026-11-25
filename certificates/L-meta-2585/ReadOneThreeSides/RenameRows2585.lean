import TwoCover2585
import Ref4805
namespace IncidenceCover.Three
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Defs.LratEncoding
-- The wire-relabelling argument follows upstream R_meta_1934_271 (Apache-2.0).
def renameGate (ρ : ℕ → ℕ) (g : Gate) : Gate :=
  { op := g.op, inputs := g.inputs.map ρ }

def renameCircuit (ρ : ℕ → ℕ) (C : Circuit) : Circuit :=
  { gates := C.gates.map (renameGate ρ), output := ρ C.output }

def wireRel (ρ : ℕ → ℕ) (w v : List Bool) : Prop :=
  ∀ i, v.getD (ρ i) false = w.getD i false

theorem wireRel_append (ρ : ℕ → ℕ) (n : ℕ)
    (hfix : ∀ i, n ≤ i → ρ i = i) (hlt : ∀ i, i < n → ρ i < n)
    (w v : List Bool) (hlen : w.length = v.length) (hn : n ≤ w.length)
    (hrel : wireRel ρ w v) (b : Bool) : wireRel ρ (w ++ [b]) (v ++ [b]) := by
  intro i
  by_cases hi : i < w.length
  · have hri : ρ i < v.length := by
      by_cases hin : i < n
      · have := hlt i hin
        omega
      · rw [hfix i (by omega)]
        omega
    rw [List.getD_append _ _ _ _ hri, List.getD_append _ _ _ _ hi]
    exact hrel i
  · have hin : n ≤ i := by omega
    rw [hfix i hin]
    rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), hlen]

theorem wires_rename (ρ : ℕ → ℕ) (n : ℕ)
    (hfix : ∀ i, n ≤ i → ρ i = i) (hlt : ∀ i, i < n → ρ i < n)
    (gs : List Gate) (w v : List Bool) (hlen : w.length = v.length)
    (hn : n ≤ w.length) (hrel : wireRel ρ w v) :
    wireRel ρ
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
      ((gs.map (renameGate ρ)).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) v) := by
  induction gs generalizing w v with
  | nil => exact hrel
  | cons g gs ih =>
    simp only [List.foldl_cons, List.map_cons]
    have hval : (renameGate ρ g).op.eval
        ((renameGate ρ g).inputs.map fun i => v.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [renameGate, List.map_map]
      congr 2
      exact funext hrel
    rw [hval]
    apply ih
    · simp [hlen]
    · simp only [List.length_append, List.length_singleton]
      omega
    · exact wireRel_append ρ n hfix hlt w v hlen hn hrel _

theorem eval_rename (ρ : ℕ → ℕ) (n : ℕ)
    (hfix : ∀ i, n ≤ i → ρ i = i) (hlt : ∀ i, i < n → ρ i < n)
    (C : Circuit) (w v : List Bool) (hlen : w.length = v.length)
    (hn : n ≤ w.length) (hrel : wireRel ρ w v) :
    (renameCircuit ρ C).eval v = C.eval w := by
  exact wires_rename ρ n hfix hlt C.gates w v hlen hn hrel C.output

theorem size_rename (ρ : ℕ → ℕ) (C : Circuit) :
    (renameCircuit ρ C).size = C.size := by
  change (C.gates.map (renameGate ρ)).length = C.gates.length
  simp only [List.length_map]


def onRaw (σ : Fin 6 → Fin 6) (i : Nat) := if h : i<6 then (σ ⟨i,h⟩).val else i
def signedRow (E : Finset (Fin 3 × Fin 3)) (σ : Fin 6 → Fin 6) (r : Nat) :=
  decide (∃ (p l : Fin 3), (p,l)∈E ∧ r.testBit (σ (Fin.castAdd 3 p)).val=true ∧
      r.testBit (σ (Fin.natAdd 3 l)).val=true)

theorem relabel_mono (C : Circuit) (ao : IsAO2 6 C) (σ : Fin 6 → Fin 6) :
    Monotone2 (renameCircuit (onRaw σ) C) := by
  intro g hg
  obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hg
  exact ⟨ao.1 h hh,by simp [renameGate,ao.2.2 h hh]⟩

theorem input_get {n : Nat} (v : Fin n → Bool) (i : Fin n) :
    (List.ofFn v).getD i.val false=v i := by simp [List.getD_eq_getElem?_getD]

theorem on_row (E : Finset (Fin 3 × Fin 3)) (C : Circuit) (correct : computes E C)
    (σ : Fin 6 → Fin 6) (r : Nat) :
    (renameCircuit (onRaw σ) C).eval (List.ofFn fun i : Fin 6 => r.testBit i.val) =
      signedRow E σ r := by
  let y : Fin 6 → Bool := fun i => r.testBit (σ i).val
  have rel : wireRel (onRaw σ) (List.ofFn y) (List.ofFn fun i : Fin 6 => r.testBit i.val) := by
    intro i
    by_cases hi : i<6
    · change (List.ofFn _).getD (onRaw σ i) false=(List.ofFn y).getD (⟨i,hi⟩ : Fin 6).val false
      rw [show onRaw σ i = (σ ⟨i,hi⟩).val by simp [onRaw,hi],input_get,input_get]
    · simp [List.getD_eq_getElem?_getD,onRaw,hi]
  rw [eval_rename _ 6 (fun i hi => by simp [onRaw,Nat.not_lt.mpr hi])
    (fun i hi => by simp [onRaw,hi]) C _ _ (by simp) (by simp) rel]
  exact correct y

theorem rows_lower (E : Finset (Fin 3 × Fin 3)) (C : Circuit) (ao : IsAO2 6 C)
    (correct : computes E C) (σ : Fin 6 → Fin 6) (s : Nat) (g : Nat → Bool) (rows : List Nat)
    (pos : 0<s) (bounded : ∀ r∈rows, r<64) (agrees : ∀ r∈rows, signedRow E σ r=g r)
    (unsat : ¬FormulaSat (enc2 6 s g rows)) : s<C.size := by
  by_contra! small
  let D := renameCircuit (onRaw σ) C
  have fits : D.size ≤ s := by simpa [D,size_rename] using small
  obtain ⟨k,_,a,ha⟩ := PEqualNP.Outside.L_meta_4805 6 s g rows D pos bounded
    (relabel_mono C ao σ) fits (fun r hr => (on_row E C correct σ r).trans (agrees r hr))
  exact unsat ⟨a,fun c hc => ha c (List.mem_append_left _ hc)⟩
#print axioms rows_lower
end IncidenceCover.Three
