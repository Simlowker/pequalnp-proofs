import RenameRows2585
namespace IncidenceCover.Three
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

def edgeSet (m : Fin 512) := Finset.univ.filter (fun e : Fin 3 × Fin 3 => m.val.testBit (3*e.1.val+e.2.val))
def encode (E : Finset (Fin 3 × Fin 3)) := Fin.ofNat 512 (∑ x ∈ E, 2^(3*x.1.val+x.2.val))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem decode_correct : ∀ E : Finset (Fin 3 × Fin 3), edgeSet (encode E)=E := by decide +kernel

inductive Shape where | g87 | g94 | g238 deriving DecidableEq
inductive Choice where
  | rectangle | sparse | cover (mask : Nat) | hard (shape : Shape) (perm : Nat)

def sBound : Shape → Nat
  | .g87 | .g94 => 6
  | .g238 => 7

def sRows : Shape → List Nat
  | .g87 => [7, 9, 12, 17, 18, 33, 38, 42, 52, 56]
  | .g94 => [7, 9, 10, 12, 17, 18, 33, 38, 52, 56]
  | .g238 => [7, 9, 10, 12, 17, 18, 20, 33, 34, 36, 56]

def sTarget : Shape → Nat → Bool
  | .g87, r => (r.testBit 0 && r.testBit 3) || (r.testBit 0 && r.testBit 4) || (r.testBit 0 && r.testBit 5) || (r.testBit 1 && r.testBit 4) || (r.testBit 2 && r.testBit 3)
  | .g94, r => (r.testBit 0 && r.testBit 4) || (r.testBit 0 && r.testBit 5) || (r.testBit 1 && r.testBit 3) || (r.testBit 1 && r.testBit 4) || (r.testBit 2 && r.testBit 3)
  | .g238, r => (r.testBit 0 && r.testBit 4) || (r.testBit 0 && r.testBit 5) || (r.testBit 1 && r.testBit 3) || (r.testBit 1 && r.testBit 5) || (r.testBit 2 && r.testBit 3) || (r.testBit 2 && r.testBit 4)

def permute (a : Nat) (i : Fin 6) := Fin.ofNat 6 ((a >>> (3*i.val)) % 8)
def leftPart (a : Nat) := Finset.univ.filter (fun i : Fin 3 => a.testBit i.val)
def rightPart (a : Nat) := Finset.univ.filter (fun j : Fin 3 => a.testBit (3+j.val))
def choices : Array Choice := #[
(.cover 3), (.cover 3), (.cover 3), (.cover 3), (.cover 3), (.cover 3), (.cover 3), (.cover 3),
(.cover 3), (.cover 3), (.cover 3), (.cover 3), (.cover 3), (.cover 3), (.cover 3), (.cover 3),
(.cover 3), (.cover 3), (.cover 3), (.cover 3), (.cover 3), (.cover 3), (.cover 3), (.cover 3),
(.cover 3), (.cover 3), (.cover 3), (.rectangle), (.cover 3), (.cover 3), (.cover 3), (.rectangle),
(.cover 3), (.cover 3), (.cover 3), (.cover 3), (.cover 3), (.cover 3), (.cover 3), (.cover 3),
(.cover 3), (.cover 3), (.cover 3), (.cover 3), (.cover 3), (.rectangle), (.cover 3), (.rectangle),
(.cover 3), (.cover 3), (.cover 3), (.cover 3), (.cover 3), (.cover 3), (.rectangle), (.rectangle),
(.cover 3), (.cover 3), (.cover 3), (.rectangle), (.cover 3), (.rectangle), (.rectangle), (.rectangle),
(.cover 5), (.cover 5), (.cover 5), (.cover 5), (.cover 5), (.cover 5), (.cover 5), (.cover 5),
(.cover 9), (.cover 9), (.cover 9), (.cover 9), (.cover 9), (.cover 9), (.cover 9), (.cover 9),
(.cover 6), (.cover 10), (.cover 20), (.cover 24), (.sparse), (.sparse), (.sparse), (.hard .g87 181896),
(.cover 6), (.cover 10), (.cover 24), (.rectangle), (.sparse), (.hard .g87 69987), (.hard .g94 181896), (.rectangle),
(.cover 6), (.cover 10), (.sparse), (.sparse), (.cover 36), (.cover 40), (.sparse), (.hard .g87 153224),
(.cover 6), (.cover 10), (.sparse), (.hard .g87 41315), (.cover 40), (.rectangle), (.hard .g94 153224), (.rectangle),
(.cover 6), (.cover 10), (.sparse), (.hard .g94 181889), (.sparse), (.hard .g94 153217), (.rectangle), (.rectangle),
(.cover 6), (.cover 10), (.hard .g87 181889), (.rectangle), (.hard .g87 153217), (.rectangle), (.rectangle), (.rectangle),
(.cover 5), (.cover 5), (.cover 5), (.cover 5), (.cover 5), (.cover 5), (.cover 5), (.cover 5),
(.cover 6), (.cover 12), (.cover 18), (.cover 24), (.sparse), (.sparse), (.sparse), (.hard .g87 178312),
(.cover 17), (.cover 17), (.cover 17), (.cover 17), (.cover 17), (.cover 17), (.cover 17), (.cover 17),
(.cover 6), (.cover 24), (.cover 18), (.rectangle), (.sparse), (.hard .g94 178312), (.hard .g87 66403), (.rectangle),
(.cover 6), (.sparse), (.cover 18), (.sparse), (.cover 36), (.sparse), (.cover 48), (.hard .g87 146056),
(.cover 6), (.sparse), (.cover 18), (.hard .g94 178305), (.sparse), (.rectangle), (.hard .g94 146049), (.rectangle),
(.cover 6), (.sparse), (.cover 18), (.hard .g87 34147), (.cover 48), (.hard .g94 146056), (.rectangle), (.rectangle),
(.cover 6), (.hard .g87 178305), (.cover 18), (.rectangle), (.hard .g87 146049), (.rectangle), (.rectangle), (.rectangle),
(.cover 5), (.cover 5), (.cover 5), (.rectangle), (.cover 5), (.cover 5), (.cover 5), (.rectangle),
(.cover 6), (.cover 12), (.cover 24), (.rectangle), (.sparse), (.hard .g87 69931), (.hard .g94 181840), (.rectangle),
(.cover 6), (.cover 24), (.cover 20), (.rectangle), (.sparse), (.hard .g94 178256), (.hard .g87 66347), (.rectangle),
(.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle),
(.cover 6), (.sparse), (.sparse), (.rectangle), (.cover 36), (.hard .g94 120849), (.hard .g94 117265), (.rectangle),
(.cover 6), (.hard .g87 69917), (.hard .g94 178242), (.rectangle), (.hard .g94 120842), (.rectangle), (.hard .g238 181896), (.rectangle),
(.cover 6), (.hard .g94 181826), (.hard .g87 66333), (.rectangle), (.hard .g94 117258), (.hard .g238 178312), (.rectangle), (.rectangle),
(.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle),
(.cover 5), (.cover 5), (.cover 5), (.cover 5), (.cover 5), (.cover 5), (.cover 5), (.cover 5),
(.cover 6), (.cover 12), (.sparse), (.sparse), (.cover 34), (.cover 40), (.sparse), (.hard .g87 120968),
(.cover 6), (.sparse), (.cover 20), (.sparse), (.cover 34), (.sparse), (.cover 48), (.hard .g87 117384),
(.cover 6), (.sparse), (.sparse), (.rectangle), (.cover 34), (.hard .g94 120961), (.hard .g94 117377), (.rectangle),
(.cover 33), (.cover 33), (.cover 33), (.cover 33), (.cover 33), (.cover 33), (.cover 33), (.cover 33),
(.cover 6), (.cover 40), (.sparse), (.hard .g94 120968), (.cover 34), (.rectangle), (.hard .g87 9059), (.rectangle),
(.cover 6), (.sparse), (.cover 48), (.hard .g94 117384), (.cover 34), (.hard .g87 5475), (.rectangle), (.rectangle),
(.cover 6), (.hard .g87 120961), (.hard .g87 117377), (.rectangle), (.cover 34), (.rectangle), (.rectangle), (.rectangle),
(.cover 5), (.cover 5), (.cover 5), (.cover 5), (.cover 5), (.rectangle), (.cover 5), (.rectangle),
(.cover 6), (.cover 12), (.sparse), (.hard .g87 41259), (.cover 40), (.rectangle), (.hard .g94 153168), (.rectangle),
(.cover 6), (.sparse), (.cover 20), (.hard .g94 178193), (.sparse), (.rectangle), (.hard .g94 145937), (.rectangle),
(.cover 6), (.hard .g87 41245), (.hard .g94 178186), (.rectangle), (.hard .g94 120898), (.rectangle), (.hard .g238 153224), (.rectangle),
(.cover 6), (.cover 40), (.sparse), (.hard .g94 120912), (.cover 36), (.rectangle), (.hard .g87 9003), (.rectangle),
(.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle),
(.cover 6), (.hard .g94 153154), (.hard .g94 145930), (.hard .g238 120968), (.hard .g87 8989), (.rectangle), (.rectangle), (.rectangle),
(.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle),
(.cover 5), (.cover 5), (.cover 5), (.cover 5), (.cover 5), (.cover 5), (.rectangle), (.rectangle),
(.cover 6), (.cover 12), (.sparse), (.hard .g94 181777), (.sparse), (.hard .g94 153105), (.rectangle), (.rectangle),
(.cover 6), (.sparse), (.cover 20), (.hard .g87 34091), (.cover 48), (.hard .g94 146000), (.rectangle), (.rectangle),
(.cover 6), (.hard .g94 181770), (.hard .g87 34077), (.rectangle), (.hard .g94 117314), (.hard .g238 146056), (.rectangle), (.rectangle),
(.cover 6), (.sparse), (.cover 48), (.hard .g94 117328), (.cover 36), (.hard .g87 5419), (.rectangle), (.rectangle),
(.cover 6), (.hard .g94 153098), (.hard .g94 145986), (.hard .g238 117384), (.hard .g87 5405), (.rectangle), (.rectangle), (.rectangle),
(.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle),
(.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle),
(.cover 5), (.cover 5), (.cover 5), (.rectangle), (.cover 5), (.rectangle), (.rectangle), (.rectangle),
(.cover 6), (.cover 12), (.hard .g87 181777), (.rectangle), (.hard .g87 153105), (.rectangle), (.rectangle), (.rectangle),
(.cover 6), (.hard .g87 178193), (.cover 20), (.rectangle), (.hard .g87 145937), (.rectangle), (.rectangle), (.rectangle),
(.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle),
(.cover 6), (.hard .g87 120849), (.hard .g87 117265), (.rectangle), (.cover 36), (.rectangle), (.rectangle), (.rectangle),
(.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle),
(.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle),
(.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle), (.rectangle)]
def choice (m : Fin 512) : Choice := choices[m.val]?.getD .rectangle
def valid (E : Finset (Fin 3 × Fin 3)) : Choice → Prop
  | .rectangle => ¬rectangleFree E
  | .sparse => E.card≤(E.image Prod.snd).card+1
  | .cover c => (leftPart c).card+(rightPart c).card≤2 ∧ ∀ e∈E,e.1∈leftPart c ∨ e.2∈rightPart c
  | .hard t perm => E.card+1 ≤ sBound t ∧ ∀ r∈sRows t,signedRow E (permute perm) r=sTarget t r

instance (E) (c) : Decidable (valid E c) := by
  cases c <;> unfold valid <;> try unfold rectangleFree
  all_goals infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid_choices : ∀ m : Fin 512, valid (edgeSet m) (choice m) := by decide +kernel

def lowerCert (t : Shape) := ¬PEqualNP.Defs.LratEncoding.FormulaSat
  (PEqualNP.Defs.LratEncoding.enc2 6 (sBound t) (sTarget t) (sRows t))
set_option maxRecDepth 32000 in
theorem finished (cert : ∀ t, lowerCert t) {E : Finset (Fin 3 × Fin 3)} {C : Circuit}
    (rect : rectangleFree E) (ao : IsAO2 6 C) (correct : computes E C) : replacement E C := by
  have ok := valid_choices (encode E)
  rw [decode_correct] at ok
  cases h : choice (encode E) with
  | rectangle => rw [h] at ok; exact False.elim (ok rect)
  | sparse => rw [h] at ok; exact symmetric_case rect ao correct (Or.inl ok)
  | cover c => rw [h] at ok; exact small_cover rect ao correct _ _ ok.2 ok.1
  | hard t perm =>
    rw [h] at ok
    obtain ⟨card,ag⟩ := ok
    have bd := rows_lower E C ao correct (permute perm) (sBound t) (sTarget t) (sRows t)
      (by cases t <;> decide) (by cases t <;> decide) ag (cert t)
    apply from_cover Finset.univ ∅ (fun e _ => Or.inl (Finset.mem_univ _))
    simp only [Finset.card_univ,Fintype.card_fin,Finset.card_empty,Nat.add_zero]
    omega
#print axioms finished
end IncidenceCover.Three
