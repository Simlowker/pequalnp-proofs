import PEqualNP.Outside.L_meta_11223
import PEqualNP.Outside.L_meta_7398
import PEqualNP.Outside.L_meta_3223

/-!
# Exact sizes of restricted circuits for the graph of L-meta-11224

The vertices are numbered 0 through 6 and the edges are 03, 04, 14, 05, 15,
35, 06, 26, 36 and 46. A true output means that some edge has two true
endpoints. Gate count and evaluation use the project's circuit definitions.

For every subset of vertices set to zero, Seven11224.Atlas.bounds gives the
exact minimum with AND, OR and arbitrary NOT gates. The matching witness
for every row uses only AND and OR. A set is encoded by the sum of 2^v over
its vertices. Bit zero stands for vertex zero. Atlas.costData contains the
128 values in mask order and Atlas.candidateData contains the circuits.

Setting one input (in vertex order) to zero gives minima 8, 9, 10, 7, 8, 8, 6.
Setting one input to one gives minima 3, 7, 7, 4, 4, 5, 5. High.exact checks
the latter seven values. Readers.per_input bounds direct uses of each raw
input in any correct circuit, following the project's normalization for NOT
gates. In every optimum, vertex 2 has exactly one effective reading gate;
that gate is an OR. Readers.all_read_budgets proves a joint constraint for
any set of inputs. The minimum after setting the set to zero, plus the number
of normalized gates reading at least one member, is at most the original
circuit size. Each gate is counted once even if it reads two set members.

The unrestricted lower bound of 11 and the search certificates for smaller
instances come from TSGut, open-goat/pequalnp-proofs PR 15646, commit
91175ef5754142d881feadbb3804d8192f619fff. TSGut credits Trey Kind and the
authors of the earlier project search code. This file converts TSGut's masked
search certificates into lower bounds for actual restricted circuit functions.
It supplies the remaining cases via support, identifications and gate deletion,
and explicit monotone upper circuits for the whole table. The input accounting
also uses the public L-meta-7398 and L-meta-3223 gate-elimination results.
-/

namespace Seven11224
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def target (x : Fin 7 → Bool) := decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def upper : Circuit := ⟨[⟨.or,[0,2]⟩, ⟨.or,[0,1]⟩, ⟨.or,[0,5]⟩, ⟨.or,[4,5]⟩, ⟨.or,[7,4]⟩, ⟨.or,[9,6]⟩, ⟨.and,[8,10]⟩, ⟨.and,[3,12]⟩, ⟨.and,[11,6]⟩, ⟨.or,[13,14]⟩, ⟨.or,[16,15]⟩],17⟩
theorem cost : upper.size=11 := rfl
theorem legal : Monotone2 upper := by
  intro g hg
  simp only [upper,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem computes : ∀ x, upper.eval (List.ofFn x)=target x := by decide +kernel
end Seven11224

namespace Seven11224
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
theorem no_smaller (D : Circuit) (legal : FanInTwo D)
    (correct : ∀ x : Fin 7 → Bool, D.eval (List.ofFn x)=target x) : 11 ≤ D.size := by
  by_contra! tooSmall
  apply PEqualNP.Outside.L_meta_11223.iroot D.size (by omega)
  apply PEqualNP.Outside.L_meta_11223.bridge D legal
  intro x
  exact (correct x).trans (PEqualNP.Outside.L_meta_11223.dec_f x)

theorem exact_budget (n : Nat) : HasCircuitSize 7 target n ↔ 11 ≤ n := by
  constructor
  · rintro ⟨D,legal,size,correct⟩
    exact (no_smaller D legal correct).trans size
  · intro enough
    refine ⟨upper,?_,cost.le.trans enough,computes⟩
    intro g hg
    obtain ⟨op, inputs⟩ := legal g hg
    rcases (show g.op=.and ∨ g.op=.or from by simpa using op) with a|b
    · exact ⟨by simp [a],inputs⟩
    · exact ⟨by simp [b],inputs⟩
end Seven11224

namespace Seven11224.Atlas
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_11223
def pinned (z : Fin 128) (x : Fin 7 → Bool) := f (fun i => if z.val.testBit i.val then false else x i)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem maskFacts : (∀ z : Fin 128, EF &&& mz z.val = tz z.val) ∧
    ∀ (z : Fin 128) (i : Fin 7), z.val.testBit i.val=true → rawP.getD i.val 0 &&& mz z.val = 0 := by
  constructor <;> decide +kernel
theorem bridgePinned (z : Fin 128) (D : Circuit) (hD : FanInTwo D)
    (hf : ∀ x : Fin 7 → Bool, D.eval (List.ofFn x) = pinned z x) :
    Sol Z0 (mz z.val) (tz z.val) D.size (C (mz z.val) (WZ [] z.val)) := by
  obtain ⟨gates, out⟩ := D
  let row : ℕ → Fin 7 → Bool := fun k v => (rawP.getD v.val 0).testBit k
  let init : List ℕ := rawP.map (· &&& mz z.val)
  have hinit_sub : ∀ x ∈ init, x &&& mz z.val = x := by
    intro x hx
    simp only [init, List.mem_map] at hx
    obtain ⟨w, _, rfl⟩ := hx
    rw [Nat.and_assoc, Nat.and_self]
  have hinit_mem : ∀ x ∈ init, x ∈ C (mz z.val) (WZ [] z.val) := by
    intro x hx
    simp only [init, List.mem_map] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
  have hinit_bits : ∀ k, (mz z.val).testBit k = true → init.map (fun x => x.testBit k) = List.ofFn (row k) := by
    intro k hk
    simp only [init, List.map_map, Function.comp_def, Nat.testBit_and, hk, Bool.and_true]
    rw [row_list]
  have hout : (ex (mz z.val) gates init).getD out 0 = tz z.val := by
    rw [← maskFacts.1 z]
    have hsub : ∀ x ∈ ex (mz z.val) gates init, x &&& mz z.val = x := ex_sub (mz z.val) hinit_sub
    have hsub' := getD_mem (S := {x | x &&& mz z.val = x}) hsub (by simp) out
    apply Nat.eq_of_testBit_eq; intro k
    have e1 := congrArg (fun x => x.testBit k) hsub'
    simp only [Nat.testBit_and] at e1
    rw [← e1, Nat.testBit_and]
    cases hk : (mz z.val).testBit k with
    | false => simp
    | true =>
      simp only [Bool.and_true]
      rw [← getD_map, ex_bit (mz z.val) hk gates init hD, hinit_bits k hk]
      have row_same : (fun i : Fin 7 => if z.val.testBit i.val then false else row k i) = row k := by
        funext i
        cases hi : z.val.testBit i.val with
        | false => rfl
        | true =>
          have off := congrArg (fun m : Nat => m.testBit k) (maskFacts.2 z i hi)
          simp only [Nat.testBit_and,hk,Bool.and_true,Nat.zero_testBit] at off
          exact off.symm
      have h := hf (row k)
      unfold pinned at h
      rw [row_same] at h
      change (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn (row k))).getD out false = f (row k) at h
      rw [h]
      exact (f_bit k).symm
  exact ex_sol (mz z.val) gates init (C (mz z.val) (WZ [] z.val))
    hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl))
    hD ⟨out, hout⟩
theorem fromAnchor (z : Fin 128) (L s : Nat) (h : (z.val,L) ∈ ac4)
    (c : HasCircuitSize 7 (pinned z) s) : L ≤ s := by
  obtain ⟨D,legal,size,correct⟩ := c
  by_contra! small
  exact ai4 _ h D.size (by omega) (bridgePinned z D legal correct)
end Seven11224.Atlas

namespace Seven11224.Atlas
set_option maxRecDepth 32768
set_option maxHeartbeats 0
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_11223 PEqualNP.Outside.L_meta_7398_aux
def bits (r : Nat) (i : Fin 7) := r.testBit i.val
def costData : Array (Nat) := #[11,8,9,5,10,7,7,4,7,5,6,2,6,4,5,1,8,5,7,4,7,4,5,2,5,3,4,1,4,1,2,0,8,5,6,3,7,4,5,2,6,4,5,2,5,2,4,1,5,2,5,2,4,1,4,1,2,1,2,1,1,0,1,0,6,4,5,1,6,4,5,1,3,2,2,0,3,2,2,0,5,2,4,1,5,2,4,1,2,1,1,0,2,1,1,0,4,1,2,0,4,1,2,0,2,1,1,0,2,1,1,0,1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0]
def cost (z : Fin 128) : Nat := costData[z.val]?.getD (0)
def candidateData : Array (Circuit) := #[⟨[⟨.or,[0,2]⟩,⟨.or,[0,1]⟩,⟨.or,[0,5]⟩,⟨.or,[4,5]⟩,⟨.or,[7,4]⟩,⟨.or,[9,6]⟩,⟨.and,[8,10]⟩,⟨.and,[3,12]⟩,⟨.and,[11,6]⟩,⟨.or,[13,14]⟩,⟨.or,[16,15]⟩],17⟩,⟨[⟨.or,[2,4]⟩,⟨.or,[5,6]⟩,⟨.or,[4,5]⟩,⟨.and,[1,9]⟩,⟨.and,[3,8]⟩,⟨.and,[7,6]⟩,⟨.or,[10,11]⟩,⟨.or,[13,12]⟩],14⟩,⟨[⟨.or,[0,3]⟩,⟨.or,[5,6]⟩,⟨.or,[3,4]⟩,⟨.or,[2,9]⟩,⟨.and,[7,8]⟩,⟨.and,[10,6]⟩,⟨.and,[0,9]⟩,⟨.or,[11,12]⟩,⟨.or,[14,13]⟩],15⟩,⟨[⟨.or,[2,4]⟩,⟨.or,[5,6]⟩,⟨.and,[3,8]⟩,⟨.and,[7,6]⟩,⟨.or,[9,10]⟩],11⟩,⟨[⟨.or,[0,1]⟩,⟨.or,[0,5]⟩,⟨.or,[0,4]⟩,⟨.or,[4,5]⟩,⟨.or,[8,6]⟩,⟨.and,[7,10]⟩,⟨.and,[3,11]⟩,⟨.and,[9,6]⟩,⟨.or,[12,13]⟩,⟨.or,[15,14]⟩],16⟩,⟨[⟨.or,[5,6]⟩,⟨.or,[4,5]⟩,⟨.and,[1,8]⟩,⟨.and,[3,7]⟩,⟨.and,[4,6]⟩,⟨.or,[9,10]⟩,⟨.or,[12,11]⟩],13⟩,⟨[⟨.or,[0,3]⟩,⟨.or,[5,6]⟩,⟨.or,[0,6]⟩,⟨.or,[3,4]⟩,⟨.and,[7,8]⟩,⟨.and,[10,9]⟩,⟨.or,[11,12]⟩],13⟩,⟨[⟨.or,[5,6]⟩,⟨.and,[3,7]⟩,⟨.and,[4,6]⟩,⟨.or,[8,9]⟩],10⟩,⟨[⟨.or,[0,2]⟩,⟨.or,[0,1]⟩,⟨.or,[4,5]⟩,⟨.or,[7,4]⟩,⟨.and,[8,9]⟩,⟨.and,[10,6]⟩,⟨.or,[11,12]⟩],13⟩,⟨[⟨.or,[2,4]⟩,⟨.or,[4,5]⟩,⟨.and,[1,8]⟩,⟨.and,[7,6]⟩,⟨.or,[9,10]⟩],11⟩,⟨[⟨.or,[2,4]⟩,⟨.or,[4,5]⟩,⟨.or,[8,6]⟩,⟨.and,[0,9]⟩,⟨.and,[7,6]⟩,⟨.or,[10,11]⟩],12⟩,⟨[⟨.or,[2,4]⟩,⟨.and,[7,6]⟩],8⟩,⟨[⟨.or,[0,1]⟩,⟨.or,[0,4]⟩,⟨.or,[4,5]⟩,⟨.and,[7,9]⟩,⟨.and,[8,6]⟩,⟨.or,[10,11]⟩],12⟩,⟨[⟨.or,[4,5]⟩,⟨.and,[1,7]⟩,⟨.and,[4,6]⟩,⟨.or,[8,9]⟩],10⟩,⟨[⟨.or,[0,4]⟩,⟨.or,[4,5]⟩,⟨.and,[7,6]⟩,⟨.and,[0,8]⟩,⟨.or,[9,10]⟩],11⟩,⟨[⟨.and,[4,6]⟩],7⟩,⟨[⟨.or,[0,3]⟩,⟨.or,[2,7]⟩,⟨.or,[1,7]⟩,⟨.and,[9,5]⟩,⟨.and,[8,6]⟩,⟨.and,[0,3]⟩,⟨.or,[10,11]⟩,⟨.or,[13,12]⟩],14⟩,⟨[⟨.or,[2,3]⟩,⟨.or,[1,3]⟩,⟨.and,[8,5]⟩,⟨.and,[7,6]⟩,⟨.or,[9,10]⟩],11⟩,⟨[⟨.or,[0,3]⟩,⟨.or,[2,7]⟩,⟨.and,[8,6]⟩,⟨.and,[7,5]⟩,⟨.and,[0,3]⟩,⟨.or,[9,10]⟩,⟨.or,[12,11]⟩],13⟩,⟨[⟨.or,[5,6]⟩,⟨.and,[3,7]⟩,⟨.and,[2,6]⟩,⟨.or,[8,9]⟩],10⟩,⟨[⟨.or,[0,3]⟩,⟨.or,[1,7]⟩,⟨.and,[8,5]⟩,⟨.and,[7,6]⟩,⟨.and,[0,3]⟩,⟨.or,[9,10]⟩,⟨.or,[12,11]⟩],13⟩,⟨[⟨.or,[1,3]⟩,⟨.and,[7,5]⟩,⟨.and,[3,6]⟩,⟨.or,[8,9]⟩],10⟩,⟨[⟨.or,[0,3]⟩,⟨.or,[5,6]⟩,⟨.and,[7,8]⟩,⟨.and,[0,3]⟩,⟨.or,[9,10]⟩],11⟩,⟨[⟨.or,[5,6]⟩,⟨.and,[3,7]⟩],8⟩,⟨[⟨.or,[0,2]⟩,⟨.or,[0,1]⟩,⟨.and,[8,5]⟩,⟨.and,[7,6]⟩,⟨.or,[9,10]⟩],11⟩,⟨[⟨.and,[1,5]⟩,⟨.and,[2,6]⟩,⟨.or,[7,8]⟩],9⟩,⟨[⟨.or,[5,6]⟩,⟨.and,[0,7]⟩,⟨.and,[2,6]⟩,⟨.or,[8,9]⟩],10⟩,⟨[⟨.and,[2,6]⟩],7⟩,⟨[⟨.or,[0,1]⟩,⟨.and,[7,5]⟩,⟨.and,[0,6]⟩,⟨.or,[8,9]⟩],10⟩,⟨[⟨.and,[1,5]⟩],7⟩,⟨[⟨.or,[5,6]⟩,⟨.and,[0,7]⟩],8⟩,⟨[],7⟩,⟨[⟨.or,[0,2]⟩,⟨.or,[0,6]⟩,⟨.or,[1,8]⟩,⟨.and,[4,9]⟩,⟨.and,[3,8]⟩,⟨.and,[7,6]⟩,⟨.or,[10,11]⟩,⟨.or,[13,12]⟩],14⟩,⟨[⟨.or,[2,3]⟩,⟨.or,[1,6]⟩,⟨.and,[4,8]⟩,⟨.and,[7,6]⟩,⟨.or,[9,10]⟩],11⟩,⟨[⟨.or,[0,2]⟩,⟨.or,[0,6]⟩,⟨.or,[3,4]⟩,⟨.and,[9,8]⟩,⟨.and,[7,6]⟩,⟨.or,[10,11]⟩],12⟩,⟨[⟨.or,[2,3]⟩,⟨.or,[7,4]⟩,⟨.and,[8,6]⟩],9⟩,⟨[⟨.or,[0,6]⟩,⟨.or,[1,7]⟩,⟨.and,[4,8]⟩,⟨.and,[3,7]⟩,⟨.and,[0,6]⟩,⟨.or,[9,10]⟩,⟨.or,[12,11]⟩],13⟩,⟨[⟨.or,[1,6]⟩,⟨.and,[4,7]⟩,⟨.and,[3,6]⟩,⟨.or,[8,9]⟩],10⟩,⟨[⟨.or,[0,6]⟩,⟨.or,[3,4]⟩,⟨.and,[8,7]⟩,⟨.and,[0,6]⟩,⟨.or,[9,10]⟩],11⟩,⟨[⟨.or,[3,4]⟩,⟨.and,[7,6]⟩],8⟩,⟨[⟨.or,[0,2]⟩,⟨.or,[0,1]⟩,⟨.or,[8,6]⟩,⟨.and,[4,9]⟩,⟨.and,[7,6]⟩,⟨.or,[10,11]⟩],12⟩,⟨[⟨.or,[1,6]⟩,⟨.and,[4,7]⟩,⟨.and,[2,6]⟩,⟨.or,[8,9]⟩],10⟩,⟨[⟨.or,[0,2]⟩,⟨.or,[0,6]⟩,⟨.and,[4,8]⟩,⟨.and,[7,6]⟩,⟨.or,[9,10]⟩],11⟩,⟨[⟨.or,[2,4]⟩,⟨.and,[7,6]⟩],8⟩,⟨[⟨.or,[0,1]⟩,⟨.or,[0,4]⟩,⟨.and,[8,6]⟩,⟨.and,[7,4]⟩,⟨.or,[9,10]⟩],11⟩,⟨[⟨.or,[1,6]⟩,⟨.and,[4,7]⟩],8⟩,⟨[⟨.or,[0,6]⟩,⟨.and,[4,7]⟩,⟨.and,[0,6]⟩,⟨.or,[8,9]⟩],10⟩,⟨[⟨.and,[4,6]⟩],7⟩,⟨[⟨.or,[0,2]⟩,⟨.or,[0,6]⟩,⟨.and,[3,8]⟩,⟨.and,[7,6]⟩,⟨.or,[9,10]⟩],11⟩,⟨[⟨.or,[2,3]⟩,⟨.and,[7,6]⟩],8⟩,⟨[⟨.or,[0,2]⟩,⟨.or,[0,6]⟩,⟨.and,[3,8]⟩,⟨.and,[7,6]⟩,⟨.or,[9,10]⟩],11⟩,⟨[⟨.or,[2,3]⟩,⟨.and,[7,6]⟩],8⟩,⟨[⟨.or,[0,6]⟩,⟨.and,[3,7]⟩,⟨.and,[0,6]⟩,⟨.or,[8,9]⟩],10⟩,⟨[⟨.and,[3,6]⟩],7⟩,⟨[⟨.or,[0,6]⟩,⟨.and,[3,7]⟩,⟨.and,[0,6]⟩,⟨.or,[8,9]⟩],10⟩,⟨[⟨.and,[3,6]⟩],7⟩,⟨[⟨.or,[0,2]⟩,⟨.and,[7,6]⟩],8⟩,⟨[⟨.and,[2,6]⟩],7⟩,⟨[⟨.or,[0,2]⟩,⟨.and,[7,6]⟩],8⟩,⟨[⟨.and,[2,6]⟩],7⟩,⟨[⟨.and,[0,6]⟩],7⟩,⟨[],7⟩,⟨[⟨.and,[0,6]⟩],7⟩,⟨[],7⟩,⟨[⟨.or,[0,1]⟩,⟨.or,[0,5]⟩,⟨.or,[4,5]⟩,⟨.and,[7,9]⟩,⟨.and,[3,8]⟩,⟨.or,[10,11]⟩],12⟩,⟨[⟨.or,[4,5]⟩,⟨.and,[1,7]⟩,⟨.and,[3,5]⟩,⟨.or,[8,9]⟩],10⟩,⟨[⟨.or,[0,3]⟩,⟨.or,[3,4]⟩,⟨.and,[7,5]⟩,⟨.and,[0,8]⟩,⟨.or,[9,10]⟩],11⟩,⟨[⟨.and,[3,5]⟩],7⟩,⟨[⟨.or,[0,1]⟩,⟨.or,[0,5]⟩,⟨.or,[4,5]⟩,⟨.and,[7,9]⟩,⟨.and,[3,8]⟩,⟨.or,[10,11]⟩],12⟩,⟨[⟨.or,[4,5]⟩,⟨.and,[1,7]⟩,⟨.and,[3,5]⟩,⟨.or,[8,9]⟩],10⟩,⟨[⟨.or,[0,3]⟩,⟨.or,[3,4]⟩,⟨.and,[7,5]⟩,⟨.and,[0,8]⟩,⟨.or,[9,10]⟩],11⟩,⟨[⟨.and,[3,5]⟩],7⟩,⟨[⟨.or,[0,1]⟩,⟨.or,[4,5]⟩,⟨.and,[7,8]⟩],9⟩,⟨[⟨.or,[4,5]⟩,⟨.and,[1,7]⟩],8⟩,⟨[⟨.or,[4,5]⟩,⟨.and,[0,7]⟩],8⟩,⟨[],7⟩,⟨[⟨.or,[0,1]⟩,⟨.or,[4,5]⟩,⟨.and,[7,8]⟩],9⟩,⟨[⟨.or,[4,5]⟩,⟨.and,[1,7]⟩],8⟩,⟨[⟨.or,[4,5]⟩,⟨.and,[0,7]⟩],8⟩,⟨[],7⟩,⟨[⟨.or,[0,1]⟩,⟨.or,[0,5]⟩,⟨.and,[3,8]⟩,⟨.and,[7,5]⟩,⟨.or,[9,10]⟩],11⟩,⟨[⟨.or,[1,3]⟩,⟨.and,[7,5]⟩],8⟩,⟨[⟨.or,[0,5]⟩,⟨.and,[3,7]⟩,⟨.and,[0,5]⟩,⟨.or,[8,9]⟩],10⟩,⟨[⟨.and,[3,5]⟩],7⟩,⟨[⟨.or,[0,1]⟩,⟨.or,[0,5]⟩,⟨.and,[3,8]⟩,⟨.and,[7,5]⟩,⟨.or,[9,10]⟩],11⟩,⟨[⟨.or,[1,3]⟩,⟨.and,[7,5]⟩],8⟩,⟨[⟨.or,[0,5]⟩,⟨.and,[3,7]⟩,⟨.and,[0,5]⟩,⟨.or,[8,9]⟩],10⟩,⟨[⟨.and,[3,5]⟩],7⟩,⟨[⟨.or,[0,1]⟩,⟨.and,[7,5]⟩],8⟩,⟨[⟨.and,[1,5]⟩],7⟩,⟨[⟨.and,[0,5]⟩],7⟩,⟨[],7⟩,⟨[⟨.or,[0,1]⟩,⟨.and,[7,5]⟩],8⟩,⟨[⟨.and,[1,5]⟩],7⟩,⟨[⟨.and,[0,5]⟩],7⟩,⟨[],7⟩,⟨[⟨.or,[3,4]⟩,⟨.and,[0,7]⟩,⟨.and,[1,4]⟩,⟨.or,[8,9]⟩],10⟩,⟨[⟨.and,[1,4]⟩],7⟩,⟨[⟨.or,[3,4]⟩,⟨.and,[0,7]⟩],8⟩,⟨[],7⟩,⟨[⟨.or,[3,4]⟩,⟨.and,[0,7]⟩,⟨.and,[1,4]⟩,⟨.or,[8,9]⟩],10⟩,⟨[⟨.and,[1,4]⟩],7⟩,⟨[⟨.or,[3,4]⟩,⟨.and,[0,7]⟩],8⟩,⟨[],7⟩,⟨[⟨.or,[0,1]⟩,⟨.and,[7,4]⟩],8⟩,⟨[⟨.and,[1,4]⟩],7⟩,⟨[⟨.and,[0,4]⟩],7⟩,⟨[],7⟩,⟨[⟨.or,[0,1]⟩,⟨.and,[7,4]⟩],8⟩,⟨[⟨.and,[1,4]⟩],7⟩,⟨[⟨.and,[0,4]⟩],7⟩,⟨[],7⟩,⟨[⟨.and,[0,3]⟩],7⟩,⟨[],7⟩,⟨[⟨.and,[0,3]⟩],7⟩,⟨[],7⟩,⟨[⟨.and,[0,3]⟩],7⟩,⟨[],7⟩,⟨[⟨.and,[0,3]⟩],7⟩,⟨[],7⟩,⟨[],7⟩,⟨[],7⟩,⟨[],7⟩,⟨[],7⟩,⟨[],7⟩,⟨[],7⟩,⟨[],7⟩,⟨[],7⟩]
def candidate (z : Fin 128) : Circuit := candidateData[z.val]?.getD (⟨[],7⟩)
def repData : Array (Fin 128) := #[0,1,2,0,4,5,6,7,8,0,10,0,12,7,14,0,16,0,18,7,18,7,22,0,0,0,7,0,7,0,0,0,32,0,34,0,18,7,22,0,10,7,14,0,14,0,46,0,14,0,14,0,46,0,46,0,0,0,0,0,0,0,0,0,12,7,14,0,12,7,14,0,0,0,0,0,0,0,0,0,14,0,46,0,14,0,46,0,0,0,0,0,0,0,0,0,7,0,0,0,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def rep (z : Fin 128) : Fin 128 := repData[z.val]?.getD (0)
def hasRepData : Array (Bool) := #[true,true,true,false,true,true,true,true,true,false,true,false,true,true,true,false,true,false,true,true,true,true,true,false,false,false,true,false,true,false,false,false,true,false,true,false,true,true,true,false,true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,false,false,false,false,false,false,true,true,true,false,true,true,true,false,false,false,false,false,false,false,false,false,true,false,true,false,true,false,true,false,false,false,false,false,false,false,false,false,true,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]
def hasRep (z : Fin 128) : Bool := hasRepData[z.val]?.getD (false)
def renameListData : Array (List (Fin 7)) := #[[0,1,2,3,4,5,6],[0,1,2,3,4,5,6],[0,0,2,3,4,5,6],[0,0,0,0,0,0,0],[0,1,0,3,4,5,6],[0,1,0,3,4,5,6],[0,0,0,3,4,5,6],[0,0,0,3,4,5,6],[0,1,2,0,4,5,6],[0,0,0,0,0,0,0],[0,0,2,0,4,5,6],[0,0,0,0,0,0,0],[0,1,0,0,4,5,6],[0,3,0,0,6,5,4],[0,0,0,0,4,5,6],[0,0,0,0,0,0,0],[0,1,2,3,0,5,6],[0,0,0,0,0,0,0],[0,0,2,3,0,5,6],[0,0,4,3,0,5,6],[0,2,0,3,0,6,5],[0,5,0,6,0,3,4],[0,0,0,3,0,5,6],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[3,0,4,0,0,5,6],[0,0,0,0,0,0,0],[3,4,0,0,0,6,5],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,1,2,3,4,0,6],[0,0,0,0,0,0,0],[0,0,2,3,4,0,6],[0,0,0,0,0,0,0],[0,2,0,5,6,0,3],[0,5,0,4,3,0,6],[0,0,0,5,6,0,3],[0,0,0,0,0,0,0],[4,5,2,0,0,0,6],[0,5,4,0,3,0,6],[4,0,5,0,6,0,0],[0,0,0,0,0,0,0],[4,5,0,0,0,0,6],[0,0,0,0,0,0,0],[0,0,0,0,4,0,6],[0,0,0,0,0,0,0],[4,0,5,6,0,0,0],[0,0,0,0,0,0,0],[4,0,5,6,0,0,0],[0,0,0,0,0,0,0],[0,0,0,4,0,0,6],[0,0,0,0,0,0,0],[0,0,0,4,0,0,6],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,1,0,6,5,4,0],[0,3,0,4,5,6,0],[0,0,0,4,5,6,0],[0,0,0,0,0,0,0],[0,1,0,6,5,4,0],[0,3,0,4,5,6,0],[0,0,0,4,5,6,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[4,5,0,6,0,0,0],[0,0,0,0,0,0,0],[0,0,0,4,0,6,0],[0,0,0,0,0,0,0],[4,5,0,6,0,0,0],[0,0,0,0,0,0,0],[0,0,0,4,0,6,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[3,4,0,5,6,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[3,4,0,5,6,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0]]
def renameList (z : Fin 128) : List (Fin 7) := renameListData[z.val]?.getD ([])
def activeRawData : Array (List (Fin 7)) := #[[0,1,2,3,4,5,6],[1,2,3,4,5,6],[0,2,3,4,5,6],[2,3,4,5,6],[0,1,3,4,5,6],[1,3,4,5,6],[0,3,4,5,6],[3,4,5,6],[0,1,2,4,5,6],[1,2,4,5,6],[0,2,4,5,6],[2,4,6],[0,1,4,5,6],[1,4,5,6],[0,4,5,6],[4,6],[0,1,2,3,5,6],[1,2,3,5,6],[0,2,3,5,6],[2,3,5,6],[0,1,3,5,6],[1,3,5,6],[0,3,5,6],[3,5,6],[0,1,2,5,6],[1,2,5,6],[0,2,5,6],[2,6],[0,1,5,6],[1,5],[0,5,6],[],[0,1,2,3,4,6],[1,2,3,4,6],[0,2,3,4,6],[2,3,4,6],[0,1,3,4,6],[1,3,4,6],[0,3,4,6],[3,4,6],[0,1,2,4,6],[1,2,4,6],[0,2,4,6],[2,4,6],[0,1,4,6],[1,4,6],[0,4,6],[4,6],[0,2,3,6],[2,3,6],[0,2,3,6],[2,3,6],[0,3,6],[3,6],[0,3,6],[3,6],[0,2,6],[2,6],[0,2,6],[2,6],[0,6],[],[0,6],[],[0,1,3,4,5],[1,3,4,5],[0,3,4,5],[3,5],[0,1,3,4,5],[1,3,4,5],[0,3,4,5],[3,5],[0,1,4,5],[1,4,5],[0,4,5],[],[0,1,4,5],[1,4,5],[0,4,5],[],[0,1,3,5],[1,3,5],[0,3,5],[3,5],[0,1,3,5],[1,3,5],[0,3,5],[3,5],[0,1,5],[1,5],[0,5],[],[0,1,5],[1,5],[0,5],[],[0,1,3,4],[1,4],[0,3,4],[],[0,1,3,4],[1,4],[0,3,4],[],[0,1,4],[1,4],[0,4],[],[0,1,4],[1,4],[0,4],[],[0,3],[],[0,3],[],[0,3],[],[0,3],[],[],[],[],[],[],[],[],[]]
def activeRaw (z : Fin 128) : List (Fin 7) := activeRawData[z.val]?.getD ([])
def probesData : Array (List Nat) := #[[8,16,64,1,1,1,1],[0,16,64,32,2,2,4],[8,0,64,1,1,1,1],[0,0,64,32,64,8,4],[8,16,0,1,1,1,1],[0,16,0,32,2,2,8],[8,0,0,1,1,1,1],[0,0,0,32,64,8,8],[16,16,64,0,1,1,1],[0,16,64,0,2,2,4],[16,0,64,0,1,1,1],[0,0,64,0,64,0,4],[16,16,0,0,1,1,1],[0,16,0,0,2,2,16],[16,0,0,0,1,1,1],[0,0,0,0,64,0,16],[8,32,64,1,0,1,1],[0,32,64,32,0,2,4],[8,0,64,1,0,1,1],[0,0,64,32,0,8,4],[8,32,0,1,0,1,1],[0,32,0,32,0,2,8],[8,0,0,1,0,1,1],[0,0,0,32,0,8,8],[32,32,64,0,0,1,1],[0,32,64,0,0,2,4],[32,0,64,0,0,1,1],[0,0,64,0,0,0,4],[32,32,0,0,0,1,1],[0,32,0,0,0,2,0],[32,0,0,0,0,1,1],[0,0,0,0,0,0,0],[8,16,64,1,1,0,1],[0,16,64,64,2,0,4],[8,0,64,1,1,0,1],[0,0,64,64,64,0,4],[8,16,0,1,1,0,1],[0,16,0,64,2,0,8],[8,0,0,1,1,0,1],[0,0,0,64,64,0,8],[16,16,64,0,1,0,1],[0,16,64,0,2,0,4],[16,0,64,0,1,0,1],[0,0,64,0,64,0,4],[16,16,0,0,1,0,1],[0,16,0,0,2,0,16],[16,0,0,0,1,0,1],[0,0,0,0,64,0,16],[8,0,64,1,0,0,1],[0,0,64,64,0,0,4],[8,0,64,1,0,0,1],[0,0,64,64,0,0,4],[8,0,0,1,0,0,1],[0,0,0,64,0,0,8],[8,0,0,1,0,0,1],[0,0,0,64,0,0,8],[64,0,64,0,0,0,1],[0,0,64,0,0,0,4],[64,0,64,0,0,0,1],[0,0,64,0,0,0,4],[64,0,0,0,0,0,1],[0,0,0,0,0,0,0],[64,0,0,0,0,0,1],[0,0,0,0,0,0,0],[8,16,0,1,1,1,0],[0,16,0,32,2,2,0],[8,0,0,1,1,1,0],[0,0,0,32,0,8,0],[8,16,0,1,1,1,0],[0,16,0,32,2,2,0],[8,0,0,1,1,1,0],[0,0,0,32,0,8,0],[16,16,0,0,1,1,0],[0,16,0,0,2,2,0],[16,0,0,0,1,1,0],[0,0,0,0,0,0,0],[16,16,0,0,1,1,0],[0,16,0,0,2,2,0],[16,0,0,0,1,1,0],[0,0,0,0,0,0,0],[8,32,0,1,0,1,0],[0,32,0,32,0,2,0],[8,0,0,1,0,1,0],[0,0,0,32,0,8,0],[8,32,0,1,0,1,0],[0,32,0,32,0,2,0],[8,0,0,1,0,1,0],[0,0,0,32,0,8,0],[32,32,0,0,0,1,0],[0,32,0,0,0,2,0],[32,0,0,0,0,1,0],[0,0,0,0,0,0,0],[32,32,0,0,0,1,0],[0,32,0,0,0,2,0],[32,0,0,0,0,1,0],[0,0,0,0,0,0,0],[8,16,0,1,1,0,0],[0,16,0,0,2,0,0],[8,0,0,1,1,0,0],[0,0,0,0,0,0,0],[8,16,0,1,1,0,0],[0,16,0,0,2,0,0],[8,0,0,1,1,0,0],[0,0,0,0,0,0,0],[16,16,0,0,1,0,0],[0,16,0,0,2,0,0],[16,0,0,0,1,0,0],[0,0,0,0,0,0,0],[16,16,0,0,1,0,0],[0,16,0,0,2,0,0],[16,0,0,0,1,0,0],[0,0,0,0,0,0,0],[8,0,0,1,0,0,0],[0,0,0,0,0,0,0],[8,0,0,1,0,0,0],[0,0,0,0,0,0,0],[8,0,0,1,0,0,0],[0,0,0,0,0,0,0],[8,0,0,1,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[0,0,0,0,0,0,0]]
def probes (z : Fin 128) : List Nat := probesData[z.val]?.getD ([])
def wireMap (z : Fin 128) (i : Fin 7) := (renameList z).getD i.val 0
def active (z : Fin 128) : Finset (Fin 7) := (activeRaw z).toFinset
def legalGate (g : Gate) := match g.op with
  | .and | .or => decide (g.inputs.length≤2)
  | _ => false
theorem validGate {g : Gate} (h : legalGate g=true) : (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by
  obtain ⟨o,ws⟩ := g
  cases o <;> simp_all [legalGate]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem repFacts : ∀ z : Fin 128, hasRep z=true →
    ((rep z=0 ∧ cost z=11) ∨ ((rep z).val,cost z) ∈ ac4) ∧
      ∀ x : Fin 7 → Bool, pinned z (x ∘ wireMap z)=pinned (rep z) x := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem activeFacts : ∀ (z : Fin 128) (i : Fin 7), i∈active z →
    let x := bits ((probes z).getD i.val 0)
    pinned z (Function.update x i (!x i)) ≠ pinned z x := by decide +kernel
theorem repBound (z : Fin 128) (s : Nat) (h : hasRep z=true)
    (small : HasCircuitSize 7 (pinned z) s) : cost z ≤ s := by
  obtain ⟨row,evals⟩ := repFacts z h
  have r := yn (wireMap z) (pinned z) s small
  have eq : (fun x => pinned z (x ∘ wireMap z))=pinned (rep z) := funext evals
  rw [eq] at r
  rcases row with ⟨root,price⟩ | mem
  · rw [root] at r
    have rt : pinned 0 = Seven11224.target := by funext x; exact (dec_f x).symm
    rw [rt] at r
    rw [price]
    exact (Seven11224.exact_budget s).mp r
  · exact fromAnchor _ _ _ mem r
theorem activeBound (z : Fin 128) (s : Nat) (small : HasCircuitSize 7 (pinned z) s) :
    (active z).card ≤ s+1 :=
  q117 7 (pinned z) (active z) (fun i h => ⟨_,activeFacts z i h⟩) s small
theorem extra3 (s : Nat) (small : HasCircuitSize 7 (pinned 3) s) : cost 3 ≤ s := by
  obtain ⟨t,save,base⟩ := q70 6 (pinned 3) 2 false s ⟨bits 64,by decide +kernel⟩
    ⟨bits 0,bits 40,by decide +kernel⟩ small
  let π : Fin 7 → Fin 7 := ![0,0,0,0,4,4,6]
  have changeGraph := yn π (fun x => pinned 3 (Function.update x 2 false)) t base
  have eq : (fun x : Fin 7 → Bool => pinned 3 (Function.update (x ∘ π) 2 false))=pinned 46 := by
    funext x; revert x; decide +kernel
  change HasCircuitSize 7 (fun x => pinned 3 (Function.update (x ∘ π) 2 false)) t at changeGraph
  rw [eq] at changeGraph
  have bound := fromAnchor 46 4 t (by decide +kernel) changeGraph
  change 5 ≤ s
  omega
theorem extra9 (s : Nat) (small : HasCircuitSize 7 (pinned 9) s) : cost 9 ≤ s := by
  obtain ⟨t,save,base⟩ := q70 6 (pinned 9) 5 false s ⟨bits 2,by decide +kernel⟩
    ⟨bits 0,bits 18,by decide +kernel⟩ small
  let π : Fin 7 → Fin 7 := ![0,0,0,0,4,0,6]
  have changeGraph := yn π (fun x => pinned 9 (Function.update x 5 false)) t base
  have eq : (fun x : Fin 7 → Bool => pinned 9 (Function.update (x ∘ π) 5 false))=pinned 46 := by
    funext x; revert x; decide +kernel
  change HasCircuitSize 7 (fun x => pinned 9 (Function.update (x ∘ π) 5 false)) t at changeGraph
  rw [eq] at changeGraph
  have bound := fromAnchor 46 4 t (by decide +kernel) changeGraph
  change 5 ≤ s
  omega
theorem extra17 (s : Nat) (small : HasCircuitSize 7 (pinned 17) s) : cost 17 ≤ s := by
  obtain ⟨t,save,base⟩ := q70 6 (pinned 17) 1 false s ⟨bits 32,by decide +kernel⟩
    ⟨bits 0,bits 40,by decide +kernel⟩ small
  let π : Fin 7 → Fin 7 := ![0,0,0,4,0,0,6]
  have changeGraph := yn π (fun x => pinned 17 (Function.update x 1 false)) t base
  have eq : (fun x : Fin 7 → Bool => pinned 17 (Function.update (x ∘ π) 1 false))=pinned 46 := by
    funext x; revert x; decide +kernel
  change HasCircuitSize 7 (fun x => pinned 17 (Function.update (x ∘ π) 1 false)) t at changeGraph
  rw [eq] at changeGraph
  have bound := fromAnchor 46 4 t (by decide +kernel) changeGraph
  change 5 ≤ s
  omega
theorem extra24 (s : Nat) (small : HasCircuitSize 7 (pinned 24) s) : cost 24 ≤ s := by
  obtain ⟨t,save,base⟩ := q70 6 (pinned 24) 1 false s ⟨bits 32,by decide +kernel⟩
    ⟨bits 0,bits 33,by decide +kernel⟩ small
  let π : Fin 7 → Fin 7 := ![0,0,4,0,0,4,6]
  have changeGraph := yn π (fun x => pinned 24 (Function.update x 1 false)) t base
  have eq : (fun x : Fin 7 → Bool => pinned 24 (Function.update (x ∘ π) 1 false))=pinned 46 := by
    funext x; revert x; decide +kernel
  change HasCircuitSize 7 (fun x => pinned 24 (Function.update (x ∘ π) 1 false)) t at changeGraph
  rw [eq] at changeGraph
  have bound := fromAnchor 46 4 t (by decide +kernel) changeGraph
  change 5 ≤ s
  omega
theorem extra33 (s : Nat) (small : HasCircuitSize 7 (pinned 33) s) : cost 33 ≤ s := by
  obtain ⟨t,save,base⟩ := q70 6 (pinned 33) 2 false s ⟨bits 64,by decide +kernel⟩
    ⟨bits 0,bits 18,by decide +kernel⟩ small
  let π : Fin 7 → Fin 7 := ![0,0,0,0,4,0,6]
  have changeGraph := yn π (fun x => pinned 33 (Function.update x 2 false)) t base
  have eq : (fun x : Fin 7 → Bool => pinned 33 (Function.update (x ∘ π) 2 false))=pinned 46 := by
    funext x; revert x; decide +kernel
  change HasCircuitSize 7 (fun x => pinned 33 (Function.update (x ∘ π) 2 false)) t at changeGraph
  rw [eq] at changeGraph
  have bound := fromAnchor 46 4 t (by decide +kernel) changeGraph
  change 5 ≤ s
  omega
theorem cases_remaining : ∀ z : Fin 128, hasRep z=false →
    cost z ≤ (active z).card-1 ∨ z=3 ∨ z=9 ∨ z=17 ∨ z=24 ∨ z=33 := by decide +kernel
theorem lower (z : Fin 128) (s : Nat) (small : HasCircuitSize 7 (pinned z) s) : cost z ≤ s := by
  cases h : hasRep z with
  | true => exact repBound z s h small
  | false =>
    rcases cases_remaining z h with cheap|rfl|rfl|rfl|rfl|rfl
    · have lb := activeBound z s small; omega
    · exact extra3 s small
    · exact extra9 s small
    · exact extra17 s small
    · exact extra24 s small
    · exact extra33 s small

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem witnesses : ∀ z : Fin 128, (candidate z).size=cost z ∧
    ((candidate z).gates.all legalGate)=true ∧ ∀ x : Fin 7 → Bool, (candidate z).eval (List.ofFn x)=pinned z x := by decide +kernel
theorem bounds (z : Fin 128) (s : Nat) : HasCircuitSize 7 (pinned z) s ↔ cost z ≤ s := by
  constructor
  · exact lower z s
  · intro enough
    have ⟨size,good,computed⟩ := witnesses z
    refine ⟨candidate z,?_,size.le.trans enough,computed⟩
    intro g hg
    obtain ⟨op,n⟩ := validGate (List.all_eq_true.mp good g hg)
    rcases op with a|b
    · exact ⟨by simp [a],n⟩
    · exact ⟨by simp [b],n⟩
end Seven11224.Atlas

namespace Seven11224.Readers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3223 Seven11224.Atlas
def mask : Fin 7 → Fin 128 := ![1,2,4,8,16,32,64]
def projection (v : Fin 7) : List (Option (Fin 7)) := List.ofFn (fun i : Fin 7 => if i=v then none else some i)
def uses (v : Fin 7) (g : Gate) := decide (v.val∈g.inputs)
def correct (C : Circuit) := ∀ x : Fin 7 → Bool, C.eval (List.ofFn x)=Seven11224.target x
set_option maxHeartbeats 0 in
theorem projList : ∀ (v : Fin 7) (x : Fin 7 → Bool), proj (projection v) x = List.ofFn (Function.update x v false) := by decide +kernel
set_option maxHeartbeats 0 in
theorem projFun : ∀ (v : Fin 7) (x : Fin 7 → Bool), Seven11224.target (Function.update x v false)=pinned (mask v) x := by
  decide +kernel
theorem projected (C : Circuit) (v : Fin 7) (hc : correct C) (x : Fin 7 → Bool) :
    C.eval (proj (projection v) x)=pinned (mask v) x := by rw [projList,hc,projFun]
theorem changing (C : Circuit) (v : Fin 7) (hc : correct C) :
    ∃ x y, C.eval (proj (projection v) x) ≠ C.eval (proj (projection v) y) := by
  have possible : ∀ i : Fin 7, ∃ r : Fin 128, pinned (mask i) (bits 0) ≠ pinned (mask i) (bits r.val) := by decide +kernel
  obtain ⟨r,h⟩ := possible v
  exact ⟨bits 0,bits r.val,by simpa only [projected C v hc] using h⟩
theorem count_pass (v : Fin 7) (m : Nat) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (ok : ∀ g ∈ gs, NOkGate g) (raw : v.val < acc.1.length)
    (tag2 : acc.1.getD v.val (.inl false) = .inl false) :
    (elimPass m gs acc).2.length + gs.countP (uses v) ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons]
    have tailBound := ih (elimStep m acc g) (fun h hh => ok _ (List.mem_cons_of_mem _ hh))
      (by simp [elimStep];omega) (by simp only [elimStep];rw [getD_snoc_ne _ _ _ _ (by omega)];exact tag2)
    set vals := g.inputs.map fun i => acc.1.getD i (.inl false) with hv
    set opt := (simplifyGate g.op (m + acc.2.length) vals).1 with ho
    have len : (elimStep m acc g).2.length = acc.2.length + opt.toList.length := by simp [elimStep,ho,hv]
    rw [len] at tailBound
    by_cases read : v.val∈g.inputs
    · have gok := ok g List.mem_cons_self
      have z : opt=none := simplifyGate_none_of_const _ _ _ gok.1.1 (by simpa [hv] using gok.1.2)
        (fun h => by simpa [hv] using gok.2 h) ⟨false,List.mem_map.mpr ⟨v.val,read,tag2⟩⟩
      rw [z] at tailBound
      simp [List.countP_cons,uses,read] at tailBound ⊢
      omega
    · have bound := toList_opt_len_le opt
      simp [List.countP_cons,uses,read] at tailBound ⊢
      omega


theorem per_input (C : Circuit) (legal : FanInTwo C) (hc : correct C) (v : Fin 7) :
    Seven11224.Atlas.cost (mask v) + (C.gates.map normGate).countP (uses v) ≤ C.size := by
  obtain ⟨D,df,ds,de⟩ := extract C (projection v) legal (changing C v hc)
  have lo := (bounds (mask v) D.size).mp ⟨D,df,le_rfl,fun x => (de x).trans (projected C v hc x)⟩
  have hlen : ∀ v : Fin 7, v.val < (start (projection v)).1.length := by decide +kernel
  have htag : ∀ v : Fin 7, (start (projection v)).1.getD v.val (.inl false)=.inl false := by decide +kernel
  have budget := count_pass v 7 (C.gates.map normGate) (start (projection v)) (by
    intro g hg; obtain ⟨g0,h0,rfl⟩ := List.mem_map.mp hg; exact normGate_nok g0 (legal g0 h0)) (hlen v) (htag v)
  change D.size = (elimPass 7 (C.gates.map normGate) (start (projection v))).2.length at ds
  have total : D.size + (C.gates.map normGate).countP (uses v) ≤ C.gates.length := by
    rw [ds]
    simpa only [start,List.length_nil,zero_add,List.length_map] using budget
  exact (Nat.add_le_add_right lo _).trans total
theorem sensitive_two (C : Circuit) (hc : correct C) :
    ∃ a b : List Bool, a.length=(projection 2).length ∧ b.length=(projection 2).length ∧
      (∀ i : Nat, i≠2 → a.getD i false=b.getD i false) ∧ C.eval a ≠ C.eval b := by
  refine ⟨List.ofFn (bits 64), List.ofFn (bits 68),rfl,rfl,?_,?_⟩
  · intro i hi
    by_cases h : i<7
    · interval_cases i <;> first | contradiction | decide
    · rw [List.getD_eq_default _ _ (by simp;omega), List.getD_eq_default _ _ (by simp;omega)]
  · rw [hc,hc];decide +kernel
theorem unique_or (C : Circuit) (legal : FanInTwo C) (hc : correct C) (small : C.size≤11) :
    (C.gates.map normGate).countP (uses 2)=1 ∧ ∃ g ∈ C.gates, g.op=.or ∧ 2∈g.inputs := by
  have base : Seven11224.Atlas.cost (mask 2)=10 := by decide +kernel
  have needed : ∃ g ∈ C.gates, g.op=.or ∧ 2∈g.inputs := by
    by_contra! h
    obtain ⟨D,df,ds,de⟩ := PEqualNP.Outside.L_meta_3223 7 C (projection 2) 2 1 legal (by decide) (by decide)
      (fun _ => h) (sensitive_two C hc) (changing C 2 hc)
    have lo := (bounds (mask 2) D.size).mp ⟨D,df,le_rfl,fun x => (de x).trans (projected C 2 hc x)⟩
    omega
  refine ⟨?_,needed⟩
  obtain ⟨g,hg,op,read⟩ := needed
  have fixed : normGate g=g := by cases g with | mk o ins => change o=.or at op; subst o; rfl
  have hit : g∈C.gates.map normGate := List.mem_map.mpr ⟨g,hg,fixed⟩
  have good : uses 2 g=true := by simpa [uses] using read
  have pos : 0 < (C.gates.map normGate).countP (uses 2) := List.countP_pos_iff.mpr ⟨g,hit,good⟩
  have budget := per_input C legal hc 2
  omega
end Seven11224.Readers

namespace Seven11224.High
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_11223 PEqualNP.Outside.L_meta_7398_aux
open Seven11224.Atlas
def cofactor (v : Fin 7) (t : Nat) (x : Fin 7 → Bool) :=
  f (Function.update (fun i => if t.testBit i.val then false else x i) v true)
def value (v : Fin 7) (x : Fin 7 → Bool) := f (Function.update x v true)
set_option maxRecDepth 32768
set_option maxHeartbeats 0
theorem low0 (s : Nat) (small : HasCircuitSize 7 (value 0) s) : 3 ≤ s := by
  have original : value 0=cofactor 0 0 := by funext x; revert x; decide +kernel
  rw [original] at small
  obtain ⟨s0,drop0,h0⟩ := q70 6 (cofactor 0 0) 3 false s
    ⟨bits 0,by decide +kernel⟩ ⟨bits 0,bits 16,by decide +kernel⟩ small
  have eq0 : (fun x => cofactor 0 0 (Function.update x 3 false))=cofactor 0 8 := by
    funext x; revert x; decide +kernel
  rw [eq0] at h0
  obtain ⟨s1,drop1,h1⟩ := q70 6 (cofactor 0 8) 4 false s0
    ⟨bits 0,by decide +kernel⟩ ⟨bits 0,bits 32,by decide +kernel⟩ h0
  have eq1 : (fun x => cofactor 0 8 (Function.update x 4 false))=cofactor 0 24 := by
    funext x; revert x; decide +kernel
  rw [eq1] at h1
  obtain ⟨s2,drop2,h2⟩ := q70 6 (cofactor 0 24) 5 false s1
    ⟨bits 0,by decide +kernel⟩ ⟨bits 0,bits 64,by decide +kernel⟩ h1
  have eq2 : (fun x => cofactor 0 24 (Function.update x 5 false))=cofactor 0 56 := by
    funext x; revert x; decide +kernel
  rw [eq2] at h2
  omega
theorem low1 (s : Nat) (small : HasCircuitSize 7 (value 1) s) : 7 ≤ s := by
  have original : value 1=cofactor 1 0 := by funext x; revert x; decide +kernel
  rw [original] at small
  obtain ⟨s0,drop0,h0⟩ := q70 6 (cofactor 1 0) 4 false s
    ⟨bits 0,by decide +kernel⟩ ⟨bits 0,bits 32,by decide +kernel⟩ small
  have eq0 : (fun x => cofactor 1 0 (Function.update x 4 false))=cofactor 1 16 := by
    funext x; revert x; decide +kernel
  rw [eq0] at h0
  obtain ⟨s1,drop1,h1⟩ := q70 6 (cofactor 1 16) 5 false s0
    ⟨bits 0,by decide +kernel⟩ ⟨bits 0,bits 9,by decide +kernel⟩ h0
  have eq1 : (fun x => cofactor 1 16 (Function.update x 5 false))=cofactor 1 48 := by
    funext x; revert x; decide +kernel
  rw [eq1] at h1
  have base : cofactor 1 48=pinned 50 := by funext x; revert x; decide +kernel
  rw [base] at h1
  have b := (Atlas.bounds 50 s1).mp h1
  change 5 ≤ s1 at b
  omega
theorem low2 (s : Nat) (small : HasCircuitSize 7 (value 2) s) : 7 ≤ s := by
  have original : value 2=cofactor 2 0 := by funext x; revert x; decide +kernel
  rw [original] at small
  obtain ⟨s0,drop0,h0⟩ := q70 6 (cofactor 2 0) 6 false s
    ⟨bits 0,by decide +kernel⟩ ⟨bits 0,bits 9,by decide +kernel⟩ small
  have eq0 : (fun x => cofactor 2 0 (Function.update x 6 false))=cofactor 2 64 := by
    funext x; revert x; decide +kernel
  rw [eq0] at h0
  have base : cofactor 2 64=pinned 68 := by funext x; revert x; decide +kernel
  rw [base] at h0
  have b := (Atlas.bounds 68 s0).mp h0
  change 6 ≤ s0 at b
  omega
theorem low3 (s : Nat) (small : HasCircuitSize 7 (value 3) s) : 4 ≤ s := by
  have original : value 3=cofactor 3 0 := by funext x; revert x; decide +kernel
  rw [original] at small
  obtain ⟨s0,drop0,h0⟩ := q70 6 (cofactor 3 0) 0 false s
    ⟨bits 0,by decide +kernel⟩ ⟨bits 0,bits 32,by decide +kernel⟩ small
  have eq0 : (fun x => cofactor 3 0 (Function.update x 0 false))=cofactor 3 1 := by
    funext x; revert x; decide +kernel
  rw [eq0] at h0
  obtain ⟨s1,drop1,h1⟩ := q70 6 (cofactor 3 1) 5 false s0
    ⟨bits 0,by decide +kernel⟩ ⟨bits 0,bits 64,by decide +kernel⟩ h0
  have eq1 : (fun x => cofactor 3 1 (Function.update x 5 false))=cofactor 3 33 := by
    funext x; revert x; decide +kernel
  rw [eq1] at h1
  obtain ⟨s2,drop2,h2⟩ := q70 6 (cofactor 3 33) 6 false s1
    ⟨bits 0,by decide +kernel⟩ ⟨bits 0,bits 18,by decide +kernel⟩ h1
  have eq2 : (fun x => cofactor 3 33 (Function.update x 6 false))=cofactor 3 97 := by
    funext x; revert x; decide +kernel
  rw [eq2] at h2
  have base : cofactor 3 97=pinned 105 := by funext x; revert x; decide +kernel
  rw [base] at h2
  have b := (Atlas.bounds 105 s2).mp h2
  change 1 ≤ s2 at b
  omega
theorem low4 (s : Nat) (small : HasCircuitSize 7 (value 4) s) : 4 ≤ s := by
  have original : value 4=cofactor 4 0 := by funext x; revert x; decide +kernel
  rw [original] at small
  obtain ⟨s0,drop0,h0⟩ := q70 6 (cofactor 4 0) 0 false s
    ⟨bits 0,by decide +kernel⟩ ⟨bits 0,bits 2,by decide +kernel⟩ small
  have eq0 : (fun x => cofactor 4 0 (Function.update x 0 false))=cofactor 4 1 := by
    funext x; revert x; decide +kernel
  rw [eq0] at h0
  obtain ⟨s1,drop1,h1⟩ := q70 6 (cofactor 4 1) 1 false s0
    ⟨bits 0,by decide +kernel⟩ ⟨bits 0,bits 64,by decide +kernel⟩ h0
  have eq1 : (fun x => cofactor 4 1 (Function.update x 1 false))=cofactor 4 3 := by
    funext x; revert x; decide +kernel
  rw [eq1] at h1
  obtain ⟨s2,drop2,h2⟩ := q70 6 (cofactor 4 3) 6 false s1
    ⟨bits 0,by decide +kernel⟩ ⟨bits 0,bits 40,by decide +kernel⟩ h1
  have eq2 : (fun x => cofactor 4 3 (Function.update x 6 false))=cofactor 4 67 := by
    funext x; revert x; decide +kernel
  rw [eq2] at h2
  have base : cofactor 4 67=pinned 83 := by funext x; revert x; decide +kernel
  rw [base] at h2
  have b := (Atlas.bounds 83 s2).mp h2
  change 1 ≤ s2 at b
  omega
theorem low5 (s : Nat) (small : HasCircuitSize 7 (value 5) s) : 5 ≤ s := by
  have original : value 5=cofactor 5 0 := by funext x; revert x; decide +kernel
  rw [original] at small
  obtain ⟨s0,drop0,h0⟩ := q70 6 (cofactor 5 0) 0 false s
    ⟨bits 0,by decide +kernel⟩ ⟨bits 0,bits 2,by decide +kernel⟩ small
  have eq0 : (fun x => cofactor 5 0 (Function.update x 0 false))=cofactor 5 1 := by
    funext x; revert x; decide +kernel
  rw [eq0] at h0
  obtain ⟨s1,drop1,h1⟩ := q70 6 (cofactor 5 1) 1 false s0
    ⟨bits 0,by decide +kernel⟩ ⟨bits 0,bits 8,by decide +kernel⟩ h0
  have eq1 : (fun x => cofactor 5 1 (Function.update x 1 false))=cofactor 5 3 := by
    funext x; revert x; decide +kernel
  rw [eq1] at h1
  obtain ⟨s2,drop2,h2⟩ := q70 6 (cofactor 5 3) 3 false s1
    ⟨bits 0,by decide +kernel⟩ ⟨bits 0,bits 68,by decide +kernel⟩ h1
  have eq2 : (fun x => cofactor 5 3 (Function.update x 3 false))=cofactor 5 11 := by
    funext x; revert x; decide +kernel
  rw [eq2] at h2
  have base : cofactor 5 11=pinned 43 := by funext x; revert x; decide +kernel
  rw [base] at h2
  have b := (Atlas.bounds 43 s2).mp h2
  change 2 ≤ s2 at b
  omega
theorem low6 (s : Nat) (small : HasCircuitSize 7 (value 6) s) : 5 ≤ s := by
  have original : value 6=cofactor 6 0 := by funext x; revert x; decide +kernel
  rw [original] at small
  obtain ⟨s0,drop0,h0⟩ := q70 6 (cofactor 6 0) 0 false s
    ⟨bits 0,by decide +kernel⟩ ⟨bits 0,bits 4,by decide +kernel⟩ small
  have eq0 : (fun x => cofactor 6 0 (Function.update x 0 false))=cofactor 6 1 := by
    funext x; revert x; decide +kernel
  rw [eq0] at h0
  obtain ⟨s1,drop1,h1⟩ := q70 6 (cofactor 6 1) 2 false s0
    ⟨bits 0,by decide +kernel⟩ ⟨bits 0,bits 8,by decide +kernel⟩ h0
  have eq1 : (fun x => cofactor 6 1 (Function.update x 2 false))=cofactor 6 5 := by
    funext x; revert x; decide +kernel
  rw [eq1] at h1
  obtain ⟨s2,drop2,h2⟩ := q70 6 (cofactor 6 5) 3 false s1
    ⟨bits 0,by decide +kernel⟩ ⟨bits 0,bits 16,by decide +kernel⟩ h1
  have eq2 : (fun x => cofactor 6 5 (Function.update x 3 false))=cofactor 6 13 := by
    funext x; revert x; decide +kernel
  rw [eq2] at h2
  obtain ⟨s3,drop3,h3⟩ := q70 6 (cofactor 6 13) 4 false s2
    ⟨bits 0,by decide +kernel⟩ ⟨bits 0,bits 34,by decide +kernel⟩ h2
  have eq3 : (fun x => cofactor 6 13 (Function.update x 4 false))=cofactor 6 29 := by
    funext x; revert x; decide +kernel
  rw [eq3] at h3
  have base : cofactor 6 29=pinned 93 := by funext x; revert x; decide +kernel
  rw [base] at h3
  have b := (Atlas.bounds 93 s3).mp h3
  change 1 ≤ s3 at b
  omega
def required : Fin 7 → Nat := ![3,7,7,4,4,5,5]
def candidates : Fin 7 → Circuit := ![⟨[⟨.or,[3,4]⟩,⟨.or,[7,5]⟩,⟨.or,[8,6]⟩],9⟩,⟨[⟨.or,[0,2]⟩,⟨.or,[0,6]⟩,⟨.and,[3,8]⟩,⟨.and,[7,6]⟩,⟨.or,[9,10]⟩,⟨.or,[11,4]⟩,⟨.or,[12,5]⟩],13⟩,⟨[⟨.or,[0,1]⟩,⟨.or,[0,5]⟩,⟨.or,[4,5]⟩,⟨.and,[7,9]⟩,⟨.and,[3,8]⟩,⟨.or,[10,11]⟩,⟨.or,[12,6]⟩],13⟩,⟨[⟨.and,[1,4]⟩,⟨.or,[7,0]⟩,⟨.or,[8,5]⟩,⟨.or,[9,6]⟩],10⟩,⟨[⟨.and,[3,5]⟩,⟨.or,[7,0]⟩,⟨.or,[8,1]⟩,⟨.or,[9,6]⟩],10⟩,⟨[⟨.or,[2,4]⟩,⟨.and,[7,6]⟩,⟨.or,[8,0]⟩,⟨.or,[9,1]⟩,⟨.or,[10,3]⟩],11⟩,⟨[⟨.and,[1,5]⟩,⟨.or,[7,0]⟩,⟨.or,[8,2]⟩,⟨.or,[9,3]⟩,⟨.or,[10,4]⟩],11⟩]
theorem certificates : ∀ v : Fin 7, (candidates v).size=required v ∧
    ((candidates v).gates.all legalGate)=true ∧ ∀ x : Fin 7 → Bool, (candidates v).eval (List.ofFn x)=value v x := by decide +kernel
theorem exact (v : Fin 7) (s : Nat) : HasCircuitSize 7 (value v) s ↔ required v ≤ s := by
  constructor
  · intro small
    fin_cases v
    · exact low0 s small
    · exact low1 s small
    · exact low2 s small
    · exact low3 s small
    · exact low4 s small
    · exact low5 s small
    · exact low6 s small
  · intro enough
    obtain ⟨size,leg,ev⟩ := certificates v
    refine ⟨candidates v,?_,size.le.trans enough,ev⟩
    intro g hg
    obtain ⟨op,n⟩ := validGate (List.all_eq_true.mp leg g hg)
    rcases op with a|b
    · exact ⟨by simp [a],n⟩
    · exact ⟨by simp [b],n⟩
end Seven11224.High

namespace Seven11224.Readers
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3223 Seven11224.Atlas
def chosen (z : Fin 128) (j : Nat) := decide (j<7) && z.val.testBit j
def readsSet (z : Fin 128) (g : Gate) := g.inputs.any (chosen z)
def restrictSet (z : Fin 128) : List (Option (Fin 7)) :=
  List.ofFn (fun i : Fin 7 => if z.val.testBit i.val then none else some i)
def zeroOut (z : Fin 128) (x : Fin 7 → Bool) (i : Fin 7) := if z.val.testBit i.val then false else x i

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem listProject : ∀ (z : Fin 128) (x : Fin 7 → Bool), proj (restrictSet z) x=List.ofFn (zeroOut z x) := by decide +kernel
theorem projectedSet (C : Circuit) (hc : correct C) (z : Fin 128) (x : Fin 7 → Bool) :
    C.eval (proj (restrictSet z) x)=pinned z x := by
  rw [listProject,hc]
  exact PEqualNP.Outside.L_meta_11223.dec_f _
set_option maxHeartbeats 0 in
theorem variations : ∀ z : Fin 128, Atlas.cost z=0 ∨ ∃ r : Fin 128, pinned z (bits 0) ≠ pinned z (bits r.val) := by decide +kernel

def HoldsZero (z : Fin 128) (xs : List (Bool ⊕ Nat)) := ∀ j : Nat, chosen z j=true →
  j<xs.length ∧ xs.getD j (.inl false)=.inl false

theorem count_restricted (z : Fin 128) (m : Nat) (gs : List Gate) (acc : List (Bool ⊕ Nat) × List Gate)
    (ok : ∀ g∈gs, NOkGate g) (hzero : HoldsZero z acc.1) :
    (elimPass m gs acc).2.length + gs.countP (readsSet z) ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons]
    have next : HoldsZero z (elimStep m acc g).1 := by
      intro j hj
      obtain ⟨lt,tag⟩ := hzero j hj
      constructor
      · simp [elimStep]; omega
      · simp only [elimStep]; rw [getD_snoc_ne _ _ _ _ (by omega)]; exact tag
    have tailBound := ih (elimStep m acc g) (fun h hh => ok _ (List.mem_cons_of_mem _ hh)) next
    set vals := g.inputs.map fun i => acc.1.getD i (.inl false) with hv
    set opt := (simplifyGate g.op (m + acc.2.length) vals).1 with ho
    have len : (elimStep m acc g).2.length = acc.2.length + opt.toList.length := by simp [elimStep,ho,hv]
    rw [len] at tailBound
    cases read : readsSet z g with
    | true =>
      obtain ⟨j,mem,sel⟩ := List.any_eq_true.mp read
      have gok := ok g List.mem_cons_self
      have eliminated : opt=none := simplifyGate_none_of_const _ _ _ gok.1.1 (by simpa [hv] using gok.1.2)
        (fun h => by simpa [hv] using gok.2 h) ⟨false,List.mem_map.mpr ⟨j,mem,(hzero j sel).2⟩⟩
      rw [eliminated] at tailBound
      simp [List.countP_cons,read] at tailBound ⊢
      omega
    | false =>
      have bound := toList_opt_len_le opt
      simp [List.countP_cons,read] at tailBound ⊢
      omega

theorem all_read_budgets (C : Circuit) (legal : FanInTwo C) (hc : correct C) (z : Fin 128) :
    Atlas.cost z + (C.gates.map normGate).countP (readsSet z) ≤ C.size := by
  rcases variations z with empty | ⟨r,hr⟩
  · rw [empty,zero_add]
    simpa only [List.length_map,Circuit.size] using (List.countP_le_length (p:=readsSet z) (l:=C.gates.map normGate))
  have vary : ∃ x y, C.eval (proj (restrictSet z) x) ≠ C.eval (proj (restrictSet z) y) :=
    ⟨bits 0,bits r.val,by simpa only [projectedSet C hc] using hr⟩
  obtain ⟨D,df,ds,de⟩ := extract C (restrictSet z) legal vary
  have lo := (bounds z D.size).mp ⟨D,df,le_rfl,fun x => (de x).trans (projectedSet C hc z x)⟩
  have init : HoldsZero z (start (restrictSet z)).1 := by
    have finite : ∀ (a : Fin 128) (i : Fin 7), chosen a i.val=true →
        i.val < (start (restrictSet a)).1.length ∧ (start (restrictSet a)).1.getD i.val (.inl false)=.inl false := by decide +kernel
    intro j hj
    have h := of_decide_eq_true (Bool.and_eq_true_iff.mp hj).1
    exact finite z ⟨j,h⟩ hj
  have budget := count_restricted z 7 (C.gates.map normGate) (start (restrictSet z)) (by
    intro g hg; obtain ⟨g0,h0,rfl⟩ := List.mem_map.mp hg; exact normGate_nok g0 (legal g0 h0)) init
  change D.size = (elimPass 7 (C.gates.map normGate) (start (restrictSet z))).2.length at ds
  have total : D.size + (C.gates.map normGate).countP (readsSet z) ≤ C.gates.length := by
    rw [ds]; simpa only [start,List.length_nil,zero_add,List.length_map] using budget
  exact (Nat.add_le_add_right lo _).trans total
end Seven11224.Readers

#print axioms Seven11224.exact_budget
#print axioms Seven11224.Atlas.bounds
#print axioms Seven11224.Atlas.witnesses
#print axioms Seven11224.High.exact
#print axioms Seven11224.High.certificates
#print axioms Seven11224.Readers.per_input
#print axioms Seven11224.Readers.unique_or
#print axioms Seven11224.Readers.all_read_budgets
