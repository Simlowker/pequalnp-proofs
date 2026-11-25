import Mathlib
import PEqualNP.Outside.L_meta_4767
import PEqualNP.Outside.L_meta_4897
import PEqualNP.Outside.L_meta_7684

/-!
# Gate counts after disabling AND gates in a projective-plane incidence circuit

`Simlowker.MatchedPlane.plane_loss` bounds the number of incidences which must disappear
when all exceptional AND gates are disabled simultaneously. `raw` follows only OR gates
backwards to primary inputs. An AND is exceptional if its two raw sets contain a pair
which is not an edge. The test uses the circuit topology and the graph.

`plane_iff` proves the threshold for a read-one replacement under the posted plane axioms.
`replacement_if` proves that conclusion for circuits satisfying the numerical loss test.
`intact_loss` strengthens the count at the first possible loss of a perfect matching.
`surviving_matching` is a separate finite geometry result for arbitrary deletions.

The general lower bound for unrestricted circuits in L-meta-2583 remains open.
The gate accounting uses Arvin's L-meta-4767 lemmas `cover_half`, `edge_birth`,
`edge_finset_gate_bound` and `gate_partition_count`. The cover lower bound and the
read-one construction come from L-meta-4897 and L-meta-7684 respectively.
-/
namespace Simlowker.IncidenceCover
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4897 (graph cross)

def computes {P L : ℕ} (E : Finset (Fin P × Fin L)) (C : Circuit) :=
  ∀ z : Fin (P+L) → Bool, circuitFun (P+L) C z =
    decide (∃ p l, (p,l)∈E ∧ z (Fin.castAdd L p)=true ∧ z (Fin.natAdd P l)=true)

def replacement {P L : ℕ} (E : Finset (Fin P × Fin L)) (C : Circuit) :=
  ∃ D : Circuit, IsAO2 (P+L) D ∧ computes E D ∧ D.size≤C.size ∧ PEqualNP.ReadK.IsReadK (P+L) D 1

theorem from_cover {P L : ℕ} {E : Finset (Fin P × Fin L)} {C : Circuit}
    (A : Finset (Fin P)) (B : Finset (Fin L))
    (hits : ∀ e∈E,e.1∈A ∨ e.2∈B) (budget : E.card+A.card+B.card≤C.size+1) :
    replacement E C := by
  obtain ⟨D,ao,sz,works,read⟩ := PEqualNP.Outside.L_meta_7684 P L E A B hits
  exact ⟨D,ao,works,by omega,read⟩

def rectangleFree {P L} (E : Finset (Fin P × Fin L)) :=
  ∀ p q l m, p≠q → l≠m → ¬ ((p,l)∈E ∧ (p,m)∈E ∧ (q,l)∈E ∧ (q,m)∈E)


end Simlowker.IncidenceCover


namespace Simlowker.ThreeCarrierGeometry

theorem plane_dual {q N : Nat} (hq : 0<q) (num : N=q^2+q+1)
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (lineCard : ∀ l, Fintype.card {p // I p l}=q+1)
    (join : ∀ p r, p≠r → ∃! l, I p l ∧ I r l) :
    (∀ A B, A≠B → ∃! t, I t A ∧ I t B) ∧ (∀ p, Fintype.card {l // I p l}=q+1) := by
  classical
  let : Membership (Fin N) (Fin N) := ⟨fun l p => I p l⟩
  let H : Fin N := ⟨0,by omega⟩
  have eqOr {p r A B : Fin N} (a : I p A) (b : I r A) (c : I p B) (d : I r B) :
      p=r ∨ A=B := by
    by_cases h : p=r
    · exact Or.inl h
    · obtain ⟨l,_,uni⟩ := join p r h
      exact Or.inr ((uni A ⟨a,b⟩).trans (uni B ⟨c,d⟩).symm)
  have outside (A : Fin N) : ∃ z, ¬I z A := by
    by_contra! h
    have e : Finset.univ.filter (fun z => I z A) = Finset.univ := by simp [h]
    have hh := lineCard A
    rw [Fintype.card_subtype,e,Finset.card_univ,Fintype.card_fin] at hh
    nlinarith [Nat.one_le_pow 2 q hq]
  have off (p : Fin N) : ∃ l, ¬ I p l := by
    by_cases ha : I p H
    · obtain ⟨z,hz⟩ := outside H
      have other : ∃ r, I r H ∧ r≠p := by
        by_contra! no
        have sub : (Finset.univ.filter fun r => I r H) ⊆ {p} := by
          intro r hr; exact Finset.mem_singleton.mpr (no r (Finset.mem_filter.mp hr).2)
        have hh := Finset.card_le_card sub
        rw [Finset.card_singleton,← Fintype.card_subtype,lineCard] at hh
        omega
      obtain ⟨r,hr,ne⟩ := other
      have rz : r≠z := by rintro rfl; exact hz hr
      obtain ⟨l,⟨a,b⟩,_⟩ := join r z rz
      refine ⟨l,fun h => ?_⟩
      have e : l=H := (eqOr a h hr ha).resolve_left ne
      exact hz (e ▸ b)
    · exact ⟨H,ha⟩
  let : Configuration.HasLines (Fin N) (Fin N) :=
    { exists_point := outside, exists_line := off, eq_or_eq := fun a b c d => eqOr a b c d
      mkLine := fun {p r} h => (join p r h).exists.choose
      mkLine_ax := fun {p r} h => (join p r h).exists.choose_spec }
  let := Configuration.HasLines.hasPoints (P := Fin N) (L := Fin N) rfl
  refine ⟨fun A B h => Configuration.HasPoints.existsUnique_point (Fin N) (Fin N) A B h,?_⟩
  obtain ⟨f,hf,prop⟩ := Configuration.HasLines.exists_bijective_of_card_eq (P := Fin N) (L := Fin N) rfl
  intro p
  obtain ⟨l,rfl⟩ := hf.surjective p
  have eq := prop l
  change Nat.card {p // I p l} = Nat.card {l' // I (f l) l'} at eq
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,lineCard] at eq
  exact eq.symm
end Simlowker.ThreeCarrierGeometry


namespace Simlowker.MatchedPlane
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm IncidenceCover

/-- In a balanced bipartite graph every vertex cover meets each edge of a perfect matching. -/
theorem paired_cover {N : Nat} (E : Finset (Fin N × Fin N)) (σ : Equiv.Perm (Fin N))
    (edge : ∀ p, (p,σ p) ∈ E) (A B : Finset (Fin N))
    (hits : ∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) : N ≤ A.card+B.card := by
  have incl : (Finset.univ : Finset (Fin N)) ⊆ A ∪ B.map σ.symm.toEmbedding := by
    intro p hp
    rcases hits (p,σ p) (edge p) with h | h
    · exact Finset.mem_union_left _ h
    · apply Finset.mem_union_right
      exact Finset.mem_map.mpr ⟨σ p,h,σ.symm_apply_apply p⟩
  have bound := (Finset.card_le_card incl).trans (Finset.card_union_le _ _)
  simpa using bound

/-- The replacement question is equivalent to a concrete gate count for these graphs. -/
theorem iff_lower {N : Nat} (E : Finset (Fin N × Fin N)) (σ : Equiv.Perm (Fin N))
    (edge : ∀ p, (p,σ p) ∈ E) (rect : IncidenceCover.rectangleFree E) (C : Circuit) :
    replacement E C ↔ E.card + N ≤ C.size + 1 := by
  constructor
  · rintro ⟨D,ok,ev,size,read⟩
    obtain ⟨A,B,hits,sz⟩ := PEqualNP.Outside.L_meta_4897 N N E D rect ok ev read
    have h := paired_cover E σ edge A B hits
    omega
  · intro h
    exact from_cover Finset.univ ∅ (fun e _ => Or.inl (Finset.mem_univ e.1)) (by simpa using h)
end Simlowker.MatchedPlane

namespace Simlowker.MatchedPlane
open PEqualNP.CircuitLowerBounds IncidenceCover

def edges {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I] : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun e => I e.1 e.2
@[simp] theorem mem_edges {N} (I : Fin N → Fin N → Prop) [DecidableRel I] (p l) :
    (p,l) ∈ edges I ↔ I p l := by simp [edges]

theorem edge_count {N d : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hc : ∀ l, (Finset.univ.filter fun p => I p l).card = d) : (edges I).card=N*d := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f:=Prod.snd) (t:=Finset.univ) (s:=edges I) (by simp)]
  have fiber (l : Fin N) : ((edges I).filter fun e => e.2=l).card = d := by
    rw [← hc l]
    apply Finset.card_bij (fun e _ => e.1)
    · rintro ⟨p,l'⟩ h
      simp only [Finset.mem_filter,mem_edges,Finset.mem_univ,true_and] at h ⊢
      exact h.2 ▸ h.1
    · rintro ⟨p,l'⟩ h ⟨r,m⟩ j eq
      simp_all
    · intro p hp
      exact ⟨(p,l),by simpa [edges] using hp,rfl⟩
  simp [fiber]

theorem regular_matching {N d : Nat} (hd : 0<d) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (row : ∀ p, (Finset.univ.filter fun l => I p l).card=d)
    (col : ∀ l, (Finset.univ.filter fun p => I p l).card=d) :
    ∃ σ : Equiv.Perm (Fin N), ∀ p,I p (σ p) := by
  classical
  have hall (A : Finset (Fin N)) : A.card ≤ (Finset.univ.filter fun l => ∃ a∈A,I a l).card := by
    let B := Finset.univ.filter fun l => ∃ a∈A,I a l
    have bind : A.card*d ≤ B.card*d := by
      apply Finset.card_mul_le_card_mul I
      · intro a ha
        have eq : B.bipartiteAbove I a = Finset.univ.filter (fun l => I a l) := by
          ext l
          simp only [Finset.bipartiteAbove,Finset.mem_filter,Finset.mem_univ,true_and,B]
          exact ⟨And.right, fun e => ⟨⟨a,ha,e⟩,e⟩⟩
        rw [eq,row]
      · intro b _
        rw [← col b]
        apply Finset.card_le_card
        exact fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ha).2⟩
    exact Nat.le_of_mul_le_mul_right bind hd
  obtain ⟨f,inj,hf⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective I).mp (by intro A; convert hall A using 2; ext b; simp)
  exact ⟨Equiv.ofBijective f ⟨inj,Finite.surjective_of_injective inj⟩,hf⟩

theorem plane_iff {q N : Nat} (hq : 2≤q) (num : N=q^2+q+1)
    (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (col : ∀ l, (Finset.univ.filter fun p => I p l).card=q+1)
    (join : ∀ p r, p≠r → ∃! l,I p l ∧ I r l) :
    replacement (edges I) C ↔ N*(q+2) ≤ C.size+1 := by
  have row := (ThreeCarrierGeometry.plane_dual (by omega) num I (fun l => by simpa [Fintype.card_subtype] using col l) join).2
  obtain ⟨σ,hσ⟩ := regular_matching (by omega : 0<q+1) I (fun p => by simpa [Fintype.card_subtype] using row p) col
  have rect : rectangleFree (edges I) := by
    rintro p r l m ne nml ⟨a,b,c,e⟩
    obtain ⟨t,_,u⟩ := join p r ne
    simp only [mem_edges] at a b c e
    exact nml ((u l ⟨a,c⟩).trans (u m ⟨b,e⟩).symm)
  rw [iff_lower (edges I) σ (fun p => (mem_edges I _ _).mpr (hσ p)) rect C,edge_count I col]
  ring_nf
end Simlowker.MatchedPlane

namespace Simlowker.RawIncidence
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_4767

/-- Inputs accessible by following only OR gates backwards. Position 0 is the dummy false wire. -/
def raw (n : Nat) (gs : List Gate) (w : Nat) : Finset (Fin n) :=
  if _h : n+1 ≤ w then
    if andPos n gs w then ∅ else raw n gs (firstWire n gs w) ∪ raw n gs (secondWire n gs w)
  else supports gs w
termination_by w
decreasing_by all_goals apply clamp_lt; omega

theorem raw_base {n gs w} (hw : w<n+1) : raw n gs w = supports gs w := by
  rw [raw]; simp [Nat.not_le_of_gt hw]
theorem raw_or {n gs w} (h : n+1≤w) (o : andPos n gs w=false) :
    raw n gs w = raw n gs (firstWire n gs w) ∪ raw n gs (secondWire n gs w) := by
  rw [raw]; simp [h,o]
theorem raw_and {n gs w} (h : n+1≤w) (o : andPos n gs w=true) : raw n gs w=∅ := by
  rw [raw]; simp [h,o]
theorem raw_sub {n : Nat} (gs : List Gate) (ops : binaryOps gs)
    (ne : ∀ g ∈ gs, g.op=GateOp.and → g.inputs≠[]) (w : Nat) (hi : w<n+1+gs.length) :
    raw n gs w ⊆ supports gs w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases lo : n+1 ≤ w
    · have l := clamp_lt (w:=w) ((gateAtPos n gs w).inputs.getD 0 (w-1)) (by omega)
      have r : secondWire n gs w < w := clamp_lt _ _ (by omega)
      change firstWire n gs w < w at l
      cases ha : andPos n gs w with
      | false => rw [raw_or lo ha,support_or gs ops ne w lo hi ha]; exact Finset.union_subset_union (ih _ l (by omega)) (ih _ r (by omega))
      | true => rw [raw_and lo ha]; exact Finset.empty_subset _
    · rw [raw_base (by omega : w<n+1)]

def Cross {n : Nat} (G : SimpleGraph (Fin n)) (gs : List Gate) (w : Nat) : Prop :=
  ∀ u ∈ raw n gs (firstWire n gs w), ∀ v ∈ raw n gs (secondWire n gs w), G.Adj u v

def exceptional {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (gs : List Gate) (w : Nat) : Bool :=
  letI : Decidable (Cross G gs w) := by unfold Cross; infer_instance
  andPos n gs w && decide (¬ Cross G gs w)

def exceptions {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (gs : List Gate) :=
  (Finset.range (n+1+gs.length)).filter fun w => n+1 ≤ w ∧ andPos n gs w = true ∧ exceptional G gs w=true

def hit {n : Nat} (gs : List Gate) (w : Nat) (u v : Fin n) := posRead gs w (pairBits u v)=true

end Simlowker.RawIncidence

namespace Simlowker.RawIncidence
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_4767

/-- Run the circuit on the two endpoints, replacing the marked AND gates by false. -/
def pruned {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (gs : List Gate)
    (w : Nat) (u v : Fin n) : Bool :=
  if _h : n+1 ≤ w then
    if andPos n gs w then
      !(exceptional G gs w) && pruned G gs (firstWire n gs w) u v && pruned G gs (secondWire n gs w) u v
    else pruned G gs (firstWire n gs w) u v || pruned G gs (secondWire n gs w) u v
  else posRead gs w (pairBits u v)
termination_by w
decreasing_by all_goals apply clamp_lt; omega

def Survives {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (gs : List Gate) (out : Nat) (u v : Fin n) :=
  pruned G gs (clampWire (n+gs.length) out) u v=true

theorem pruned_symm {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (gs : List Gate) (w : Nat) (u v : Fin n) :
    pruned G gs w u v = pruned G gs w v u := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hk : n+1≤w
    · have a : firstWire n gs w < w := clamp_lt _ _ (by omega)
      have b : secondWire n gs w < w := clamp_lt _ _ (by omega)
      rw [pruned.eq_1 G gs w u v,pruned.eq_1 G gs w v u]; simp [hk,ih _ a,ih _ b]
    · rw [pruned.eq_1 G gs w u v,pruned.eq_1 G gs w v u,dite_eq_right hk,dite_eq_right hk]
      have eq : pairBits u v = pairBits v u := by funext i; simp [pairBits,or_comm]
      rw [eq]

/-- Pair acceptance in the pruned circuit implies pair acceptance in the original circuit. -/
theorem pruned_sound {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (gs : List Gate)
    (ops : binaryOps gs) (ne : ∀ g∈gs, g.op=GateOp.and → g.inputs≠[])
    (w : Nat) (hi : w<n+1+gs.length) (u v : Fin n) : pruned G gs w u v=true → hit gs w u v := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rw [pruned.eq_1]; unfold hit
    split_ifs with lo ha
    · rw [pos_gate gs ops ne w lo hi,ha]
      have a : firstWire n gs w < w := clamp_lt _ _ (by omega)
      have b : secondWire n gs w < w := clamp_lt _ _ (by omega)
      simp only [Bool.and_eq_true,ite_true]
      exact fun h => ⟨ih _ a (by omega) h.1.2,ih _ b (by omega) h.2⟩
    · rw [pos_gate gs ops ne w lo hi,ite_eq_right ha]
      have a : firstWire n gs w < w := clamp_lt _ _ (by omega)
      have b : secondWire n gs w < w := clamp_lt _ _ (by omega)
      simp only [Bool.or_eq_true]
      exact fun h => h.imp (ih _ a (by omega)) (ih _ b (by omega))
    · exact id
end Simlowker.RawIncidence

namespace Simlowker.RawIncidence
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_4767

/-- A successful justification follows a selected branch at OR and both branches at AND. -/
structure Paths {n : Nat} (gs : List Gate) (P : Nat → Fin n → Fin n → Prop) : Prop where
  input : ∀ w u v, w<n+1 → P w u v → u∈raw n gs w ∨ v∈raw n gs w
  orGate : ∀ w u v, n+1≤w → w<n+1+gs.length → andPos n gs w=false → P w u v →
    P (firstWire n gs w) u v ∨ P (secondWire n gs w) u v
  andGate : ∀ w u v, n+1≤w → w<n+1+gs.length → andPos n gs w=true → P w u v →
    P (firstWire n gs w) u v ∧ P (secondWire n gs w) u v

theorem ordinary_paths {n gs} (ops : binaryOps gs) (ne : ∀ g∈gs,g.op=GateOp.and → g.inputs≠[]) :
    Paths gs (hit (n:=n) gs) := by
  constructor
  · intro w u v hw h; simpa only [raw_base hw] using hit_base gs w u v hw h
  · intro w u v lo hi ha h; simpa only [hit,pos_gate gs ops ne w lo hi,ha,Bool.false_eq_true,ite_false,Bool.or_eq_true] using h
  · intro w u v lo hi ha h; simpa only [hit,pos_gate gs ops ne w lo hi,ha,ite_true,Bool.and_eq_true] using h

theorem pruned_paths {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (gs : List Gate) :
    Paths gs (fun w u v => pruned G gs w u v=true) := by
  constructor
  · intro w u v hw h
    rw [pruned.eq_1,dite_eq_right (by omega : ¬ n+1≤w)] at h
    simpa only [raw_base hw] using hit_base gs w u v hw h
  · intro w u v lo _ ha h
    rw [pruned.eq_1,dite_eq_left lo,ha] at h
    simpa using h
  · intro w u v lo _ ha h
    rw [pruned.eq_1,dite_eq_left lo,ha] at h
    simp only [ite_true,Bool.and_eq_true] at h
    exact ⟨h.1.2,h.2⟩

theorem pruned_off {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (gs : List Gate)
    {w} (hw : w∈exceptions G gs) (u v : Fin n) : pruned G gs w u v=false := by
  obtain ⟨_,lo,ha,ex⟩ := Finset.mem_filter.mp hw
  rw [pruned.eq_1,dite_eq_left lo,ha]; simp [ex]

/-- Count F and cover K independently, with separate choices of gate justifications. -/
theorem path_bound {n : Nat} (G K : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gs : List Gate) (out : Nat) (ops : binaryOps gs)
    (ne : ∀ g∈gs, g.op=GateOp.and → g.inputs≠[])
    (correct : ∀ x, (Circuit.mk gs out).eval (List.ofFn x)=true ↔ edgeTrue G x)
    (hc4 : ∀ a b c d : Fin n, a≠c → b≠d → ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (F : Finset (Sym2 (Fin n)))
    (P Q : Nat → Fin n → Fin n → Prop) (pP : Paths gs P) (pQ : Paths gs Q)
    (rootF : ∀ u v, s(u,v)∈F → P (clampWire (n+gs.length) out) u v)
    (rootK : ∀ u v, K.Adj u v → Q (clampWire (n+gs.length) out) u v)
    (safeF : ∀ w ∈ exceptions G gs, ∀ u v, s(u,v) ∈ F → ¬ P w u v)
    (pin : Nat → Finset (Fin n)) (small : ∀ w, (pin w).card ≤ 1)
    (pins : ∀ w ∈ exceptions G gs, ∀ u v, K.Adj u v → Q w u v → u∈pin w ∨ v∈pin w) :
    ∃ T : Finset (Fin n), (∀ u v, K.Adj u v → u∈T ∨ v∈T) ∧
      F.card + T.card + (exceptions G gs).card ≤ gs.length+1 := by
  classical
  let k := n+1
  let N := n+1+gs.length
  let root := clampWire (n+gs.length) out
  let S := raw n gs
  let leftWire := firstWire n gs
  let rightWire := secondWire n gs
  let A := andPos n gs
  let dirty := exceptional G gs
  have dirtyIsAnd (w : Nat) (hd : dirty w=true) : A w=true := (Bool.and_eq_true_iff.mp hd).1
  have earlier1 (w : ℕ) (lo : k ≤ w) (_ : w < N) : leftWire w < w :=
    clamp_lt _ _ (by dsimp [k] at lo; omega)
  have earlier2 (w : ℕ) (lo : k ≤ w) (_ : w < N) : rightWire w < w :=
    clamp_lt _ _ (by dsimp [k] at lo; omega)
  have ORsupport (w : ℕ) (lo : k ≤ w) (hi : w < N) (ho : A w = false) :
      S w = S (leftWire w) ∪ S (rightWire w) := raw_or lo ho
  have crossing (w : Nat) (_ : k ≤ w) (_ : w < N) (ha : A w=true) (hd : dirty w=false) :
      ∀ u∈S (leftWire w), ∀ v∈S (rightWire w), G.Adj u v := by
    change Cross G gs w
    have a : andPos n gs w=true := ha
    simpa [dirty,exceptional,a] using hd
  have disjoint (w : ℕ) (lo : k ≤ w) (hi : w < N) (ha : A w = true)
      (hd : dirty w = false) : Disjoint (S (leftWire w)) (S (rightWire w)) := by
    rw [Finset.disjoint_left]
    intro u hu hv
    exact G.loopless.irrefl u (crossing w lo hi ha hd _ hu _ hv)
  have sideSmall (w : ℕ) (lo : k ≤ w) (hi : w < N) (ha : A w = true)
      (hd : dirty w = false) : (S (leftWire w)).card ≤ 1 ∨ (S (rightWire w)).card ≤ 1 := by
    by_contra! large
    obtain ⟨u, hu, v, hv, hne⟩ := Finset.one_lt_card.mp large.1
    obtain ⟨a, ha', b, hb, hab⟩ := Finset.one_lt_card.mp large.2
    have cross := crossing w lo hi ha hd
    exact hc4 u a v b hne hab ⟨cross u hu a ha', (cross v hv a ha').symm,
      cross v hv b hb, (cross u hu b hb).symm⟩
  have rBound : root < N := root_bound n gs.length out
  have rEmpty : S root = ∅ := Finset.subset_empty.mp ((raw_sub gs ops ne root rBound).trans (by rw [root_support_empty G gs out correct]))
  have pinHit (w : Nat) (u v : Fin n) (lo : k≤w) (hi : w<N) (hd : dirty w=true)
      (uv : K.Adj u v) (h : Q w u v) : u∈pin w ∨ v∈pin w :=
    pins w (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,lo,dirtyIsAnd w hd,hd⟩) u v uv h
  obtain ⟨T,cover,coverBound⟩ := cover_half n k N root K S Q leftWire rightWire A dirty pin rBound rEmpty
    rootK pQ.input earlier1 earlier2 ORsupport pQ.orGate small pinHit sideSmall pQ.andGate
    (fun f R B step => dag_union_bound f R B step)
  let goodAND := (Finset.range N).filter (fun w => k ≤ w ∧ A w = true ∧ dirty w = false)
  let badAND := (Finset.range N).filter (fun w => k ≤ w ∧ A w = true ∧ dirty w = true)
  let allAND := (Finset.range N).filter (fun w => k ≤ w ∧ A w = true)
  let largeOR := (Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)
  let smallOR := (Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ (S w).card ≤ 1)
  have goodBound : F.card ≤ goodAND.card + largeOR.card := by
    apply edge_finset_gate_bound n k N G S leftWire rightWire A dirty F hc4
      (fun w hw => by simpa only [S,raw_base hw] using support_base gs w hw)
      (fun w lo hi => ⟨earlier1 w lo hi, earlier2 w lo hi⟩)
      (fun w lo _ ha _ _ => by simp [S,raw_and lo ha]) ORsupport crossing sideSmall
    intro u v h
    obtain ⟨w,lo,hi,ha,birth⟩ := edge_birth n k N root S P leftWire rightWire A dirty u v rBound
      (rootF u v h) (by simp [rEmpty]) (by simp [rEmpty])
      pP.input earlier1 earlier2 ORsupport pP.orGate pP.andGate disjoint
    rcases birth with ⟨hd,on⟩ | ⟨hd,cross⟩
    · exact (safeF w (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,lo,ha,hd⟩) u v h on).elim
    · exact ⟨w,lo,hi,ha,hd,cross⟩
  have andDisjoint : Disjoint goodAND badAND := by
    rw [Finset.disjoint_left]
    intro w hgood hbad
    have f : dirty w = false := (Finset.mem_filter.mp hgood).2.2.2
    have t : dirty w = true := (Finset.mem_filter.mp hbad).2.2.2
    simp_all
  have andPartition : goodAND.card + badAND.card ≤ allAND.card := by
    rw [← Finset.card_union_of_disjoint andDisjoint]
    apply Finset.card_le_card
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h).1, (Finset.mem_filter.mp h).2.1,
        (Finset.mem_filter.mp h).2.2.1⟩
    · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h).1, (Finset.mem_filter.mp h).2.1,
        (Finset.mem_filter.mp h).2.2.1⟩
  have total : allAND.card + largeOR.card + smallOR.card ≤ gs.length :=
    gate_partition_count n gs.length A S
  change T.card ≤ 1 + smallOR.card at coverBound
  refine ⟨T,cover,?_⟩
  change F.card + T.card + badAND.card ≤ gs.length+1
  omega

/-- Even after all exceptional gates are disabled, every surviving edge needs one unit
of the edge budget and the surviving graph needs a vertex cover. -/
theorem survived_bound {n : Nat} (G K : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel K.Adj]
    (gs : List Gate) (out : Nat) (ops : binaryOps gs) (ne : ∀ g∈gs,g.op=GateOp.and → g.inputs≠[])
    (correct : ∀ x, (Circuit.mk gs out).eval (List.ofFn x)=true ↔ edgeTrue G x)
    (hc4 : ∀ a b c d : Fin n, a≠c → b≠d → ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (keep : ∀ u v, K.Adj u v → Survives G gs out u v) :
    ∃ T : Finset (Fin n), (∀ u v,K.Adj u v → u∈T ∨ v∈T) ∧
      K.edgeFinset.card + T.card + (exceptions G gs).card ≤ gs.length+1 := by
  apply path_bound G K gs out ops ne correct hc4 K.edgeFinset _ _ (pruned_paths G gs) (pruned_paths G gs)
    (fun u v h => keep u v (K.mem_edgeFinset.mp h)) keep _ (fun _ => ∅) (by simp)
  · intro w hw u v _ h; rw [pruned_off G gs hw] at h; contradiction
  · intro w hw u v _ h; rw [pruned_off G gs hw] at h; contradiction
end Simlowker.RawIncidence

namespace Simlowker.MatchedPlane

theorem row_fiber {N} (I : Fin N → Fin N → Prop) [DecidableRel I] (p : Fin N) :
    ((edges I).filter (fun e => e.1=p)).card=(Finset.univ.filter fun l => I p l).card := by
  apply Finset.card_bij (fun e _ => e.2)
  · rintro ⟨p',l⟩ h
    simp only [Finset.mem_filter,mem_edges,Finset.mem_univ,true_and] at h ⊢
    exact h.2 ▸ h.1
  · rintro ⟨p',l⟩ h ⟨r,m⟩ j eq; simp_all
  · intro l h; exact ⟨(p,l),by simpa [edges] using h,rfl⟩

theorem col_fiber {N} (I : Fin N → Fin N → Prop) [DecidableRel I] (l : Fin N) :
    ((edges I).filter (fun e => e.2=l)).card=(Finset.univ.filter fun p => I p l).card := by
  apply Finset.card_bij (fun e _ => e.1)
  · rintro ⟨p,l'⟩ h
    simp only [Finset.mem_filter,mem_edges,Finset.mem_univ,true_and] at h ⊢
    exact h.2 ▸ h.1
  · rintro ⟨p,l'⟩ h ⟨r,m⟩ j eq; simp_all
  · intro p h; exact ⟨(p,l),by simpa [edges] using h,rfl⟩

/-- In a d-regular balanced incidence relation, deleting b edges lowers its minimum cover
size by at most floor(b/d). The remaining edges are counted only once. -/
theorem cover_loss {N d : Nat} (hd : 0<d) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (row : ∀ p, (Finset.univ.filter fun l => I p l).card=d)
    (col : ∀ l, (Finset.univ.filter fun p => I p l).card=d)
    (F : Finset (Fin N × Fin N)) (sub : F ⊆ edges I) (A B : Finset (Fin N))
    (cover : ∀ e∈F, e.1∈A ∨ e.2∈B) : N ≤ A.card+B.card+((edges I).card-F.card)/d := by
  classical
  let R (p : Fin N) := (edges I).filter fun e => e.1=p
  let C (l : Fin N) := (edges I).filter fun e => e.2=l
  have incl : F ⊆ A.biUnion R ∪ B.biUnion C := by
    intro e he
    rcases cover e he with h|h
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨_,h,Finset.mem_filter.mpr ⟨sub he,rfl⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨_,h,Finset.mem_filter.mpr ⟨sub he,rfl⟩⟩)
  have hr : (A.biUnion R).card ≤ A.card*d := by
    calc _ ≤ ∑ p∈A,(R p).card := Finset.card_biUnion_le
         _ = _ := by simp [R,row_fiber,row]
  have hc : (B.biUnion C).card ≤ B.card*d := by
    calc _ ≤ ∑ l∈B,(C l).card := Finset.card_biUnion_le
         _ = _ := by simp [C,col_fiber,col]
  have area := (Finset.card_le_card incl).trans (Finset.card_union_le _ _)
  have size : F.card ≤ (A.card+B.card)*d := by rw [Nat.add_mul]; omega
  have s := Finset.card_le_card sub
  rw [edge_count I col] at *
  by_cases done : N ≤ A.card+B.card
  · exact done.trans (Nat.le_add_right _ _)
  have dn : (N-(A.card+B.card))*d ≤ N*d-F.card := by rw [Nat.sub_mul]; omega
  have rem := (Nat.le_div_iff_mul_le hd).mpr dn
  omega
end Simlowker.MatchedPlane

namespace Simlowker.MatchedPlane
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open IncidenceCover PEqualNP.Outside.L_meta_4897 PEqualNP.Outside.L_meta_4767 Simlowker.RawIncidence

instance graphRel {m n} (E : Finset (Fin m × Fin n)) : DecidableRel (graph E).Adj := by
  intro a b
  change Decidable (cross E (finSumFinEquiv.symm a) (finSumFinEquiv.symm b))
  cases finSumFinEquiv.symm a <;> cases finSumFinEquiv.symm b <;> simp only [cross] <;> infer_instance

def kept {N} (E : Finset (Fin N × Fin N)) (C : Circuit) :=
  E.filter fun e => pruned (graph E) C.gates (clampWire (N+N+C.gates.length) C.output)
    (Fin.castAdd N e.1) (Fin.natAdd N e.2)=true

/-- Cost charged by the edges which survive simultaneous deletion of all exceptional AND outputs. -/
theorem bipartite_bound {N} (E : Finset (Fin N × Fin N)) (C : Circuit) (rect : rectangleFree E)
    (ao : IsAO2 (N+N) C) (correct : computes E C) :
    ∃ A B : Finset (Fin N), (∀ e∈kept E C,e.1∈A ∨ e.2∈B) ∧
      (kept E C).card+A.card+B.card+(exceptions (graph E) C.gates).card ≤ C.size+1 := by
  classical
  let G := graph E
  let F := kept E C
  let K := graph F
  have hrect : ∀ a b c d, a≠c → b≠d → ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
    let : DecidableRel (graph E).Adj := Classical.decRel _
    rintro a b c d hac hbd ⟨ab,bc,cd,da⟩
    have h := noRectangle E rect a c hac
    exact hbd (Finset.card_le_one.mp h b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ab,bc.symm⟩)
      d (Finset.mem_filter.mpr ⟨Finset.mem_univ _,da.symm,cd⟩))
  have works (x : Fin (N+N) → Bool) : C.eval (List.ofFn x)=true ↔ edgeTrue G x := by
    change circuitFun _ C x=true ↔ _
    rw [correct,decide_eq_true_eq]
    constructor
    · rintro ⟨p,l,mem,hp,hl⟩
      exact ⟨Fin.castAdd N p,Fin.natAdd N l,by simpa only [G,graph,finSumFinEquiv_symm_apply_castAdd,finSumFinEquiv_symm_apply_natAdd,cross] using mem,hp,hl⟩
    · rintro ⟨u,v,uv,hu,hv⟩
      cases u using Fin.addCases <;> cases v using Fin.addCases <;> simp only [G,graph,finSumFinEquiv_symm_apply_castAdd,finSumFinEquiv_symm_apply_natAdd,cross] at uv
      · exact ⟨_,_,uv,hu,hv⟩
      · exact ⟨_,_,uv,hv,hu⟩
  have oks : binaryOps C.gates := fun g hg => ⟨ao.1 _ hg,(ao.2.2 _ hg).le⟩
  have ne : ∀ g ∈ C.gates, g.op=GateOp.and → g.inputs≠[] := by
    intro g hg _ h; have l := ao.2.2 _ hg; simp [h] at l
  have keep : ∀ u v,K.Adj u v → Survives G C.gates C.output u v := by
    intro u v h
    cases u using Fin.addCases <;> cases v using Fin.addCases <;> simp only [K,graph,finSumFinEquiv_symm_apply_castAdd,finSumFinEquiv_symm_apply_natAdd,cross] at h
    · exact (Finset.mem_filter.mp h).2
    · unfold Survives
      rw [pruned_symm]
      exact (Finset.mem_filter.mp h).2
  obtain ⟨T,covers,bound⟩ := survived_bound G K C.gates C.output oks ne works hrect keep
  let S := T.map finSumFinEquiv.symm.toEmbedding
  refine ⟨S.toLeft,S.toRight,?_,?_⟩
  · rintro ⟨p,l⟩ h
    have hit := covers (Fin.castAdd N p) (Fin.natAdd N l) (by simpa only [K,graph,finSumFinEquiv_symm_apply_castAdd,finSumFinEquiv_symm_apply_natAdd,cross] using h)
    rcases hit with hp|hl
    · exact Or.inl (Finset.mem_toLeft.mpr (Finset.mem_map.mpr ⟨_,hp,finSumFinEquiv_symm_apply_castAdd p⟩))
    · exact Or.inr (Finset.mem_toRight.mpr (Finset.mem_map.mpr ⟨_,hl,finSumFinEquiv_symm_apply_natAdd l⟩))
  · have eq : S.toLeft.card + S.toRight.card = T.card := Finset.card_toLeft_add_card_toRight.trans (Finset.card_map _)
    have le : F.card ≤ K.edgeFinset.card := by
      convert counts F using 1
      apply congrArg Finset.card
      ext z; simp [K]
    change F.card+S.toLeft.card+S.toRight.card+(exceptions G C.gates).card ≤ C.gates.length+1
    omega

theorem plane_loss {q N : Nat} (hq : 2≤q) (num : N=q^2+q+1) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (col : ∀ l, (Finset.univ.filter fun p => I p l).card=q+1)
    (join : ∀ p r, p≠r → ∃! l,I p l ∧ I r l) (ao : IsAO2 (N+N) C) (works : computes (edges I) C) :
    let E := edges I
    let b := E.card-(kept E C).card
    N*(q+2)+(exceptions (graph E) C.gates).card ≤ C.size+1+b+b/(q+1) := by
  dsimp only
  have row := (ThreeCarrierGeometry.plane_dual (by omega) num I (fun l => by simpa [Fintype.card_subtype] using col l) join).2
  have rect : rectangleFree (edges I) := by
    rintro p r l m ne nml ⟨a,b,c,e⟩
    obtain ⟨t,_,u⟩ := join p r ne
    simp only [mem_edges] at a b c e
    exact nml ((u l ⟨a,c⟩).trans (u m ⟨b,e⟩).symm)
  obtain ⟨A,B,cover,count⟩ := bipartite_bound (edges I) C rect ao works
  have incl : kept (edges I) C ⊆ edges I := Finset.filter_subset _ _
  have cov := cover_loss (by omega : 0<q+1) I (fun p => by simpa [Fintype.card_subtype] using row p) col _ incl A B cover
  have sz := Finset.card_le_card incl
  have numEdges := edge_count I col
  rw [show N*(q+2)=(edges I).card+N by rw [numEdges]; ring]
  omega
end Simlowker.MatchedPlane

namespace Simlowker.MatchedPlane
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm IncidenceCover PEqualNP.Outside.L_meta_4897 Simlowker.RawIncidence
/-- A directly testable sufficient condition for the exact posted read-one replacement. -/
theorem replacement_if {q N : Nat} (hq : 2≤q) (num : N=q^2+q+1) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (col : ∀ l, (Finset.univ.filter fun p => I p l).card=q+1)
    (join : ∀ p r, p≠r → ∃! l,I p l ∧ I r l) (ao : IsAO2 (N+N) C) (works : computes (edges I) C)
    (small : let b := (edges I).card-(kept (edges I) C).card
             b+b/(q+1) ≤ (exceptions (graph (edges I)) C.gates).card) : replacement (edges I) C := by
  apply (plane_iff hq num I C col join).mpr
  have lower := plane_loss hq num I C col join ao works
  dsimp only at lower small
  omega
end Simlowker.MatchedPlane

namespace Simlowker.MatchedPlane

/-- If at most one line's worth of incidences was lost, a smaller vertex cover forces
an isolated point or line. Every remaining point and line having a neighbor precludes this. -/
theorem intact_cover {q N : Nat} (hq : 2≤q) (num : N=q^2+q+1) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (col : ∀ l, (Finset.univ.filter fun p => I p l).card=q+1)
    (join : ∀ p r, p≠r → ∃! l,I p l ∧ I r l)
    (F : Finset (Fin N × Fin N)) (sub : F ⊆ edges I) (lost : (edges I).card-F.card≤q+1)
    (liveP : ∀ p,∃ l,(p,l)∈F) (liveL : ∀ l,∃ p,(p,l)∈F) (A B : Finset (Fin N))
    (cover : ∀ e∈F,e.1∈A ∨ e.2∈B) : N ≤ A.card+B.card := by
  classical
  by_contra! smaller
  obtain ⟨meet,row'⟩ := ThreeCarrierGeometry.plane_dual (by omega) num I (fun l => by simpa [Fintype.card_subtype] using col l) join
  have row (p : Fin N) : (Finset.univ.filter fun l => I p l).card=q+1 := by simpa [Fintype.card_subtype] using row' p
  let L := edges I \ F
  have loss : L.card≤q+1 := by simpa [L,Finset.card_sdiff_of_subset sub] using lost
  let X := A.biUnion (fun p => (edges I).filter fun e => e.1=p)
  let Y := B.biUnion (fun l => (edges I).filter fun e => e.2=l)
  have incl : F ⊆ X ∪ Y := by
    intro e he; rcases cover e he with h|h
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨_,h,Finset.mem_filter.mpr ⟨sub he,rfl⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨_,h,Finset.mem_filter.mpr ⟨sub he,rfl⟩⟩)
  have hx : X.card≤A.card*(q+1) := Finset.card_biUnion_le.trans (by simp [row_fiber,row])
  have hy : Y.card≤B.card*(q+1) := Finset.card_biUnion_le.trans (by simp [col_fiber,col])
  have above := Finset.card_le_card incl
  have exactSum := Finset.card_union_add_card_inter X Y
  have budget : (A.card+B.card)*(q+1)+(q+1) ≤ N*(q+1) := by
    simpa [Nat.succ_mul] using Nat.mul_le_mul_right (q+1) (Nat.succ_le_iff.mpr smaller)
  rw [Nat.add_mul] at budget
  have size := edge_count I col
  have no (p : Fin N) (hp : p∈A) (l : Fin N) (hl : l∈B) : ¬I p l := by
    intro e
    have mem := (mem_edges I p l).mpr e
    have ix : (p,l)∈X := Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_filter.mpr ⟨mem,rfl⟩⟩
    have iy : (p,l)∈Y := Finset.mem_biUnion.mpr ⟨l,hl,Finset.mem_filter.mpr ⟨mem,rfl⟩⟩
    have pos := Finset.card_pos.mpr (show (X∩Y).Nonempty from ⟨_,Finset.mem_inter.mpr ⟨ix,iy⟩⟩)
    omega
  have a : A.Nonempty := by
    by_contra! h
    have all : B=Finset.univ := Finset.eq_univ_of_forall (fun l => by
      obtain ⟨p,e⟩ := liveL l; exact (cover (p,l) e).resolve_left (by simp [h]))
    simp [all,h] at smaller
  have b : B.Nonempty := by
    by_contra! h
    have all : A=Finset.univ := Finset.eq_univ_of_forall (fun p => by
      obtain ⟨l,e⟩ := liveP p; exact (cover (p,l) e).resolve_right (by simp [h]))
    simp [all,h] at smaller
  obtain ⟨p,hp⟩ := a
  obtain ⟨l,hl⟩ := b
  have outsideP (x : Fin N) (hx : x∈Aᶜ) : ∃ y,(x,y)∈L := by
    have nx := Finset.mem_compl.mp hx
    obtain ⟨j,⟨pj,xj⟩,_⟩ := join p x (fun e => nx (e ▸ hp))
    exact ⟨j,Finset.mem_sdiff.mpr ⟨(mem_edges I x j).mpr xj, fun f => (cover _ f).elim nx (fun hj => no p hp j hj pj)⟩⟩
  have outsideL (y : Fin N) (hy : y∈Bᶜ) : ∃ x,(x,y)∈L := by
    have ny := Finset.mem_compl.mp hy
    obtain ⟨i,⟨il,iy⟩,_⟩ := meet l y (fun e => ny (e ▸ hl))
    exact ⟨i,Finset.mem_sdiff.mpr ⟨(mem_edges I i y).mpr iy, fun f => (cover _ f).elim (fun hi => no i hi l hl il) ny⟩⟩
  have ia : Aᶜ ⊆ L.image Prod.fst := by intro x hx; obtain ⟨y,hy⟩ := outsideP x hx; exact Finset.mem_image.mpr ⟨(x,y),hy,rfl⟩
  have ib : Bᶜ ⊆ L.image Prod.snd := by intro y hy; obtain ⟨x,hx⟩ := outsideL y hy; exact Finset.mem_image.mpr ⟨(x,y),hx,rfl⟩
  have c1 := (Finset.card_le_card ia).trans Finset.card_image_le
  have c2 := (Finset.card_le_card ib).trans Finset.card_image_le
  simp only [Finset.card_compl,Fintype.card_fin] at c1 c2
  have large : 2*(q+1)≤N := by nlinarith [Nat.mul_le_mul_left q hq]
  omega
end Simlowker.MatchedPlane

namespace Simlowker.MatchedPlane
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm IncidenceCover PEqualNP.Outside.L_meta_4897 Simlowker.RawIncidence

theorem surviving_matching {q N : Nat} (hq : 2≤q) (num : N=q^2+q+1) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (col : ∀ l, (Finset.univ.filter fun p => I p l).card=q+1)
    (join : ∀ p r,p≠r → ∃! l,I p l ∧ I r l)
    (F : Finset (Fin N × Fin N)) (sub : F⊆edges I) (lost : (edges I).card-F.card≤q+1)
    (liveP : ∀ p,∃ l,(p,l)∈F) (liveL : ∀ l,∃ p,(p,l)∈F) :
    ∃ σ : Equiv.Perm (Fin N), ∀ p,(p,σ p)∈F := by
  classical
  let R (p l : Fin N) := (p,l)∈F
  have hall (A : Finset (Fin N)) : A.card≤(Finset.univ.filter fun l => ∃ p∈A,R p l).card := by
    let B := Finset.univ.filter fun l => ∃ p∈A,R p l
    have cov (e) (he : e∈F) : e.1∈Aᶜ ∨ e.2∈B := by
      by_cases h : e.1∈A
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨e.1,h,he⟩⟩)
      · exact Or.inl (Finset.mem_compl.mpr h)
    have hh := intact_cover hq num I col join F sub lost liveP liveL Aᶜ B cov
    have aa := Finset.card_le_univ A
    simp only [Finset.card_compl,Fintype.card_fin] at hh aa
    change A.card ≤ B.card; omega
  obtain ⟨f,inj,hf⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective R).mp (by intro A; convert hall A using 2; ext b; simp)
  exact ⟨Equiv.ofBijective f ⟨inj,Finite.surjective_of_injective inj⟩,hf⟩

/-- With at most q+1 losses and no isolated vertex the division term can be removed. -/
theorem intact_loss {q N : Nat} (hq : 2≤q) (num : N=q^2+q+1) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (col : ∀ l, (Finset.univ.filter fun p => I p l).card=q+1)
    (join : ∀ p r,p≠r → ∃! l,I p l ∧ I r l) (ao : IsAO2 (N+N) C) (works : computes (edges I) C)
    (lost : (edges I).card-(kept (edges I) C).card≤q+1)
    (liveP : ∀ p,∃ l,(p,l)∈kept (edges I) C) (liveL : ∀ l,∃ p,(p,l)∈kept (edges I) C) :
    N*(q+2)+(exceptions (graph (edges I)) C.gates).card ≤ C.size+1+((edges I).card-(kept (edges I) C).card) := by
  have rect : rectangleFree (edges I) := by
    rintro p r l m ne nml ⟨a,b,c,e⟩
    obtain ⟨t,_,u⟩ := join p r ne
    simp only [mem_edges] at a b c e
    exact nml ((u l ⟨a,c⟩).trans (u m ⟨b,e⟩).symm)
  obtain ⟨A,B,cover,count⟩ := bipartite_bound (edges I) C rect ao works
  have sub : kept (edges I) C⊆edges I := Finset.filter_subset _ _
  have cv := intact_cover hq num I col join _ sub lost liveP liveL A B cover
  have ss := Finset.card_le_card sub
  rw [show N*(q+2)=(edges I).card+N by rw [edge_count I col]; ring]
  omega
end Simlowker.MatchedPlane
