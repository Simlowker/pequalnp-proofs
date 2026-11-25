import PEqualNP.Outside.L_meta_2074

/-! ## Residual maximum degree -/

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
namespace Simlowker.Residual1735

theorem residual_degree (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (least : IsLeastAO G C) (d : Nat)
    (bound : ∀ v, (G.deleteEdges (starEdges G C : Set (Sym2 (Fin n)))).degree v ≤ d) :
    2 * (Ustar G C).card ≤ (C.size + 1) * d := by
  classical
  let D := G.deleteEdges (starEdges G C : Set (Sym2 (Fin n)))
  have edgeEq : D.edgeFinset.card = (Ustar G C).card := by
    simp [D,Ustar,SimpleGraph.edgeFinset_deleteEdges]
  have supp (v : Fin n) (hv : 0 < D.degree v) : v ∈ G.support := by
    obtain ⟨w,hw⟩ := (D.degree_pos_iff_exists_adj v).mp hv
    exact ⟨w,(G.deleteEdges_le _) hw⟩
  have filterSum : (∑ v ∈ G.support.toFinset, D.degree v) = ∑ v, D.degree v := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ outside
    by_contra! h
    exact outside (Set.mem_toFinset.mpr (supp v (by omega)))
  have edgeBound : (∑ v ∈ G.support.toFinset, D.degree v) ≤ G.support.toFinset.card * d := by
    calc
      _ ≤ ∑ _v ∈ G.support.toFinset, d := Finset.sum_le_sum (fun v _ => bound v)
      _ = _ := by simp
  rw [filterSum,D.sum_degrees_eq_twice_card_edges,edgeEq] at edgeBound
  have supportBound := PEqualNP.Outside.L_meta_2074 n G C least
  have cardSupport : G.support.toFinset.card = G.support.ncard := by
    simp [Set.ncard_eq_toFinset_card']
  rw [cardSupport] at edgeBound
  exact edgeBound.trans (Nat.mul_le_mul_right d supportBound)

#print axioms residual_degree
end Simlowker.Residual1735

/-! ## Disjoint second neighborhoods -/

namespace Simlowker.Residual1735
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

variable {n : Nat} (D : SimpleGraph (Fin n)) [DecidableRel D.Adj]

def triangleFree := ∀ a b c, D.Adj a b → D.Adj a c → ¬ D.Adj b c
def squareFree := ∀ u v x y, u ≠ v → D.Adj u x → D.Adj v x → D.Adj u y → D.Adj v y → x = y

def block (a b : Fin n) := insert b ((D.neighborFinset b).erase a)

theorem block_card {a b : Fin n} (h : D.Adj a b) : (block D a b).card = D.degree b := by
  have hab : a ∈ D.neighborFinset b := (D.mem_neighborFinset _ _).mpr h.symm
  have hbb : b ∉ (D.neighborFinset b).erase a := by
    intro h
    exact D.loopless.irrefl b ((D.mem_neighborFinset _ _).mp (Finset.mem_erase.mp h).2)
  rw [block, Finset.card_insert_of_notMem hbb, Finset.card_erase_add_one hab, D.card_neighborFinset_eq_degree]

theorem block_disjoint (tri : triangleFree D) (sq : squareFree D) (a : Fin n) :
    (↑(D.neighborFinset a) : Set (Fin n)).PairwiseDisjoint (block D a) := by
  intro u hu v hv uv
  have au := (D.mem_neighborFinset _ _).mp hu
  have av := (D.mem_neighborFinset _ _).mp hv
  apply Finset.disjoint_left.mpr
  intro t ht ht'
  rcases Finset.mem_insert.mp ht with rfl | ht
  · rcases Finset.mem_insert.mp ht' with eq | h
    · exact uv eq
    · exact tri a _ _ av au ((D.mem_neighborFinset _ _).mp (Finset.mem_erase.mp h).2)
  · obtain ⟨ta,ut⟩ := Finset.mem_erase.mp ht
    rcases Finset.mem_insert.mp ht' with rfl | ht'
    · exact tri a _ _ au av ((D.mem_neighborFinset _ _).mp ut)
    · obtain ⟨_,vt⟩ := Finset.mem_erase.mp ht'
      exact ta (sq u v t a uv ((D.mem_neighborFinset _ _).mp ut) ((D.mem_neighborFinset _ _).mp vt) au.symm av.symm)

theorem local_degree (tri : triangleFree D) (sq : squareFree D) (a : Fin n)
    (S : Finset (Fin n)) (incl : ∀ v ∈ D.support, v ∈ S) (inS : a ∈ S) :
    ∑ b ∈ D.neighborFinset a, D.degree b ≤ S.card - 1 := by
  have sub : (D.neighborFinset a).biUnion (block D a) ⊆ S.erase a := by
    intro t ht
    obtain ⟨b,hb,ht⟩ := Finset.mem_biUnion.mp ht
    have ab := (D.mem_neighborFinset _ _).mp hb
    rcases Finset.mem_insert.mp ht with rfl | h
    · exact Finset.mem_erase.mpr ⟨ab.ne.symm, incl _ ⟨a,ab.symm⟩⟩
    · obtain ⟨ta,bt⟩ := Finset.mem_erase.mp h
      exact Finset.mem_erase.mpr ⟨ta, incl t ⟨b,((D.mem_neighborFinset _ _).mp bt).symm⟩⟩
  have count := Finset.card_le_card sub
  rw [Finset.card_biUnion (block_disjoint D tri sq a), Finset.card_erase_of_mem inS] at count
  simpa only [Finset.sum_congr rfl (fun b hb => block_card D ((D.mem_neighborFinset _ _).mp hb))] using count

#print axioms local_degree
end Simlowker.Residual1735

/-! ## Summing the local degree inequalities -/

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
namespace Simlowker.Residual1735
variable {n : Nat} (D : SimpleGraph (Fin n)) [DecidableRel D.Adj]

theorem girth_local (h : ∀ a : Fin n, ∀ p : D.Walk a a, p.IsCycle → 5 ≤ p.length) :
    triangleFree D ∧ squareFree D := by
  constructor
  · intro a b c ab ac bc
    let p := SimpleGraph.Walk.cons ab (.cons bc (.cons ac.symm .nil))
    have hp : p.IsCycle := by
      dsimp only [p]
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      simp [SimpleGraph.Walk.isPath_def, Sym2.eq_iff, ab.ne, ab.ne.symm, ac.ne, ac.ne.symm,
        bc.ne, bc.ne.symm]
    have absurd := h a p hp
    change 5 ≤ 3 at absurd
    omega
  · intro u v x y uv ux vx uy vy
    by_contra xy
    let p := SimpleGraph.Walk.cons ux (.cons vx.symm (.cons vy (.cons uy.symm .nil)))
    have hp : p.IsCycle := by
      dsimp only [p]
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      simp [SimpleGraph.Walk.isPath_def, Sym2.eq_iff, uv, Ne.symm uv, xy, Ne.symm xy,
        ux.ne, ux.ne.symm, vx.ne, vx.ne.symm, vy.ne, vy.ne.symm, uy.ne, uy.ne.symm]
    have absurd := h u p hp
    change 5 ≤ 4 at absurd
    omega

theorem global_degree (tri : triangleFree D) (sq : squareFree D) :
    (2 * D.edgeFinset.card)^2 ≤ D.support.ncard^2 * (D.support.ncard-1) := by
  classical
  let S := D.support.toFinset
  have memS (v : Fin n) (hv : v ∈ D.support) : v ∈ S := Set.mem_toFinset.mpr hv
  have sn : S.card = D.support.ncard := by simp [S, Set.ncard_eq_toFinset_card']
  have filt (a : Fin n) : S.filter (D.Adj a) = D.neighborFinset a := by
    ext b
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    exact ⟨And.right, fun h => ⟨memS b ⟨a,h.symm⟩,h⟩⟩
  have swap (a b : Fin n) : (if D.Adj a b then D.degree b else 0) =
    (if D.Adj b a then D.degree b else 0) := by
    by_cases h : D.Adj a b
    · simp [h,h.symm]
    · have hn : ¬ D.Adj b a := fun h2 => h h2.symm
      simp [h,hn]
  have localSum : ∑ a ∈ S, ∑ b ∈ D.neighborFinset a, D.degree b ≤ S.card*(S.card-1) :=
    calc
      _ ≤ ∑ _a ∈ S, (S.card-1) := Finset.sum_le_sum (fun a ha => local_degree D tri sq a S memS ha)
      _ = _ := by simp
  have double : (∑ a ∈ S, ∑ b ∈ D.neighborFinset a, D.degree b) = ∑ b ∈ S, D.degree b ^ 2 := by
    calc
      _ = ∑ a ∈ S, ∑ b ∈ S, if D.Adj a b then D.degree b else 0 := by
        apply Finset.sum_congr rfl; intro a _
        rw [← Finset.sum_filter,filt]
      _ = ∑ b ∈ S, ∑ a ∈ S, if D.Adj b a then D.degree b else 0 := by
        rw [Finset.sum_comm]; simp_rw [swap]
      _ = _ := by
        apply Finset.sum_congr rfl; intro b _
        rw [← Finset.sum_filter,filt]; simp [pow_two]
  rw [double] at localSum
  have cs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:Nat)) (fun v => D.degree v)
  simp only [one_mul,one_pow,Finset.sum_const, Nat.nsmul_eq_mul, mul_one] at cs
  have sumEq : ∑ v ∈ S, D.degree v = 2 * D.edgeFinset.card := D.sum_degrees_support_eq_twice_card_edges
  rw [sumEq] at cs
  calc _ ≤ _ := cs
       _ ≤ S.card * (S.card*(S.card-1)) := Nat.mul_le_mul_left _ localSum
       _ = _ := by rw [sn]; ring

#print axioms global_degree
end Simlowker.Residual1735

/-! ## A bound without top form -/

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
namespace Simlowker.Residual1735

/-- An unconditional size-dependent bound on all residual edges. -/
theorem fractional_bound (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (girth : ∀ a : Fin n, ∀ p : G.Walk a a, p.IsCycle → 5 ≤ p.length)
    (least : IsLeastAO G C) :
    (2 * (Ustar G C).card)^2 ≤ (C.size+1)^2 * C.size := by
  classical
  let D := G.deleteEdges (starEdges G C : Set (Sym2 (Fin n)))
  have sub : D ≤ G := G.deleteEdges_le _
  obtain ⟨gt,gs⟩ := girth_local G girth
  have dt : triangleFree D := fun a b c ab ac bc => gt a b c (sub ab) (sub ac) (sub bc)
  have ds : squareFree D := fun u v x y uv ux vx uy vy =>
    gs u v x y uv (sub ux) (sub vx) (sub uy) (sub vy)
  have support : D.support ⊆ G.support := by
    rintro v ⟨w,h⟩
    exact ⟨w,sub h⟩
  have size := (Set.ncard_le_ncard support).trans (PEqualNP.Outside.L_meta_2074 n G C least)
  have count : D.edgeFinset.card = (Ustar G C).card := by simp [D,Ustar,SimpleGraph.edgeFinset_deleteEdges]
  have bound := global_degree D dt ds
  rw [count] at bound
  exact bound.trans (Nat.mul_le_mul (Nat.pow_le_pow_left size 2) (by omega))

#print axioms fractional_bound
end Simlowker.Residual1735

/-! ## Peeling residual graphs at an arbitrary degree threshold -/

namespace Simlowker.Residual1735
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
/-- Threshold version of the peeling argument from R_meta_1735_5. -/
theorem dense_core (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (least : IsLeastAO G C) (d : Nat)
    (many : 2*(d*(C.size+1)) < (Ustar G C).card) :
    ∃ H : SimpleGraph (Fin n), H ≤ G.deleteEdges (starEdges G C : Set (Sym2 (Fin n))) ∧
      (∀ v, (H.neighborSet v).ncard = 0 ∨ d+1 ≤ (H.neighborSet v).ncard) ∧
      d*(C.size+1) < H.edgeSet.ncard := by
  classical
  have edgeCount (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] :
      F.edgeSet.ncard = F.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset,Set.ncard_coe_finset]
  have peel (p : ℕ) : ∀ (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      F.support.ncard = p →
      ∃ H : SimpleGraph (Fin n), H ≤ F ∧
        (∀ v : Fin n, (H.neighborSet v).ncard = 0 ∨ d+1 ≤ (H.neighborSet v).ncard) ∧
        F.edgeSet.ncard ≤ H.edgeSet.ncard + d * p := by
    induction p using Nat.strong_induction_on with
    | ind p smaller =>
      intro F _ hF
      by_cases h : ∀ v : Fin n, (F.neighborSet v).ncard = 0 ∨ d+1 ≤ (F.neighborSet v).ncard
      · exact ⟨F,le_rfl,h,by omega⟩
      · push Not at h
        obtain ⟨v,hv0,hv2⟩ := h
        have hDeg := F.ncard_neighborSet v
        have hvPos : 0 < F.degree v := by omega
        have hv : v ∈ F.support := by
          by_contra hn
          have hz : F.neighborSet v = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro w hw
            exact hn ⟨w,hw⟩
          exact hv0 (by rw [hz,Set.ncard_empty])
        have hPpos : 0 < F.support.ncard := by
          rw [← Set.fintypeCard_eq_ncard]
          exact Fintype.card_pos_iff.mpr ⟨⟨v,hv⟩⟩
        let R := F.deleteIncidenceSet v
        have hDrop : R.support.ncard ≤ F.support.ncard - 1 := by
          simpa only [Set.fintypeCard_eq_ncard] using F.card_support_deleteIncidenceSet hv
        obtain ⟨H,hHR,hMin,hH⟩ := smaller R.support.ncard (by omega) R rfl
        refine ⟨H,hHR.trans (F.deleteIncidenceSet_le v),hMin,?_⟩
        have hRemoved : R.edgeFinset.card = F.edgeFinset.card - F.degree v :=
          F.card_edgeFinset_deleteIncidenceSet v
        have hLe : F.degree v ≤ F.edgeFinset.card := by
          rw [← F.card_incidenceFinset_eq_degree v]
          exact Finset.card_le_card (F.incidenceFinset_subset v)
        have paid : d * R.support.ncard + d ≤ d * p := by
          rw [←Nat.mul_succ]
          exact Nat.mul_le_mul_left _ (by omega)
        rw [edgeCount R] at hH
        rw [edgeCount F]
        omega
  let D := G.deleteEdges (starEdges G C : Set (Sym2 (Fin n)))
  obtain ⟨H,hHD,hMin,hPeel⟩ := peel D.support.ncard D rfl
  have hsub : D.support ⊆ G.support := by
    rintro v ⟨w,h⟩
    exact ⟨w,(G.deleteEdges_le _) h⟩
  have hs := (Set.ncard_le_ncard hsub).trans (PEqualNP.Outside.L_meta_2074 n G C least)
  have ev : D.edgeSet.ncard = (Ustar G C).card := by
    rw [edgeCount D]; simp [D,Ustar,SimpleGraph.edgeFinset_deleteEdges]
  rw [ev] at hPeel
  have spent := Nat.mul_le_mul_left d hs
  exact ⟨H,hHD,hMin,by omega⟩
#print axioms dense_core
end Simlowker.Residual1735
