import Mathlib.Tactic
import PEqualNP.Defs

namespace SparseIncidence
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def incidences (N : Nat) (I : Fin N → Fin N → Prop) [DecidableRel I] :=
  (List.finRange N).flatMap fun p => ((List.finRange N).filter fun l => decide (I p l)).map
    fun l => (p.val,N+l.val)

def normal (N : Nat) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (G : SimpleGraph (Fin (N+N))) [DecidableRel G.Adj] (D : Circuit) : Prop :=
  IsLeastAO G D ∧ PEqualNP.Core.IsLiftFixedPoint G D ∧
    (∀ k < D.gates.length, (gateAt D k).op = .and → ∀ t∈(gateAt D k).inputs,
      ¬(∀ x : Fin (N+N) → Bool, (Circuit.mk D.gates t).eval (List.ofFn x)=true →
          graphFun G ∅ x=true)) ∧ PEqualNP.FactorSubst.liveSize (N+N) D = D.size ∧
     PEqualNP.ReadK.doubleReread D (N+N) (fun i => decide (N ≤ i)) (incidences N I) = []

def compatible (N : Nat) (I : Fin N → Fin N → Prop) (G : SimpleGraph (Fin (N+N))) :=
  ∀ u v, G.Adj u v ↔ ∃ p l : Fin N, I p l ∧
    ((u=Fin.castAdd N p ∧ v=Fin.natAdd N l) ∨ (u=Fin.natAdd N l ∧ v=Fin.castAdd N p))

theorem empty_normal (N : Nat) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (G : SimpleGraph (Fin (N+N))) [DecidableRel G.Adj] (edges : compatible N I G)
    (empty : ∀ p l, ¬I p l) : normal N I G ⟨[],N+N⟩ := by
  have noadj (u v) : ¬G.Adj u v := by
    intro adj
    obtain ⟨p,l,h,_⟩ := (edges u v).mp adj
    exact empty p l h
  have noedges : incidences N I=[] := by simp [incidences,empty]
  constructor
  · refine ⟨?_,?_,?_⟩
    · simp [IsAO2,PEqualNP.EdgeOwnership.AndOrOnly,ReadsBack]
    · funext x
      simp [circuitFun,Circuit.eval,Circuit.wires,graphFun,noadj,List.getD_eq_getElem?_getD]
    · intro D _ _
      exact Nat.zero_le _
  · simp [PEqualNP.Core.IsLiftFixedPoint,PEqualNP.Core.LiftApplies,PEqualNP.FactorSubst.liveSize,
      PEqualNP.FactorSubst.liveGates,Circuit.size,noedges,PEqualNP.ReadK.doubleReread]

#print axioms empty_normal
end SparseIncidence
