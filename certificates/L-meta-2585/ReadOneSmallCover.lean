import Mathlib
import PEqualNP.Defs


/-
Read-one replacement for incidence graphs covered by two vertices.
A partial result for L-meta-2585. The proof combines prior project work with the support and four-vertex path bounds and the covering arguments below.
The read-one star construction is the public L_meta_7684, copied from the Apache-2.0 project.
The definitions cross and graph are from L_meta_4897 of the same project.
Upstream revision a4bbd50801b635c41ce4ad600130b085b838a81a.
-/

namespace IncidenceBudget

abbrev Sig := Finset Nat × Nat
def join (a b : Sig) : Sig := (a.1 ∪ b.1,a.2+b.2)
def cover (A : Finset Sig) := A.biUnion Prod.fst
def cost (A : Finset Sig) := ∑ a ∈ A, a.2

def Budget (k : Nat) (P : Finset Sig) := ∀ A ⊆ P,
  (cover A).card ≤ k+A.card ∧ (k+A.card ≤ (cover A).card → cost A ≤ (cover A).card)

theorem initial {P : Finset Sig} (base : ∀ a∈P, a.1.card≤a.2 ∧ a.2≤1) : Budget 0 P := by
  intro A h
  have x : (cover A).card≤cost A := Finset.card_biUnion_le.trans (Finset.sum_le_sum fun a ha => (base a (h ha)).1)
  have y : cost A ≤ A.card := by
    calc
      (∑ a ∈ A, a.2) ≤ ∑ _a ∈ A, 1 := Finset.sum_le_sum (fun a ha => (base a (h ha)).2)
      _ = A.card := by simp
  constructor
  · exact x.trans (by omega)
  · omega

theorem extend {P : Finset Sig} {k : Nat} (h : Budget k P) {a b : Sig}
    (ha : a∈P) (hb : b∈P) : Budget (k+1) (insert (join a b) P) := by
  intro A sub
  let c := join a b
  by_cases hc : c∈A
  · let B := A.erase c
    let Q := insert a (insert b B)
    have Bsub : B⊆P := by
      intro v hv
      have hh := sub (Finset.mem_erase.mp hv).2
      simpa [c,(Finset.mem_erase.mp hv).1] using hh
    have Qsub : Q⊆P := Finset.insert_subset ha (Finset.insert_subset hb Bsub)
    have ce : insert c B=A := Finset.insert_erase hc
    have ne : c∉B := Finset.notMem_erase _ _
    have eq : cover A=cover Q := by
      rw [←ce]
      simp [cover,Q,c,join,Finset.union_assoc]
    have cb : A.card=B.card+1 := by rw [←ce,Finset.card_insert_of_notMem ne]
    have bound := h Q Qsub
    have upper : Q.card ≤ B.card+2 := by
      have := Finset.card_insert_le a (insert b B)
      have := Finset.card_insert_le b B
      dsimp [Q]; omega
    rw [eq]
    constructor
    · omega
    · intro tight
      have separate : a∉insert b B := by
        intro bad
        have same : Q=insert b B := Finset.insert_eq_of_mem bad
        have small := Finset.card_insert_le b B
        rw [same] at bound tight
        omega
      have single : b∉B := by
        intro bad
        have same : Q=insert a B := by simp [Q,Finset.insert_eq_of_mem bad]
        have small := Finset.card_insert_le a B
        rw [same] at bound tight
        omega
      have costs : cost A=cost Q := by
        rw [←ce]
        unfold cost
        rw [Finset.sum_insert ne]
        dsimp only [Q]
        rw [Finset.sum_insert separate,Finset.sum_insert single]
        change a.2+b.2+_=a.2+(b.2+_)
        omega
      rw [costs]
      apply bound.2
      omega
  · have sub' : A⊆P := by
      intro v hv
      rcases Finset.mem_insert.mp (sub hv) with e|h'
      · exact False.elim (hc (by simpa [c,e] using hv))
      · exact h'
    have hh := (h A sub').1
    exact ⟨by omega,by omega⟩

end IncidenceBudget

namespace IncidenceBudget

inductive Tree where
  | dead
  | var (i : Nat)
  | node (isAnd : Bool) (a b : Tree)

def sig : Tree → Sig
  | .dead => (∅,0)
  | .var i => ({i},1)
  | .node _ a b => join (sig a) (sig b)

def op (d a b : Bool) := if d then a && b else a || b
def linop (d : Bool) (a b : Bool × Bool) : Bool × Bool :=
  if d then (a.1 && b.1,(a.1 && b.2) || (a.2 && b.1)) else (a.1 || b.1,a.2 || b.2)

def ev (x : Nat → Bool) : Tree → Bool
  | .dead => false
  | .var i => x i
  | .node d a b => op d (ev x a) (ev x b)

def lin (mark x : Nat → Bool) : Tree → Bool × Bool
  | .dead => (false,false)
  | .var i => if mark i then (false,x i) else (x i,false)
  | .node d a b => linop d (lin mark x a) (lin mark x b)

theorem card_le (e : Tree) : (sig e).1.card≤(sig e).2 := by
  induction e with
  | dead => rfl
  | var i => simp [sig]
  | node d a b ia ib => exact (Finset.card_union_le ..).trans (Nat.add_le_add ia ib)

theorem ev_agree (e : Tree) {x y : Nat → Bool} (h : ∀ i∈(sig e).1,x i=y i) : ev x e=ev y e := by
  induction e with
  | dead => rfl
  | var i => exact h i (Finset.mem_singleton_self _)
  | node d a b ia ib =>
    exact congrArg₂ (op d) (ia fun i hi => h i (Finset.mem_union_left _ hi))
      (ib fun i hi => h i (Finset.mem_union_right _ hi))

theorem constant_part (e : Tree) (m x : Nat → Bool) :
    (lin m x e).1=ev (fun i => x i && !m i) e := by
  induction e with
  | dead => rfl
  | var i => cases h : m i <;> simp [lin,ev,h]
  | node d a b ia ib => cases d <;> simp [lin,ev,linop,op,ia,ib]

theorem constant_when {e : Tree} {m x : Nat → Bool} {i : Nat}
    (active : ∀ j, m j=true → x j=true → j=i) (out : i∉(sig e).1) :
    (lin m x e).1=ev x e := by
  rw [constant_part]
  apply ev_agree
  intro j hj
  cases hm : m j <;> cases hx : x j <;> simp
  exact False.elim (out ((active j hm hx) ▸ hj))

theorem linear_when_tight (e : Tree) (m x : Nat → Bool) (i : Nat)
    (active : ∀ j, m j=true → x j=true → j=i) (tight : (sig e).2≤(sig e).1.card) :
    ((lin m x e).1 || (lin m x e).2) = ev x e := by
  induction e with
  | dead => rfl
  | var j => cases h : m j <;> simp [lin,ev,h]
  | node d a b ia ib =>
    have ha := card_le a
    have hb := card_le b
    change (sig a).2+(sig b).2 ≤ ((sig a).1 ∪ (sig b).1).card at tight
    have hu := Finset.card_union_le (sig a).1 (sig b).1
    have dis := Finset.card_union_eq_card_add_card.mp (show ((sig a).1∪(sig b).1).card =
        (sig a).1.card+(sig b).1.card by omega)
    have aa := ia (by omega)
    have bb := ib (by omega)
    have alone : i∉(sig a).1 ∨ i∉(sig b).1 := by
      by_cases h : i∈(sig a).1
      · exact Or.inr (fun h' => Finset.disjoint_left.mp dis h h')
      · exact Or.inl h
    have clean : (lin m x a).1=ev x a ∨ (lin m x b).1=ev x b :=
      alone.imp (constant_when active) (constant_when active)
    have law : ∀ (d : Bool) (a b : Bool × Bool), (a.1=(a.1||a.2) ∨ b.1=(b.1||b.2)) →
        ((linop d a b).1 || (linop d a b).2) = op d (a.1||a.2) (b.1||b.2) := by decide +kernel
    rw [←aa,←bb] at clean
    exact (law d _ _ clean).trans (congrArg₂ (op d) aa bb)

end IncidenceBudget

namespace IncidenceBudget
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.ReadK

def raw (n : Nat) := (List.range n).map Tree.var
def rows (n : Nat) (x : Nat → Bool) := (List.range n).map x
def read (ws : List Tree) (g : Gate) (k : Nat) := ws.getD (g.inputs.getD k 0) .dead
def binary (g : Gate) : Bool := match g.op with | .and => true | _ => false
def produce (ws : List Tree) (g : Gate) := Tree.node (binary g) (read ws g 0) (read ws g 1)
def advance (ws : List Tree) (g : Gate) := ws++[produce ws g]
def output (n : Nat) (C : Circuit) := (C.gates.foldl advance (raw n)).getD C.output .dead
def pool (ws : List Tree) : Finset Sig := insert (sig .dead) (ws.map sig).toFinset
def good (g : Gate) := (g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2

theorem in_pool (ws : List Tree) (i) : sig (ws.getD i .dead)∈pool ws := by
  by_cases hi : i<ws.length
  · apply Finset.mem_insert_of_mem
    apply List.mem_toFinset.mpr
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
    exact List.mem_map.mpr ⟨_,List.getElem_mem hi,rfl⟩
  · rw [List.getD_eq_default _ _ (by omega)]; exact Finset.mem_insert_self _ _

theorem source_budget (n : Nat) : Budget 0 (pool (raw n)) := by
  apply initial
  intro v hv
  rcases Finset.mem_insert.mp hv with e|h
  · subst v; simp [sig]
  · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht
    simp [sig]

theorem budget_fold (gs : List Gate) (ws : List Tree) (t : Nat) (h : Budget t (pool ws)) :
    Budget (t+gs.length) (pool (gs.foldl advance ws)) := by
  induction gs generalizing ws t with
  | nil => simpa using h
  | cons g gs ih =>
    have h' := extend h (in_pool ws (g.inputs.getD 0 0)) (in_pool ws (g.inputs.getD 1 0))
    have eqP : pool (advance ws g) = insert (sig (produce ws g)) (pool ws) := by
      ext v; simp [pool,advance,or_left_comm]
    rw [List.foldl_cons]
    have eqN : t+(g::gs).length=t+1+gs.length := by simp; omega
    rw [eqN]
    apply ih
    rw [eqP]
    exact h'

theorem output_budget (n : Nat) (C : Circuit) :
    (sig (output n C)).1.card ≤ C.size+1 ∧
      (C.size+1 ≤ (sig (output n C)).1.card → (sig (output n C)).2 ≤ (sig (output n C)).1.card) := by
  have h := budget_fold C.gates (raw n) 0 (source_budget n)
  have hh := h {sig (output n C)} (Finset.singleton_subset_iff.mpr (in_pool _ C.output))
  simpa [cover,cost,Circuit.size] using hh

theorem map_fold {α : Type} (f : Tree → α) (q : List α → Gate → α) (std : List Gate)
    (ok : ∀ g∈std,good g) (ws : List Tree)
    (eq : ∀ v g,good g → f (produce v g)=q (v.map f) g) :
    (std.foldl advance ws).map f=std.foldl (fun v g => v++[q v g]) (ws.map f) := by
  induction std generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,List.foldl_cons,ih (fun a ha => ok a (List.mem_cons_of_mem _ ha))]
    simp [advance,eq _ g (ok g List.mem_cons_self)]

theorem project_ev (n : Nat) (C : Circuit) (h : IsAO2 n C) (x : Nat → Bool) :
    ev x (output n C)=C.eval (rows n x) := by
  let st := fun (ws : List Bool) (g : Gate) => g.op.eval (g.inputs.map fun i => ws.getD i false)
  have one (ws : List Tree) (g : Gate) (ok : good g) : ev x (produce ws g)=st (ws.map (ev x)) g := by
    obtain ⟨op',two⟩ := ok
    obtain ⟨a,b,ab⟩ := List.length_eq_two.mp two
    have rd (i) : (ws.map (ev x)).getD i false=ev x (ws.getD i .dead) :=
      List.getD_map (l:=ws) (n:=i) (d:=Tree.dead) (ev x)
    rcases op' with hh|hh <;> simp only [st,produce,read,binary,op,ev,ab,hh,GateOp.eval,List.getD_cons_zero,List.getD_cons_succ,
      List.map_cons,List.map_nil,rd] <;> simp
  have p := map_fold (ev x) st C.gates (fun g hg => ⟨h.1 g hg,h.2.2 g hg⟩) (raw n) one
  have init : (raw n).map (ev x)=rows n x := by simp [raw,rows,List.map_map,Function.comp_def,ev]
  rw [init] at p
  have readOut := List.getD_map (l:=C.gates.foldl advance (raw n)) (n:=C.output) (d:=Tree.dead) (ev x)
  rw [p] at readOut
  exact readOut.symm

def lst (ws : List (Bool × Bool)) (g : Gate) : Bool × Bool :=
  let ins := g.inputs.map fun i => ws.getD i (false,false)
  match g.op with
  | .or  => (ins.any (·.1),ins.any (·.2))
  | .and => ins.foldl (fun (acc : Bool × Bool) p =>
      (acc.1 && p.1,(acc.1 && p.2) || (acc.2 && p.1))) (true,false)
  | _ => (false,false)

theorem project_lin (n : Nat) (C : Circuit) (h : IsAO2 n C) (mark x : Nat → Bool) :
    lin mark x (output n C)=(linearParts C mark (rows n x)).getD C.output (false,false) := by
  have one (ws : List Tree) (g : Gate) (ok : good g) :
      lin mark x (produce ws g)=lst (ws.map (lin mark x)) g := by
    obtain ⟨ops,two⟩ := ok
    obtain ⟨a,b,ab⟩ := List.length_eq_two.mp two
    have rd (i) : (ws.map (lin mark x)).getD i (false,false)=lin mark x (ws.getD i .dead) :=
      List.getD_map (l:=ws) (n:=i) (d:=Tree.dead) (lin mark x)
    rcases ops with hh|hh <;> simp only [produce,read,ab,List.getD_cons_zero,List.getD_cons_succ,
      lin,binary,hh,lst,List.map_cons,List.map_nil,rd,linop,List.foldl_cons,List.foldl_nil,List.any_cons,
      List.any_nil] <;> simp
  have p := map_fold (lin mark x) lst C.gates (fun g hg => ⟨h.1 g hg,h.2.2 g hg⟩) (raw n) one
  have init : (raw n).map (lin mark x)=((rows n x).zipIdx).map
      (fun (z,i) => if mark i then (false,z) else (z,false)) := by
    apply List.ext_getElem
    · simp [raw,rows]
    · intro j hl hr
      simp [raw,rows,lin,List.getElem_zipIdx]
  rw [init] at p
  have readOut := List.getD_map (l:=C.gates.foldl advance (raw n)) (n:=C.output) (d:=Tree.dead) (lin mark x)
  rw [p] at readOut
  exact readOut.symm

end IncidenceBudget


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

end SparseIncidence

namespace IncidenceBudget
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.ReadK SparseIncidence

def used {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Finset Nat :=
  (Finset.univ.filter fun v : Fin n => ∃ w,G.Adj v w).image Fin.val

theorem computed {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (ao : IsAO2 n C) (works : circuitFun n C=graphFun G ∅) (x : Nat → Bool) :
    ev x (output n C)=graphFun G ∅ (fun i => x i.val) := by
  rw [project_ev n C ao]
  have listEq : rows n x=List.ofFn (fun i : Fin n => x i.val) := by
    apply List.ext_getElem <;> simp [rows]
  rw [listEq]
  exact congrFun works _

def pair (u v j : Nat) := (j==u) || (j==v)
def one (v j : Nat) := j==v

theorem edge_on {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} (edge : G.Adj u v) : graphFun G ∅ (fun i => pair u.val v.val i.val)=true := by
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq]
  exact ⟨u,v,edge,by simp [pair],by simp [pair]⟩

theorem single_off {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : Nat) :
    graphFun G ∅ (fun i => one p i.val)=false := by
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_false_iff_not]
  rintro ⟨a,b,adj,ha,hb⟩
  have eq : a=b := Fin.ext ((beq_iff_eq.mp ha).trans (beq_iff_eq.mp hb).symm)
  subst b
  exact G.irrefl adj

theorem support_contains {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (ao : IsAO2 n C) (works : circuitFun n C=graphFun G ∅) :
    used G ⊆ (sig (output n C)).1 := by
  intro j hj
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hj
  obtain ⟨v,edge⟩ := (Finset.mem_filter.mp hu).2
  by_contra missing
  have eq : ev (pair u.val v.val) (output n C)=ev (one v.val) (output n C) := by
    apply ev_agree
    intro i hi
    have ne : i≠u.val := fun e => missing (e ▸ hi)
    simp [pair,one,ne]
  rw [computed ao works,computed ao works,edge_on edge,single_off] at eq
  contradiction

theorem support_lower {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (ao : IsAO2 n C) (works : circuitFun n C=graphFun G ∅) : (used G).card≤C.size+1 :=
  (Finset.card_le_card (support_contains ao works)).trans (output_budget n C).1

theorem tight_single {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (ao : IsAO2 n C) (works : circuitFun n C=graphFun G ∅) (tight : C.size+1≤(used G).card)
    (m : Nat → Bool) {u v : Fin n} (edge : G.Adj u v) (mu : m u=false) (mv : m v=true) :
    lineSingle C n m u v=true := by
  let e := output n C
  let x := pair u.val v.val
  have treeTight := (output_budget n C).2 (tight.trans (Finset.card_le_card (support_contains ao works)))
  have active (j) (hm : m j=true) (hx : x j=true) : j=v.val := by
    rcases Bool.or_eq_true_iff.mp hx with h|h
    · have eq : j=u := beq_iff_eq.mp h
      rw [eq,mu] at hm; contradiction
    · exact beq_iff_eq.mp h
  have table := linear_when_tight e m x v.val active treeTight
  have mask : (fun j => x j && !m j)=one u.val := by
    funext j
    by_cases hu : j=u.val
    · subst j; simp [x,pair,one,mu]
    · by_cases hv : j=v.val
      · subst j; simp [x,pair,one,mv,hu]
      · simp [x,pair,one,beq_eq_false_iff_ne.mpr hv,beq_eq_false_iff_ne.mpr hu]
  have dead : (lin m x e).1=false := by
    rw [constant_part,mask,computed ao works,single_off]
  have yes : ev x e=true := (computed ao works x).trans (edge_on edge)
  rw [dead,yes,Bool.false_or] at table
  change ((linearParts C m (rows n x)).getD C.output (false,false)).2=true
  rw [←project_lin n C ao m x]
  exact table

theorem tight_incidence {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (G : SimpleGraph (Fin (N+N))) [DecidableRel G.Adj] (ok : compatible N I G) (C : Circuit)
    (ao : IsAO2 (N+N) C) (works : circuitFun (N+N) C=graphFun G ∅) (tight : C.size+1≤(used G).card) :
    doubleReread C (N+N) (fun i => decide (N ≤ i)) (incidences N I)=[] := by
  apply List.filter_eq_nil_iff.mpr
  intro z hz
  obtain ⟨p,_,hp⟩ := List.mem_flatMap.mp hz
  obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hp
  have edge := (ok (Fin.castAdd N p) (Fin.natAdd N l)).mpr
    ⟨p,l,of_decide_eq_true (List.mem_filter.mp hl).2,Or.inl ⟨rfl,rfl⟩⟩
  have hs := tight_single ao works tight (fun i => decide (N ≤ i)) edge
    (by simp [p.isLt]) (by simp)
  change lineSingle C (N+N) (fun i => decide (N ≤ i)) p.val (N+l.val)=true at hs
  simp [hs]

end IncidenceBudget

namespace IncidenceBudget
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def pairLib : Nat → List Nat
  | 0 => [0, 7, 56, 63]
  | 1 => [0, 2, 5, 7, 16, 21, 23, 40, 42, 47, 56, 58, 61, 63]
  | 2 => [0, 1, 6, 7, 24, 25, 31, 32, 38, 39, 56, 57, 62, 63]
  | 3 => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 16, 17, 20, 21, 22, 23, 24, 25, 26, 27, 29, 31, 32, 34, 36, 37, 38, 39, 40, 41, 42, 43, 46, 47, 48, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
  | _ => []

def bag (a b : Bool) := pairLib (a.toNat+2*b.toNat)
theorem closure : ∀ a b c d : Bool, ¬(a=true ∧ c=true) → ¬(b=true ∧ d=true) →
    ∀ v∈bag a b, ∀ w∈bag c d, v &&& w∈bag (a||c) (b||d) ∧ v ||| w∈bag (a||c) (b||d) := by
  decide +kernel

def pack (rs : List Nat) (f : Nat → Bool) := rs.foldr (fun r n => Nat.bit (f r) n) 0
theorem pack_op (rs : List Nat) (d : Bool) (f g : Nat → Bool) :
    pack rs (fun r => op d (f r) (g r)) =
      if d then pack rs f &&& pack rs g else pack rs f ||| pack rs g := by
  induction rs with
  | nil => cases d <;> simp [pack]
  | cons a rs ih => cases d <;> simp [pack,op,List.foldr_cons,Nat.land_bit,Nat.lor_bit] at ih ⊢ <;> rw [ih]

def vword (u v s t j : Nat) :=
  if j=u then 21 else if j=v then 38 else if j=s ∨ j=t then 56 else 0
def word (u v s t : Nat) (e : Tree) :=
  pack [0,1,2,3,4,5] (fun r => ev (fun j => (vword u v s t j).testBit r) e)

theorem word_bound (u v s t : Nat) (uv : u≠v) (e : Tree) (tight : (sig e).2≤(sig e).1.card) :
    word u v s t e ∈ bag (decide (u∈(sig e).1)) (decide (v∈(sig e).1)) := by
  induction e with
  | dead => change 0 ∈ bag false false; decide +kernel
  | var j =>
    simp only [sig,Finset.mem_singleton,word,ev,vword]
    by_cases ju : j=u
    · subst j
      simp only [ite_true,decide_true,ite_false,uv,Ne.symm uv,decide_false]
      decide +kernel
    · by_cases jv : j=v
      · subst j
        simp only [ite_true,ite_false,decide_true,decide_false,ju,Ne.symm ju]
        decide +kernel
      · by_cases rest : j=s ∨ j=t
        all_goals simp only [ite_true,ite_false,ju,jv,Ne.symm ju,Ne.symm jv,rest,decide_false]
        all_goals decide +kernel
  | node d a b ia ib =>
    have ha := card_le a
    have hb := card_le b
    change (sig a).2+(sig b).2≤((sig a).1∪(sig b).1).card at tight
    have upper := Finset.card_union_le (sig a).1 (sig b).1
    have dis := Finset.card_union_eq_card_add_card.mp (show ((sig a).1∪(sig b).1).card =
        (sig a).1.card+(sig b).1.card by omega)
    have sep (k : Nat) : ¬(decide (k∈(sig a).1)=true ∧ decide (k∈(sig b).1)=true) := by
      rintro ⟨ak,bk⟩
      exact Finset.disjoint_left.mp dis (of_decide_eq_true ak) (of_decide_eq_true bk)
    have p := closure _ _ _ _ (sep u) (sep v) _ (ia (by omega)) _ (ib (by omega))
    have eq : word u v s t (.node d a b)=
        (if d then word u v s t a &&& word u v s t b else word u v s t a ||| word u v s t b) :=
      pack_op _ d _ _
    rw [eq]
    have decOr (A B : Prop) [Decidable A] [Decidable B] : decide (A ∨ B) = (decide A || decide B) := by by_cases h : A <;> simp [h]
    simp only [sig,join,Finset.mem_union,decOr]
    cases d
    · exact p.2
    · exact p.1

end IncidenceBudget

namespace IncidenceBudget
open PEqualNP.MetaComplexity.NestedCover

-- Fix an outside input. A monotone computation that sees the inside only
-- through one Boolean signal is constant, or is the signal itself.
theorem unary_id (h : Bool → Bool) (nz : h false ≠ h true) (mono : h false=true → h true=true) :
    h=id := by
  funext b
  cases a : h false <;> cases c : h true <;> cases b <;> simp_all

def restrictTo {n : Nat} (S : Finset (Fin n)) (x : Fin n → Bool) (i : Fin n) :=
  x i && decide (i∈S)
def exterior {n : Nat} (S : Finset (Fin n)) (x : Fin n → Bool) (i : Fin n) :=
  x i && decide (i∉S)

def OnePort {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) :=
  ∃ (z : (Fin n → Bool) → Bool) (h : (Fin n → Bool) → Bool → Bool),
    (∀ y, h y false=true → h y true=true) ∧
    ∀ x, graphFun G ∅ x = h (exterior S x) (z (restrictTo S x))

def combine {n : Nat} (S : Finset (Fin n)) (i o : Fin n → Bool) (v : Fin n) :=
  if v∈S then i v else o v

theorem port_cofactor {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {S : Finset (Fin n)}
    (port : OnePort G S) (a b : Fin n → Bool)
    (ca : ∃ i j, graphFun G ∅ (combine S i a)≠graphFun G ∅ (combine S j a))
    (cb : ∃ i j, graphFun G ∅ (combine S i b)≠graphFun G ∅ (combine S j b)) :
    ∀ i, graphFun G ∅ (combine S i a)=graphFun G ∅ (combine S i b) := by
  obtain ⟨z,h,m,rep⟩ := port
  have fg (i o) : graphFun G ∅ (combine S i o)=h (exterior S o) (z (restrictTo S i)) := by
    rw [rep]
    congr 1
    · funext v; by_cases hv : v∈S <;> simp [exterior,combine,hv]
    · congr 1; funext v; by_cases hv : v∈S <;> simp [restrictTo,combine,hv]
  have idAt (o : Fin n → Bool) (varies : ∃ i j, graphFun G ∅ (combine S i o)≠graphFun G ∅ (combine S j o)) :
      h (exterior S o)=id := by
    obtain ⟨i,j,ne⟩ := varies
    rw [fg,fg] at ne
    apply unary_id _ _ (m _)
    by_contra eq
    cases h1 : z (restrictTo S i) <;> cases h2 : z (restrictTo S j) <;> simp_all
  intro i
  rw [fg,fg,idAt a ca,idAt b cb]

theorem graph_pair {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a b : Fin n) :
    graphFun G ∅ (fun k => (k==a) || (k==b)) = decide (G.Adj a b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq,
    Bool.or_eq_true_iff,beq_iff_eq]
  constructor
  · rintro ⟨v,w,e,hv,hw⟩
    rcases hv with rfl|rfl <;> rcases hw with rfl|rfl <;> first | exact e | exact e.symm | exact False.elim (G.irrefl e)
  · intro e; exact ⟨a,b,e,Or.inl rfl,Or.inr rfl⟩

theorem port_separates {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {S : Finset (Fin n)}
    (port : OnePort G S) {a b : Fin n} (ha : a∈S) (hb : b∈S) (edge : G.Adj a b)
    {u v : Fin n} (hu : u∈S) (hv : v∉S) : ¬G.Adj u v := by
  intro cross
  let O : Fin n → Bool := fun _ => false
  let sing (i : Fin n) : Fin n → Bool := fun j => j==i
  let dbl (i j : Fin n) : Fin n → Bool := fun k => (k==i) || (k==j)
  have sep (x y : Fin n → Bool) (sx : ∀ j,x j=true → j∈S) (sy : ∀ j,y j=true → j∉S) :
      combine S x y = fun j => x j || y j := by
    funext j
    by_cases hj : j∈S
    · have e : y j=false := by cases h : y j <;> simp_all
      simp [combine,hj,e]
    · have e : x j=false := by cases h : x j <;> simp_all
      simp [combine,hj,e]
  have s0 : ∀ j,O j=true → j∈S := by simp [O]
  have o0 : ∀ j,O j=true → j∉S := by simp [O]
  have ou : ∀ j,sing u j=true → j∈S := by simpa [sing] using hu
  have ov : ∀ j,sing v j=true → j∉S := by simpa [sing] using hv
  have sab : ∀ j,dbl a b j=true → j∈S := by
    intro j h
    rcases Bool.or_eq_true_iff.mp h with l|r
    · exact beq_iff_eq.mp l ▸ ha
    · exact beq_iff_eq.mp r ▸ hb
  have off (t : Fin n) : graphFun G ∅ (sing t)=false := by
    have e := graph_pair G t t
    simp [sing] at e ⊢
    exact e
  have f00 : graphFun G ∅ (combine S O O)=false := by simp [combine,O,graphFun]
  have fab : graphFun G ∅ (combine S (dbl a b) O)=true := by
    rw [sep _ _ sab o0]; simpa [O,dbl] using (graph_pair G a b).trans (decide_eq_true edge)
  have f0v : graphFun G ∅ (combine S O (sing v))=false := by
    rw [sep _ _ s0 ov]; simpa [O] using off v
  have fuv : graphFun G ∅ (combine S (sing u) (sing v))=true := by
    rw [sep _ _ ou ov]; exact (graph_pair G u v).trans (decide_eq_true cross)
  have fu0 : graphFun G ∅ (combine S (sing u) O)=false := by
    rw [sep _ _ ou o0]; simpa [O] using off u
  have eq := port_cofactor port O (sing v) ⟨O,dbl a b,by rw [f00,fab]; decide⟩ ⟨O,sing u,by rw [f0v,fuv]; decide⟩ (sing u)
  rw [fu0,fuv] at eq
  contradiction

end IncidenceBudget

namespace IncidenceBudget
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

theorem graph_hit {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool)
    {a b : Fin n} (e : G.Adj a b) (ha : x a=true) (hb : x b=true) : graphFun G ∅ x=true := by
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq]
  exact ⟨a,b,e,ha,hb⟩

theorem p4_budget {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (works : circuitFun n C=graphFun G ∅)
    {u v s t : Fin n} (uv : G.Adj u v) (us : G.Adj u s) (vt : G.Adj v t)
    (sv : s≠v) (tu : t≠u) (st : ¬ G.Adj s t) : (used G).card≤C.size := by
  by_contra! small
  have tight := (output_budget n C).2 ((show C.size+1≤(used G).card by omega).trans
    (Finset.card_le_card (support_contains ao works)))
  let X := fun (r j : Nat) => (vword u.val v.val s.val t.val j).testBit r
  have vu : v.val≠u.val := fun eq => uv.ne (Fin.ext eq.symm)
  have su : s.val≠u.val := fun eq => us.ne (Fin.ext eq.symm)
  have tv : t.val≠v.val := fun eq => vt.ne (Fin.ext eq.symm)
  have sv' : s.val≠v.val := fun eq => sv (Fin.ext eq)
  have tu' : t.val≠u.val := fun eq => tu (Fin.ext eq)
  let encode (a b c : Bool) : Nat := if a then 21 else if b then 38 else if c then 56 else 0
  have lookup : ∀ a b c : Bool, ¬(a=true ∧ b=true) → ¬(a=true ∧ c=true) → ¬(b=true ∧ c=true) →
      (encode a b c).testBit 0=a ∧ (encode a b c).testBit 1=b ∧
      (encode a b c).testBit 2=(a||b) ∧ (encode a b c).testBit 3=c := by decide +kernel
  have point (j : Nat) : X 0 j=one u.val j ∧ X 1 j=one v.val j ∧
      X 2 j=pair u.val v.val j ∧ X 3 j=pair s.val t.val j := by
    have eq : vword u.val v.val s.val t.val j=encode (j==u.val) (j==v.val) ((j==s.val)||(j==t.val)) := by
      simp only [vword,encode,Bool.or_eq_true_iff,beq_iff_eq]
    unfold X
    rw [eq]
    apply lookup <;> simp only [Bool.or_eq_true_iff,beq_iff_eq] <;> grind
  have rows : X 0=one u.val ∧ X 1=one v.val ∧ X 2=pair u.val v.val ∧ X 3=pair s.val t.val :=
    ⟨funext (fun j => (point j).1),funext (fun j => (point j).2.1),
      funext (fun j => (point j).2.2.1),funext (fun j => (point j).2.2.2)⟩
  let e := output n C
  have a0 : ev (X 0) e=false := by rw [rows.1,computed ao works,single_off]
  have a1 : ev (X 1) e=false := by rw [rows.2.1,computed ao works,single_off]
  have a2 : ev (X 2) e=true := by rw [rows.2.2.1,computed ao works,edge_on uv]
  have a3 : ev (X 3) e=false := by
    rw [rows.2.2.2,computed ao works]
    change graphFun G ∅ (fun j => (j==s) || (j==t))=false
    rw [graph_pair]; exact decide_eq_false st
  have a4 : ev (X 4) e=true := by
    rw [computed ao works]
    apply graph_hit G _ us
    · simp [X,vword] <;> decide +kernel
    · simp [X,vword,su,sv'] <;> decide +kernel
  have a5 : ev (X 5) e=true := by
    rw [computed ao works]
    apply graph_hit G _ vt
    · simp [X,vword,vu] <;> decide +kernel
    · simp [X,vword,tu',tv] <;> decide +kernel
  have w := word_bound u.val v.val s.val t.val vu.symm e tight
  have exactWord : word u.val v.val s.val t.val e=52 := by
    change pack [0,1,2,3,4,5] (fun r => ev (X r) e)=52
    simp only [pack,List.foldr_cons,List.foldr_nil,a0,a1,a2,a3,a4,a5]
    decide +kernel
  rw [exactWord] at w
  have reject : ∀ a b : Bool, 52∉bag a b := by decide +kernel
  exact reject _ _ w

end IncidenceBudget


namespace PEqualNP.Outside.L_meta_7684

namespace A3692

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

private def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_stepW_len (gs : List Gate) (inp : List Bool) :
    (gs.foldl stepW inp).length = inp.length + gs.length := by
  induction gs generalizing inp with
  | nil => simp
  | cons g rest ih =>
    simp [List.foldl, stepW, ih]
    omega

private lemma wires_eq_foldl (C : Circuit) (inp : List Bool) :
    C.wires inp = C.gates.foldl stepW inp := rfl

private lemma wires_len (C : Circuit) (inp : List Bool) :
    (C.wires inp).length = inp.length + C.gates.length := by
  simpa [wires_eq_foldl] using foldl_stepW_len C.gates inp

private lemma getD_append_left (l1 l2 : List Bool) (i : ℕ) (hi : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_append_self (l1 : List Bool) (b : Bool) :
    (l1 ++ [b]).getD l1.length false = b := by
  simp [List.getD]

private lemma getD_of_ge (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD, List.getElem?_eq_none hi]

private lemma getD_ofFn {n : ℕ} (z : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn z).getD i false = z ⟨i, hi⟩ := by
  simp [List.getD, hi]

private def wireVal (n : ℕ) (gs : List Gate) (z : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl stepW (List.ofFn z)).getD i false

private lemma wireVal_append_gate_lt (n : ℕ) (gs : List Gate) (g : Gate) (z : Fin n → Bool)
    (i : ℕ) (hi : i < n + gs.length) :
    wireVal n (gs ++ [g]) z i = wireVal n gs z i := by
  unfold wireVal
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen : (gs.foldl stepW (List.ofFn z)).length = n + gs.length := by
    rw [foldl_stepW_len, List.length_ofFn]
  exact getD_append_left _ _ i (by omega)

private lemma wireVal_append_gate_self (n : ℕ) (gs : List Gate) (g : Gate) (z : Fin n → Bool) :
    wireVal n (gs ++ [g]) z (n + gs.length) =
      g.op.eval (g.inputs.map (fun i => wireVal n gs z i)) := by
  unfold wireVal
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen : (gs.foldl stepW (List.ofFn z)).length = n + gs.length := by
    rw [foldl_stepW_len, List.length_ofFn]
  rw [← hlen]
  exact getD_append_self (gs.foldl stepW (List.ofFn z)) _

private def gateAtL (gs : List Gate) (j : ℕ) : Gate :=
  gs.getD j ⟨GateOp.or, []⟩

private lemma gateAtL_append_lt (gs : List Gate) (g : Gate) (j : ℕ) (hj : j < gs.length) :
    gateAtL (gs ++ [g]) j = gateAtL gs j := by
  simp [gateAtL, List.getD, List.getElem?_append_left hj]

private lemma gateAtL_append_self (gs : List Gate) (g : Gate) :
    gateAtL (gs ++ [g]) gs.length = g := by
  simp [gateAtL, List.getD]

private def Good (x1 x2 : ℕ) (S : Bool → Finset ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ j < gs.length, ∀ i ∈ (gateAtL gs j).inputs, i < x1 + x2 + j) ∧
  (∀ b : Bool, ∀ w ∈ S b, w < x1 + x2 + gs.length) ∧
  (∀ b : Bool, ∀ w ∈ S b,
    (w < x1 + x2 ∧ decide (x1 ≤ w) = b) ∨
    ∃ j < gs.length, w = x1 + x2 + j ∧ (gateAtL gs j).op = GateOp.or ∧
      ∀ u ∈ (gateAtL gs j).inputs, u ∈ S b) ∧
  (∀ j < gs.length, (gateAtL gs j).op = GateOp.and →
    ∃ a c : ℕ, (gateAtL gs j).inputs = [a, c] ∧ a ∈ S false ∧ c ∈ S true)

private def S0 (x1 x2 : ℕ) (b : Bool) : Finset ℕ :=
  if b then Finset.Ico x1 (x1 + x2) else Finset.range x1

private lemma good_init (x1 x2 : ℕ) : Good x1 x2 (S0 x1 x2) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg; cases hg
  · intro j hj; simp at hj
  · intro b w hw
    cases b <;> simp [S0] at hw <;> omega
  · intro b w hw
    left
    cases b <;> simp [S0] at hw
    · exact ⟨by omega, by simp [show ¬(x1 ≤ w) by omega]⟩
    · exact ⟨hw.2, by simp [hw.1]⟩
  · intro j hj; simp at hj

private lemma mem_S0_false {x1 x2 : ℕ} (p : Fin x1) : p.1 ∈ S0 x1 x2 false := by
  simp [S0, p.2]

private lemma mem_S0_true {x1 x2 : ℕ} (l : Fin x2) : x1 + l.1 ∈ S0 x1 x2 true := by
  simp [S0]

private lemma good_append_or_side {x1 x2 : ℕ} {S : Bool → Finset ℕ} {gs : List Gate}
    (hG : Good x1 x2 S gs) (b : Bool) {u v : ℕ} (hu : u ∈ S b) (hv : v ∈ S b) :
    let w := x1 + x2 + gs.length
    let S' : Bool → Finset ℕ := fun b' => if b' = b then insert w (S b') else S b'
    Good x1 x2 S' (gs ++ [⟨GateOp.or, [u, v]⟩]) := by
  rcases hG with ⟨hAO, hRB, hLt, hSide, hAnd⟩
  have hu_lt : u < x1 + x2 + gs.length := hLt b u hu
  have hv_lt : v < x1 + x2 + gs.length := hLt b v hv
  dsimp only
  have hSub : ∀ b' : Bool, S b' ⊆ (if b' = b then insert (x1 + x2 + gs.length) (S b') else S b') := by
    intro b'
    by_cases hbb : b' = b
    · simp [hbb]
    · simp [hbb]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO g hg
    · exact ⟨Or.inr rfl, rfl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hi
      exact hRB j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro b' w hw
    simp only [List.length_append, List.length_singleton]
    by_cases hbb : b' = b
    · simp only [hbb, ite_true, Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · omega
      · have := hLt b w hw; omega
    · simp only [hbb, ite_false] at hw
      have := hLt b' w hw; omega
  · intro b' w hw
    by_cases hbb : b' = b
    · subst hbb
      simp only [ite_true, Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · right
        refine ⟨gs.length, by simp, rfl, ?_, ?_⟩
        · rw [gateAtL_append_self]
        · rw [gateAtL_append_self]
          intro t ht
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl
          · exact hSub b' hu
          · exact hSub b' hv
      · rcases hSide b' w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
        · exact Or.inl h1
        · right
          refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
          · rw [gateAtL_append_lt _ _ _ hj]; exact hop
          · rw [gateAtL_append_lt _ _ _ hj]
            intro t ht
            exact hSub b' (hin t ht)
    · simp only [hbb, ite_false] at hw
      rcases hSide b' w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
      · exact Or.inl h1
      · right
        refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
        · rw [gateAtL_append_lt _ _ _ hj]; exact hop
        · rw [gateAtL_append_lt _ _ _ hj]
          intro t ht
          simp only [hbb, ite_false]
          exact hin t ht
  · intro j hj hop
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hop ⊢
      rcases hAnd j hlt hop with ⟨a, c, hin, ha, hc⟩
      exact ⟨a, c, hin, hSub false ha, hSub true hc⟩
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hop
      cases hop

private lemma good_append_or_top {x1 x2 : ℕ} {S : Bool → Finset ℕ} {gs : List Gate}
    (hG : Good x1 x2 S gs) {u v : ℕ} (hu : u < x1 + x2 + gs.length) (hv : v < x1 + x2 + gs.length) :
    Good x1 x2 S (gs ++ [⟨GateOp.or, [u, v]⟩]) := by
  rcases hG with ⟨hAO, hRB, hLt, hSide, hAnd⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO g hg
    · exact ⟨Or.inr rfl, rfl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hi
      exact hRB j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro b w hw
    simp only [List.length_append, List.length_singleton]
    have := hLt b w hw; omega
  · intro b w hw
    rcases hSide b w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
    · exact Or.inl h1
    · right
      refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
      · rw [gateAtL_append_lt _ _ _ hj]; exact hop
      · rw [gateAtL_append_lt _ _ _ hj]; exact hin
  · intro j hj hop
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hop ⊢
      exact hAnd j hlt hop
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hop
      cases hop

private lemma good_append_and {x1 x2 : ℕ} {S : Bool → Finset ℕ} {gs : List Gate}
    (hG : Good x1 x2 S gs) {a c : ℕ} (ha : a ∈ S false) (hc : c ∈ S true) :
    Good x1 x2 S (gs ++ [⟨GateOp.and, [a, c]⟩]) := by
  rcases hG with ⟨hAO, hRB, hLt, hSide, hAnd⟩
  have ha_lt : a < x1 + x2 + gs.length := hLt false a ha
  have hc_lt : c < x1 + x2 + gs.length := hLt true c hc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO g hg
    · exact ⟨Or.inl rfl, rfl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hi
      exact hRB j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro b' w hw
    simp only [List.length_append, List.length_singleton]
    have := hLt b' w hw; omega
  · intro b' w hw
    rcases hSide b' w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
    · exact Or.inl h1
    · right
      refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
      · rw [gateAtL_append_lt _ _ _ hj]; exact hop
      · rw [gateAtL_append_lt _ _ _ hj]; exact hin
  · intro j hj hop
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hop ⊢
      exact hAnd j hlt hop
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self]
      exact ⟨a, c, rfl, ha, hc⟩

private lemma addOrInSide {x1 x2 : ℕ} (b : Bool) (ws : List ℕ) (hne : ws ≠ []) :
    ∀ (S : Bool → Finset ℕ) (gs : List Gate),
      Good x1 x2 S gs →
      (∀ u ∈ ws, u ∈ S b) →
      ∃ (S' : Bool → Finset ℕ) (gs' : List Gate) (w : ℕ),
        gs'.length = gs.length + (ws.length - 1) ∧
        Good x1 x2 S' gs' ∧
        (∀ b', S b' ⊆ S' b') ∧
        w ∈ S' b ∧
        (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
        (∀ z, wireVal (x1 + x2) gs' z w = ws.any (fun u => wireVal (x1 + x2) gs z u)) := by
  induction ws with
  | nil => exact absurd rfl hne
  | cons u rest ih =>
    intro S gs hG hws
    cases rest with
    | nil =>
      refine ⟨S, gs, u, by simp, hG, fun _ => Finset.Subset.rfl, hws u (by simp), ?_, ?_⟩
      · intro z i _; rfl
      · intro z; simp
    | cons v rest' =>
      have hne' : v :: rest' ≠ [] := List.cons_ne_nil v rest'
      have hws' : ∀ t ∈ v :: rest', t ∈ S b := fun t ht => hws t (List.mem_cons_of_mem u ht)
      rcases ih hne' S gs hG hws' with ⟨S1, gs1, w1, hlen1, hG1, hSub1, hw1, hPres1, hVal1⟩
      have hu1 : u ∈ S1 b := hSub1 b (hws u (by simp))
      let w := x1 + x2 + gs1.length
      let gs2 := gs1 ++ [⟨GateOp.or, [u, w1]⟩]
      let S2 : Bool → Finset ℕ := fun b' => if b' = b then insert w (S1 b') else S1 b'
      have hG2 : Good x1 x2 S2 gs2 := good_append_or_side hG1 b hu1 hw1
      have hSub2 : ∀ b', S b' ⊆ S2 b' := by
        intro b'
        refine Finset.Subset.trans (hSub1 b') ?_
        by_cases hbb : b' = b
        · simp [S2, hbb]
        · simp [S2, hbb]
      have hw2 : w ∈ S2 b := by simp [S2]
      have hu_lt : u < x1 + x2 + gs.length := hG.2.2.1 b u (hws u (by simp))
      refine ⟨S2, gs2, w, ?_, hG2, hSub2, hw2, ?_, ?_⟩
      · simp [gs2, hlen1]; omega
      · intro z i hi
        have hi1 : i < x1 + x2 + gs1.length := by omega
        rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
        exact hPres1 z i hi
      · intro z
        rw [wireVal_append_gate_self]
        simp only [List.map, GateOp.eval, List.any_cons]
        rw [hPres1 z u hu_lt, hVal1 z]
        simp

private lemma addOrTop {x1 x2 : ℕ} (ws : List ℕ) (hne : ws ≠ []) :
    ∀ (S : Bool → Finset ℕ) (gs : List Gate),
      Good x1 x2 S gs →
      (∀ u ∈ ws, u < x1 + x2 + gs.length) →
      ∃ (gs' : List Gate) (w : ℕ),
        gs'.length = gs.length + (ws.length - 1) ∧
        Good x1 x2 S gs' ∧
        w < x1 + x2 + gs'.length ∧
        (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
        (∀ z, wireVal (x1 + x2) gs' z w = ws.any (fun u => wireVal (x1 + x2) gs z u)) := by
  induction ws with
  | nil => exact absurd rfl hne
  | cons u rest ih =>
    intro S gs hG hws
    cases rest with
    | nil =>
      refine ⟨gs, u, by simp, hG, hws u (by simp), ?_, ?_⟩
      · intro z i _; rfl
      · intro z; simp
    | cons v rest' =>
      have hne' : v :: rest' ≠ [] := List.cons_ne_nil v rest'
      have hws' : ∀ t ∈ v :: rest', t < x1 + x2 + gs.length :=
        fun t ht => hws t (List.mem_cons_of_mem u ht)
      rcases ih hne' S gs hG hws' with ⟨gs1, w1, hlen1, hG1, hw1, hPres1, hVal1⟩
      have hu_lt : u < x1 + x2 + gs.length := hws u (by simp)
      have hu1 : u < x1 + x2 + gs1.length := by omega
      let w := x1 + x2 + gs1.length
      let gs2 := gs1 ++ [⟨GateOp.or, [u, w1]⟩]
      have hG2 : Good x1 x2 S gs2 := good_append_or_top hG1 hu1 hw1
      refine ⟨gs2, w, ?_, hG2, ?_, ?_, ?_⟩
      · simp [gs2, hlen1]; omega
      · simp [gs2, w]
      · intro z i hi
        have hi1 : i < x1 + x2 + gs1.length := by omega
        rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
        exact hPres1 z i hi
      · intro z
        rw [wireVal_append_gate_self]
        simp only [List.map, GateOp.eval, List.any_cons]
        rw [hPres1 z u hu_lt, hVal1 z]
        simp

private abbrev Star (x1 x2 : ℕ) := (Fin x1 × List (Fin x2)) ⊕ (Fin x2 × List (Fin x1))

private def starSize {x1 x2 : ℕ} : Star x1 x2 → ℕ
  | Sum.inl (_, ls) => ls.length
  | Sum.inr (_, ps) => ps.length

private def starEval {x1 x2 : ℕ} (z : Fin (x1 + x2) → Bool) : Star x1 x2 → Bool
  | Sum.inl (p, ls) => z (Fin.castAdd x2 p) && ls.any (fun l => z (Fin.natAdd x1 l))
  | Sum.inr (l, ps) => ps.any (fun p => z (Fin.castAdd x2 p)) && z (Fin.natAdd x1 l)

private lemma wireVal_input_left {x1 x2 : ℕ} (gs : List Gate) (z : Fin (x1 + x2) → Bool)
    (p : Fin x1) :
    wireVal (x1 + x2) gs z p.1 = z (Fin.castAdd x2 p) := by
  induction gs using List.reverseRecOn with
  | nil =>
    unfold wireVal
    simp only [List.foldl_nil]
    have hlt : p.1 < x1 + x2 := by omega
    rw [getD_ofFn z p.1 hlt]
    rfl
  | append_singleton gs g ih =>
    rw [wireVal_append_gate_lt _ _ _ _ _ (by omega)]
    exact ih

private lemma wireVal_input_right {x1 x2 : ℕ} (gs : List Gate) (z : Fin (x1 + x2) → Bool)
    (l : Fin x2) :
    wireVal (x1 + x2) gs z (x1 + l.1) = z (Fin.natAdd x1 l) := by
  induction gs using List.reverseRecOn with
  | nil =>
    unfold wireVal
    simp only [List.foldl_nil]
    have hlt : x1 + l.1 < x1 + x2 := by omega
    rw [getD_ofFn z (x1 + l.1) hlt]
    rfl
  | append_singleton gs g ih =>
    rw [wireVal_append_gate_lt _ _ _ _ _ (by omega)]
    exact ih

private lemma addStar {x1 x2 : ℕ} (st : Star x1 x2) (hpos : 0 < starSize st)
    (S : Bool → Finset ℕ) (gs : List Gate)
    (hG : Good x1 x2 S gs) (hBase : ∀ b, S0 x1 x2 b ⊆ S b) :
    ∃ (S' : Bool → Finset ℕ) (gs' : List Gate) (w : ℕ),
      gs'.length = gs.length + starSize st ∧
      Good x1 x2 S' gs' ∧
      (∀ b, S b ⊆ S' b) ∧
      w < x1 + x2 + gs'.length ∧
      (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
      (∀ z, wireVal (x1 + x2) gs' z w = starEval z st) := by
  cases st with
  | inl pl =>
    rcases pl with ⟨p, ls⟩
    have hne_ls : ls ≠ [] := by
      intro h; simp [starSize, h] at hpos
    let ws : List ℕ := ls.map (fun l => x1 + l.1)
    have hne_ws : ws ≠ [] := by
      simp [ws, hne_ls]
    have hws_mem : ∀ u ∈ ws, u ∈ S true := by
      intro u hu
      simp only [ws, List.mem_map] at hu
      rcases hu with ⟨l, _, rfl⟩
      exact hBase true (mem_S0_true l)
    rcases addOrInSide true ws hne_ws S gs hG hws_mem with
      ⟨S1, gs1, wL, hlen1, hG1, hSub1, hwL, hPres1, hVal1⟩
    have hp1 : p.1 ∈ S1 false := hSub1 false (hBase false (mem_S0_false p))
    let w := x1 + x2 + gs1.length
    let gs2 := gs1 ++ [⟨GateOp.and, [p.1, wL]⟩]
    have hG2 : Good x1 x2 S1 gs2 := good_append_and hG1 hp1 hwL
    refine ⟨S1, gs2, w, ?_, hG2, hSub1, ?_, ?_, ?_⟩
    · simp only [gs2, List.length_append, List.length_singleton, hlen1, ws, List.length_map,
        starSize]
      have : 0 < ls.length := by simpa [starSize] using hpos
      omega
    · simp [gs2, w]
    · intro z i hi
      have hi1 : i < x1 + x2 + gs1.length := by omega
      rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
      exact hPres1 z i hi
    · intro z
      rw [wireVal_append_gate_self]
      simp only [List.map, GateOp.eval, starEval]
      rw [wireVal_input_left, hVal1 z]
      simp only [ws, List.any_map]
      have hfn : (fun l : Fin x2 => wireVal (x1 + x2) gs z (x1 + l.1)) =
          (fun l : Fin x2 => z (Fin.natAdd x1 l)) := by
        funext l
        exact wireVal_input_right gs z l
      simp [Function.comp_def, hfn]
  | inr lp =>
    rcases lp with ⟨l, ps⟩
    have hne_ps : ps ≠ [] := by
      intro h; simp [starSize, h] at hpos
    let ws : List ℕ := ps.map (fun p => p.1)
    have hne_ws : ws ≠ [] := by
      simp [ws, hne_ps]
    have hws_mem : ∀ u ∈ ws, u ∈ S false := by
      intro u hu
      simp only [ws, List.mem_map] at hu
      rcases hu with ⟨p, _, rfl⟩
      exact hBase false (mem_S0_false p)
    rcases addOrInSide false ws hne_ws S gs hG hws_mem with
      ⟨S1, gs1, wP, hlen1, hG1, hSub1, hwP, hPres1, hVal1⟩
    have hl1 : x1 + l.1 ∈ S1 true := hSub1 true (hBase true (mem_S0_true l))
    let w := x1 + x2 + gs1.length
    let gs2 := gs1 ++ [⟨GateOp.and, [wP, x1 + l.1]⟩]
    have hG2 : Good x1 x2 S1 gs2 := good_append_and hG1 hwP hl1
    refine ⟨S1, gs2, w, ?_, hG2, hSub1, ?_, ?_, ?_⟩
    · simp only [gs2, List.length_append, List.length_singleton, hlen1, ws, List.length_map,
        starSize]
      have : 0 < ps.length := by simpa [starSize] using hpos
      omega
    · simp [gs2, w]
    · intro z i hi
      have hi1 : i < x1 + x2 + gs1.length := by omega
      rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
      exact hPres1 z i hi
    · intro z
      rw [wireVal_append_gate_self]
      simp only [List.map, GateOp.eval, starEval]
      rw [wireVal_input_right, hVal1 z]
      simp only [ws, List.any_map]
      have hfn : (fun p : Fin x1 => wireVal (x1 + x2) gs z p.1) =
          (fun p : Fin x1 => z (Fin.castAdd x2 p)) := by
        funext p
        exact wireVal_input_left gs z p
      simp [Function.comp_def, hfn]

private lemma addStars {x1 x2 : ℕ} (stars : List (Star x1 x2))
    (hpos : ∀ st ∈ stars, 0 < starSize st) :
    ∀ (S : Bool → Finset ℕ) (gs : List Gate),
      Good x1 x2 S gs →
      (∀ b, S0 x1 x2 b ⊆ S b) →
      ∃ (S' : Bool → Finset ℕ) (gs' : List Gate) (ws : List ℕ),
        gs'.length = gs.length + (stars.map starSize).sum ∧
        ws.length = stars.length ∧
        Good x1 x2 S' gs' ∧
        (∀ w ∈ ws, w < x1 + x2 + gs'.length) ∧
        (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
        (∀ z, ws.any (fun w => wireVal (x1 + x2) gs' z w) = stars.any (fun st => starEval z st)) := by
  induction stars with
  | nil =>
    intro S gs hG _
    refine ⟨S, gs, [], by simp, rfl, hG, by simp, ?_, ?_⟩
    · intro z i _; rfl
    · intro z; simp
  | cons st rest ih =>
    intro S gs hG hBase
    rcases addStar st (hpos st (by simp)) S gs hG hBase with
      ⟨S1, gs1, w1, hlen1, hG1, hSub1, hw1, hPres1, hVal1⟩
    have hBase1 : ∀ b, S0 x1 x2 b ⊆ S1 b := fun b => Finset.Subset.trans (hBase b) (hSub1 b)
    have hpos_rest : ∀ s ∈ rest, 0 < starSize s := fun s hs => hpos s (List.mem_cons_of_mem st hs)
    rcases ih hpos_rest S1 gs1 hG1 hBase1 with
      ⟨S2, gs2, ws2, hlen2, hwslen2, hG2, hws2_lt, hPres2, hVal2⟩
    refine ⟨S2, gs2, w1 :: ws2, ?_, ?_, hG2, ?_, ?_, ?_⟩
    · simp [hlen2, hlen1, Nat.add_assoc]
    · simp [hwslen2]
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · omega
      · exact hws2_lt w hw
    · intro z i hi
      have hi1 : i < x1 + x2 + gs1.length := by omega
      rw [hPres2 z i hi1]
      exact hPres1 z i hi
    · intro z
      simp only [List.any_cons]
      rw [hPres2 z w1 hw1, hVal1 z, hVal2 z]

private lemma circuit_from_good {x1 x2 : ℕ} (S : Bool → Finset ℕ) (gs : List Gate) (out : ℕ)
    (hG : Good x1 x2 S gs) :
    let C : Circuit := ⟨gs, out⟩
    IsAO2 (x1 + x2) C ∧
    (∀ b : Bool, ∀ w ∈ S b,
      (w < x1 + x2 ∧ decide (x1 ≤ w) = b) ∨
      ∃ j < C.size, w = x1 + x2 + j ∧ (gateAt C j).op = GateOp.or ∧
        ∀ u ∈ (gateAt C j).inputs, u ∈ S b) ∧
    (∀ j < C.size, (gateAt C j).op = GateOp.and →
      ∃ a c : ℕ, (gateAt C j).inputs = [a, c] ∧ a ∈ S false ∧ c ∈ S true) := by
  rcases hG with ⟨hAO, hRB, _, hSide, hAnd⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg; exact (hAO g hg).1
  · intro j hj i hi; exact hRB j hj i hi
  · intro g hg; exact (hAO g hg).2
  · intro b w hw; exact hSide b w hw
  · intro j hj hop; exact hAnd j hj hop

end A3692

open A3692 in
theorem t3692 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)),   (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) →     ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : Bool → Finset ℕ),       PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧         x7.size ≤ x3.card + x4.card + x5.card - (1 : ℕ) ∧           (∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), (x10, x11) ∈ x3 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) ∧             have x9 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x7;             (∀ (x10 : Bool), ∀ x11 ∈ x8 x10, x11 < x1 + x2 ∧ Decidable.decide (x1 ≤ x11) = x10 ∨ ∃ x13 < x7.size, x11 = x1 + x2 + x13 ∧ (x9 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x14 ∈ (x9 x13).inputs, x14 ∈ x8 x10) ∧ ∀ x10 < x7.size, (x9 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ), (x9 x10).inputs = [x13, x14] ∧ x13 ∈ x8 Bool.false ∧ x14 ∈ x8 Bool.true := by
  intro x1 x2 E A B hcov
  by_cases hE : E = ∅
  · subst hE
    refine ⟨⟨[], x1 + x2⟩, fun _ => ∅, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro g hg; cases hg
      · intro j hj; simp at hj
      · intro g hg; cases hg
    · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
    · intro z
      simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
        PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_nil, Finset.notMem_empty,
        false_and, exists_false, decide_false]
      exact getD_of_ge (List.ofFn z) (x1 + x2) (by simp)
    · intro b w hw; simp at hw
    · intro j hj; simp [PEqualNP.CircuitLowerBounds.Circuit.size] at hj
  · have hE_ne : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hE
    let NA : Fin x1 → Finset (Fin x2) := fun p => Finset.univ.filter (fun l => (p, l) ∈ E)
    let NB : Fin x2 → Finset (Fin x1) := fun l => Finset.univ.filter (fun p => (p, l) ∈ E ∧ p ∉ A)
    let A' : Finset (Fin x1) := A.filter (fun p => (NA p).Nonempty)
    let B' : Finset (Fin x2) := B.filter (fun l => (NB l).Nonempty)
    let starsA : List (Star x1 x2) := A'.toList.map (fun p => Sum.inl (p, (NA p).toList))
    let starsB : List (Star x1 x2) := B'.toList.map (fun l => Sum.inr (l, (NB l).toList))
    let stars : List (Star x1 x2) := starsA ++ starsB
    have hpos : ∀ st ∈ stars, 0 < starSize st := by
      intro st hst
      simp only [stars, starsA, starsB, List.mem_append, List.mem_map, Finset.mem_toList] at hst
      rcases hst with ⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩
      · simp only [starSize, Finset.length_toList]
        exact Finset.card_pos.mpr (Finset.mem_filter.mp hp).2
      · simp only [starSize, Finset.length_toList]
        exact Finset.card_pos.mpr (Finset.mem_filter.mp hl).2
    have hsumA : (starsA.map starSize).sum = ∑ p ∈ A', (NA p).card := by
      have h1 : (starsA.map starSize) = A'.toList.map (fun p => (NA p).card) := by
        simp [starsA, starSize, Function.comp_def]
      rw [h1, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
      rfl
    have hsumB : (starsB.map starSize).sum = ∑ l ∈ B', (NB l).card := by
      have h1 : (starsB.map starSize) = B'.toList.map (fun l => (NB l).card) := by
        simp [starsB, starSize, Function.comp_def]
      rw [h1, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
      rfl
    have hcardE : (∑ p ∈ A', (NA p).card) + (∑ l ∈ B', (NB l).card) = E.card := by
      let EA : Finset (Fin x1 × Fin x2) := A'.biUnion (fun p => (NA p).image (fun l => (p, l)))
      let EB : Finset (Fin x1 × Fin x2) := B'.biUnion (fun l => (NB l).image (fun p => (p, l)))
      have hEA_card : EA.card = ∑ p ∈ A', (NA p).card := by
        rw [Finset.card_biUnion]
        · refine Finset.sum_congr rfl ?_
          intro p _
          exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
        · intro p1 _ p2 _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro e he1 he2
          simp only [Finset.mem_image] at he1 he2
          rcases he1 with ⟨l1, _, rfl⟩
          rcases he2 with ⟨l2, _, heq⟩
          exact hne (Prod.mk.inj heq).1.symm
      have hEB_card : EB.card = ∑ l ∈ B', (NB l).card := by
        rw [Finset.card_biUnion]
        · refine Finset.sum_congr rfl ?_
          intro l _
          exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)
        · intro l1 _ l2 _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro e he1 he2
          simp only [Finset.mem_image] at he1 he2
          rcases he1 with ⟨p1, _, rfl⟩
          rcases he2 with ⟨p2, _, heq⟩
          exact hne (Prod.mk.inj heq).2.symm
      have hdisj : Disjoint EA EB := by
        rw [Finset.disjoint_left]
        intro e he1 he2
        simp only [EA, EB, Finset.mem_biUnion, Finset.mem_image] at he1 he2
        rcases he1 with ⟨p1, hp1, l1, _, rfl⟩
        rcases he2 with ⟨l2, _, p2, hp2, heq⟩
        have hp_eq : p2 = p1 := (Prod.mk.inj heq).1
        subst hp_eq
        have hp1A : p2 ∈ A := (Finset.mem_filter.mp hp1).1
        have hp2nA : p2 ∉ A := (Finset.mem_filter.mp hp2).2.2
        exact hp2nA hp1A
      have hunion : EA ∪ EB = E := by
        ext ⟨p, l⟩
        simp only [EA, EB, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
        constructor
        · rintro (⟨p1, _, l1, hl1, heq⟩ | ⟨l1, _, p1, hp1, heq⟩)
          · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
            exact (Finset.mem_filter.mp hl1).2
          · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
            exact (Finset.mem_filter.mp hp1).2.1
        · intro hpl
          by_cases hpA : p ∈ A
          · left
            refine ⟨p, Finset.mem_filter.mpr ⟨hpA, ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩⟩⟩,
              l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩, rfl⟩
          · right
            have hlB : l ∈ B := (hcov (p, l) hpl).resolve_left hpA
            refine ⟨l, Finset.mem_filter.mpr ⟨hlB, ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩⟩⟩,
              p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩, rfl⟩
      rw [← hEA_card, ← hEB_card, ← Finset.card_union_of_disjoint hdisj, hunion]
    have hsum_stars : (stars.map starSize).sum = E.card := by
      simp only [stars, List.map_append, List.sum_append, hsumA, hsumB, hcardE]
    have hstars_len : stars.length = A'.card + B'.card := by
      simp [stars, starsA, starsB]
    have hstars_ne : stars ≠ [] := by
      intro hnil
      have h0 : E.card = 0 := by
        rw [← hsum_stars, hnil]; rfl
      exact (Finset.card_pos.mpr hE_ne).ne' h0
    rcases addStars stars hpos (S0 x1 x2) [] (good_init x1 x2) (fun _ => Finset.Subset.rfl) with
      ⟨S1, gs1, ws1, hlen1, hwslen1, hG1, hws1_lt, _, hVal1⟩
    have hws1_ne : ws1 ≠ [] := by
      intro hnil
      apply hstars_ne
      apply List.eq_nil_of_length_eq_zero
      rw [← hwslen1, hnil]
      rfl
    rcases addOrTop ws1 hws1_ne S1 gs1 hG1 hws1_lt with
      ⟨gs2, wOut, hlen2, hG2, _, hPres2, hVal2⟩
    let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs2, wOut⟩
    have hC := circuit_from_good S1 gs2 wOut hG2
    refine ⟨C, S1, hC.1, ?_, ?_, hC.2.1, hC.2.2⟩
    · have hA' : A'.card ≤ A.card := Finset.card_filter_le _ _
      have hB' : B'.card ≤ B.card := Finset.card_filter_le _ _
      have hk_pos : 1 ≤ ws1.length := by
        cases ws1 with
        | nil => exact absurd rfl hws1_ne
        | cons _ _ => simp
      simp only [C, PEqualNP.CircuitLowerBounds.Circuit.size, hlen2, hlen1, List.length_nil,
        Nat.zero_add, hsum_stars, hwslen1, hstars_len]
      omega
    · intro z
      have hcf : PEqualNP.MetaComplexity.circuitFun (x1 + x2) C z = wireVal (x1 + x2) gs2 z wOut := rfl
      rw [hcf, hVal2 z, hVal1 z]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨st, hst, hst_eval⟩
        simp only [stars, starsA, starsB, List.mem_append, List.mem_map, Finset.mem_toList] at hst
        rcases hst with ⟨p, _, rfl⟩ | ⟨l, _, rfl⟩
        · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList] at hst_eval
          rcases hst_eval with ⟨hzp, l, hl, hzl⟩
          exact ⟨p, l, (Finset.mem_filter.mp hl).2, hzp, hzl⟩
        · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList] at hst_eval
          rcases hst_eval with ⟨⟨p, hp, hzp⟩, hzl⟩
          exact ⟨p, l, (Finset.mem_filter.mp hp).2.1, hzp, hzl⟩
      · rintro ⟨p, l, hpl, hzp, hzl⟩
        by_cases hpA : p ∈ A
        · refine ⟨Sum.inl (p, (NA p).toList), ?_, ?_⟩
          · simp only [stars, starsA, List.mem_append, List.mem_map, Finset.mem_toList]
            left
            exact ⟨p, Finset.mem_filter.mpr ⟨hpA, ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩⟩⟩, rfl⟩
          · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList]
            exact ⟨hzp, l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩, hzl⟩
        · have hlB : l ∈ B := (hcov (p, l) hpl).resolve_left hpA
          refine ⟨Sum.inr (l, (NB l).toList), ?_, ?_⟩
          · simp only [stars, starsB, List.mem_append, List.mem_map, Finset.mem_toList]
            right
            exact ⟨l, Finset.mem_filter.mpr ⟨hlB, ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩⟩⟩, rfl⟩
          · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList]
            exact ⟨⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩, hzp⟩, hzl⟩

namespace B6579

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadK PEqualNP.TopForm

def s2230_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma s2230_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl s2230_stepWire x := rfl

lemma s2230_foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl s2230_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2230_stepWire]
    omega

lemma s2230_foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl s2230_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2230_stepWire w g).length := by simp [s2230_stepWire]; omega
    rw [ih (s2230_stepWire w g) hlt]
    simp [s2230_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma s2230_getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma s2230_wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [s2230_wires_eq_foldl, s2230_foldl_stepWire_length, List.length_ofFn]

lemma s2230_split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def s2230_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma s2230_gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma s2230_W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    s2230_W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then s2230_W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := s2230_split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [s2230_gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl s2230_stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, s2230_foldl_stepWire_length, hpre_len]
  have hCj : s2230_W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [s2230_W]
    rw [s2230_wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [s2230_foldl_stepWire_getD_lt post (s2230_stepWire w0 gj) (n + k) (by simp [s2230_stepWire]; omega)]
    simp [s2230_stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [s2230_W]
    rw [s2230_wires_eq_foldl, hgs, List.foldl_append]
    exact (s2230_foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact s2230_getD_ge_length w0 i (by omega)

lemma s2230_W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    s2230_W n C x u = x ⟨u, hu⟩ := by
  simp only [s2230_W]
  rw [s2230_wires_eq_foldl, s2230_foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]


def s2230_FR (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
  | _ => []

def s2230_stepR (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List (List ℕ)) :=
  R ++ [s2230_FR S k R g]

lemma s2230_readVectors_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = C.gates.foldl (s2230_stepR S k) ((List.range n).map (leafVectors S k)) := by
  first
    | rfl
    | (unfold readVectors; congr 1; funext R g; rcases g with ⟨op, ins⟩; cases op <;> rfl)

lemma s2230_FR_or (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) (h : g.op = GateOp.or) :
    s2230_FR S k R g =
      (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) [] := by
  obtain ⟨op, ins⟩ := g
  have h2 : op = GateOp.or := h
  subst h2
  rfl

lemma s2230_FR_and (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate)
    (h : g.op = GateOp.and) :
    s2230_FR S k R g = (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0] := by
  obtain ⟨op, ins⟩ := g
  have h2 : op = GateOp.and := h
  subst h2
  rfl

lemma s2230_foldR_length (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) :
    (gs.foldl (s2230_stepR S k) R).length = R.length + gs.length := by
  induction gs generalizing R with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2230_stepR]
    omega

lemma s2230_foldR_getD_lt (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) (i : ℕ)
    (hi : i < R.length) : (gs.foldl (s2230_stepR S k) R).getD i [] = R.getD i [] := by
  induction gs generalizing R with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2230_stepR S k R g).length := by simp [s2230_stepR]; omega
    rw [ih (s2230_stepR S k R g) hlt]
    simp [s2230_stepR, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def s2230_RV (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) : List (List ℕ) :=
  (readVectors C n S k).getD w []

lemma s2230_RV_input (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) (hw : w < n) :
    s2230_RV C n S k w = leafVectors S k w := by
  simp only [s2230_RV]
  rw [s2230_readVectors_eq, s2230_foldR_getD_lt S k C.gates ((List.range n).map (leafVectors S k)) w
    (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma s2230_RV_gate (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (j : ℕ) (hj : j < C.gates.length) :
    ∃ Rp : List (List (List ℕ)),
      (∀ i, i < n + j → Rp.getD i [] = s2230_RV C n S k i) ∧
      s2230_RV C n S k (n + j) = s2230_FR S k Rp (gateAt C j) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := s2230_split_gates C.gates j hj
  have hga : gateAt C j = gj := by rw [s2230_gateAt_eq C j hj]; exact hgj
  rw [hga]
  obtain ⟨Rp, hRp⟩ : ∃ Rp, Rp = pre.foldl (s2230_stepR S k) ((List.range n).map (leafVectors S k)) :=
    ⟨_, rfl⟩
  have hlen : Rp.length = n + j := by
    rw [hRp, s2230_foldR_length]
    simp only [List.length_map, List.length_range, hpre_len]
  have hall : readVectors C n S k = post.foldl (s2230_stepR S k) (s2230_stepR S k Rp gj) := by
    rw [s2230_readVectors_eq, hgs, List.foldl_append, List.foldl_cons, hRp]
  have hlen1 : (s2230_stepR S k Rp gj).length = n + j + 1 := by
    simp [s2230_stepR, hlen]
  refine ⟨Rp, ?_, ?_⟩
  · intro i hi
    simp only [s2230_RV]
    rw [hall, s2230_foldR_getD_lt S k post (s2230_stepR S k Rp gj) i (by omega)]
    simp [s2230_stepR, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show i < Rp.length by omega)]
  · simp only [s2230_RV]
    rw [hall, s2230_foldR_getD_lt S k post (s2230_stepR S k Rp gj) (n + j) (by omega)]
    simp [s2230_stepR, List.getD_eq_getElem?_getD, hlen]

lemma s2230_mem_foldl_insertNew (L : List (List ℕ)) (acc : List (List ℕ)) (v : List ℕ)
    (h : v ∈ L.foldl insertNew acc) : v ∈ acc ∨ v ∈ L := by
  induction L generalizing acc with
  | nil => exact Or.inl h
  | cons x L ih =>
    rw [List.foldl_cons] at h
    rcases ih _ h with h1 | h1
    · unfold insertNew at h1
      split_ifs at h1
      · exact Or.inl h1
      · rcases List.mem_append.1 h1 with h2 | h2
        · exact Or.inl h2
        · have h3 : v = x := by simpa using h2
          exact Or.inr (by simp [h3])
    · exact Or.inr (List.mem_cons_of_mem _ h1)

lemma s2230_mem_andStep (k : ℕ) (A B : List (List ℕ)) (v : List ℕ) (h : v ∈ andStep k A B) :
    ∃ u ∈ A, ∃ u2 ∈ B, v = capAdd k u u2 := by
  unfold andStep at h
  rcases s2230_mem_foldl_insertNew _ _ _ h with h1 | h1
  · simp at h1
  · simp only [List.mem_flatMap, List.mem_map] at h1
    obtain ⟨u, hu, u2, hu2, rfl⟩ := h1
    exact ⟨u, hu, u2, hu2, rfl⟩

lemma s2230_capAdd_pair (k x1 y1 x2 y2 : ℕ) :
    capAdd k [x1, y1] [x2, y2] = [min (x1 + x2) (k + 1), min (y1 + y2) (k + 1)] := by
  first
    | rfl
    | simp [capAdd]

lemma s2230_leaf_eq (a b w : ℕ) :
    leafVectors [a, b] 1 w =
      if w ∈ [a, b] then [[if a = w then 1 else 0, if b = w then 1 else 0]] else [] := by
  first
    | rfl
    | (unfold leafVectors; simp)


lemma mem_foldl_insertNew_of_acc (L : List (List ℕ)) (acc : List (List ℕ)) (v : List ℕ)
    (h : v ∈ acc) : v ∈ L.foldl insertNew acc := by
  induction L generalizing acc with
  | nil => exact h
  | cons x L ih =>
    rw [List.foldl_cons]
    apply ih
    unfold insertNew
    split_ifs
    · exact h
    · exact List.mem_append_left _ h

lemma mem_foldl_insertNew_of_mem (L : List (List ℕ)) (acc : List (List ℕ)) (v : List ℕ)
    (h : v ∈ L) : v ∈ L.foldl insertNew acc := by
  induction L generalizing acc with
  | nil => simp at h
  | cons x L ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.1 h with h1 | h1
    · apply mem_foldl_insertNew_of_acc
      subst h1
      unfold insertNew
      split_ifs with h2
      · exact h2
      · simp
    · exact ih _ h1

lemma mem_andStep_of (k : ℕ) (A B : List (List ℕ)) (u u2 : List ℕ) (hu : u ∈ A) (hu2 : u2 ∈ B) :
    capAdd k u u2 ∈ andStep k A B := by
  unfold andStep
  apply mem_foldl_insertNew_of_mem
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨u, hu, u2, hu2, rfl⟩

lemma mem_orFold (As : List (List (List ℕ))) (acc : List (List ℕ)) (v : List ℕ)
    (h : v ∈ acc ∨ ∃ A ∈ As, v ∈ A) :
    v ∈ As.foldl (fun acc A => A.foldl insertNew acc) acc := by
  induction As generalizing acc with
  | nil =>
    rcases h with h | ⟨A, hA, _⟩
    · exact h
    · simp at hA
  | cons A0 As ih =>
    rw [List.foldl_cons]
    apply ih
    rcases h with h | ⟨A, hA, hv⟩
    · exact Or.inl (mem_foldl_insertNew_of_acc _ _ _ h)
    · rcases List.mem_cons.1 hA with h1 | h1
      · subst h1
        exact Or.inl (mem_foldl_insertNew_of_mem _ _ _ hv)
      · exact Or.inr ⟨A, h1, hv⟩

lemma capAdd_map (L : List ℕ) (f g : ℕ → ℕ) (k : ℕ) :
    capAdd k (L.map f) (L.map g) = L.map (fun j => min (f j + g j) (k + 1)) := by
  unfold capAdd
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.map_cons, List.zipWith_cons_cons, ih]

def uv (L : List ℕ) (i : ℕ) : List ℕ := L.map fun j => if j = i then min 1 (1 + 1) else 0

lemma mem_setList {n : ℕ} (S : Finset (Fin n)) (w : ℕ) (hw : w < n) (h : (⟨w, hw⟩ : Fin n) ∈ S) :
    w ∈ setList S := by
  unfold setList
  simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  exact ⟨⟨w, hw⟩, h, rfl⟩

theorem inv (x1 x2 : ℕ) (C : Circuit) (x4 : Bool → Finset ℕ) (hC : IsAO2 (x1 + x2) C)
    (hx4 : ∀ (b : Bool), ∀ w ∈ x4 b, (w < x1 + x2 ∧ decide (x1 ≤ w) = b) ∨
      ∃ j < C.size, w = x1 + x2 + j ∧ (gateAt C j).op = GateOp.or ∧
        ∀ i ∈ (gateAt C j).inputs, i ∈ x4 b)
    (hand : ∀ j < C.size, (gateAt C j).op = GateOp.and →
      ∃ (a : ℕ) (c : ℕ), (gateAt C j).inputs = [a, c] ∧ a ∈ x4 false ∧ c ∈ x4 true)
    (S : Finset (Fin (x1 + x2))) :
    ∀ w, s2230_W (x1 + x2) C (setInput S) w = true →
      (∃ v ∈ s2230_RV C (x1 + x2) (setList S) 1 w, ∀ a ∈ v, a ≤ 1) ∧
      (∀ b, w ∈ x4 b → ∃ i, decide (x1 ≤ i) = b ∧
        uv (setList S) i ∈ s2230_RV C (x1 + x2) (setList S) 1 w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw
  obtain ⟨hAO, hRB, _⟩ := hC
  by_cases hwn : w < x1 + x2
  · have hS : (⟨w, hwn⟩ : Fin (x1 + x2)) ∈ S := by
      rw [s2230_W_input (x1 + x2) C _ w hwn] at hw
      simpa [setInput] using hw
    have hmem : w ∈ setList S := mem_setList S w hwn hS
    have hRV : s2230_RV C (x1 + x2) (setList S) 1 w = [uv (setList S) w] := by
      rw [s2230_RV_input C (x1 + x2) (setList S) 1 w hwn]
      unfold leafVectors uv
      rw [if_pos hmem]
    refine ⟨⟨uv (setList S) w, by rw [hRV]; exact List.mem_singleton_self _, ?_⟩, ?_⟩
    · intro a ha
      unfold uv at ha
      simp only [List.mem_map] at ha
      obtain ⟨j, _, rfl⟩ := ha
      split_ifs <;> omega
    · intro b hb
      refine ⟨w, ?_, by rw [hRV]; exact List.mem_singleton_self _⟩
      rcases hx4 b w hb with ⟨_, hside⟩ | ⟨j, _, hj, _⟩
      · exact hside
      · omega
  · by_cases hwl : w < x1 + x2 + C.gates.length
    swap
    · exfalso
      have hf : s2230_W (x1 + x2) C (setInput S) w = false := by
        unfold s2230_W
        exact s2230_getD_ge_length _ _ (by rw [s2230_wires_length]; omega)
      rw [hf] at hw
      exact Bool.false_ne_true hw
    obtain ⟨j, rfl⟩ : ∃ j, w = x1 + x2 + j := ⟨w - (x1 + x2), by omega⟩
    have hj : j < C.gates.length := by omega
    have hgW := s2230_W_gate (x1 + x2) C (setInput S) j hj
    obtain ⟨Rp, hRp, hRVj⟩ := s2230_RV_gate C (x1 + x2) (setList S) 1 j hj
    have hRB' : ∀ i ∈ (gateAt C j).inputs, i < x1 + x2 + j := hRB j hj
    have hmapW : ((gateAt C j).inputs.map fun i =>
        if i < x1 + x2 + j then s2230_W (x1 + x2) C (setInput S) i else false) =
        (gateAt C j).inputs.map fun i => s2230_W (x1 + x2) C (setInput S) i := by
      refine List.map_congr_left fun i hi => ?_
      rw [if_pos (hRB' i hi)]
    have hmapR : ((gateAt C j).inputs.map fun i => Rp.getD i []) =
        (gateAt C j).inputs.map fun i => s2230_RV C (x1 + x2) (setList S) 1 i := by
      refine List.map_congr_left fun i hi => ?_
      exact hRp i (hRB' i hi)
    have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or :=
      hAO (gateAt C j) (by rw [s2230_gateAt_eq C j hj]; exact List.getElem_mem hj)
    have hor_true : (gateAt C j).op = GateOp.or →
        ∃ i ∈ (gateAt C j).inputs, s2230_W (x1 + x2) C (setInput S) i = true := by
      intro ho
      have hw' := hw
      rw [hgW, hmapW, ho] at hw'
      simpa [GateOp.eval] using hw'
    have hor_mem : (gateAt C j).op = GateOp.or → ∀ i ∈ (gateAt C j).inputs,
        ∀ v ∈ s2230_RV C (x1 + x2) (setList S) 1 i,
          v ∈ s2230_RV C (x1 + x2) (setList S) 1 (x1 + x2 + j) := by
      intro ho i hi v hv
      rw [hRVj, s2230_FR_or _ _ _ _ ho, hmapR]
      apply mem_orFold
      exact Or.inr ⟨_, List.mem_map.2 ⟨i, hi, rfl⟩, hv⟩
    refine ⟨?_, ?_⟩
    · rcases hop with ho | ho
      · obtain ⟨a, c, hac, ha, hc⟩ := hand j hj ho
        have hw' := hw
        rw [hgW, hmapW, ho, hac] at hw'
        have hwa : s2230_W (x1 + x2) C (setInput S) a = true ∧
            s2230_W (x1 + x2) C (setInput S) c = true := by
          simpa [GateOp.eval] using hw'
        have hRBa : a < x1 + x2 + j := hRB' a (by rw [hac]; simp)
        have hRBc : c < x1 + x2 + j := hRB' c (by rw [hac]; simp)
        obtain ⟨ia, hia, hA⟩ := (ih a hRBa hwa.1).2 false ha
        obtain ⟨ic, hic, hCc⟩ := (ih c hRBc hwa.2).2 true hc
        have hne : ia ≠ ic := by
          rintro rfl
          rw [hia] at hic
          exact Bool.false_ne_true hic
        refine ⟨capAdd 1 (capAdd 1 ((setList S).map fun _ => 0) (uv (setList S) ia))
          (uv (setList S) ic), ?_, ?_⟩
        · rw [hRVj, s2230_FR_and _ _ _ _ ho, hmapR, hac]
          simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
          exact mem_andStep_of _ _ _ _ _
            (mem_andStep_of _ _ _ _ _ (List.mem_singleton_self _) hA) hCc
        · intro e he
          unfold uv at he
          rw [capAdd_map, capAdd_map] at he
          simp only [List.mem_map] at he
          obtain ⟨t, _, rfl⟩ := he
          split_ifs <;> omega
      · obtain ⟨i, hi, hwi⟩ := hor_true ho
        obtain ⟨v, hv, hle⟩ := (ih i (hRB' i hi) hwi).1
        exact ⟨v, hor_mem ho i hi v hv, hle⟩
    · intro b hb
      rcases hx4 b _ hb with ⟨hlt, _⟩ | ⟨j', _, hjj, ho, hins⟩
      · omega
      · have hjj' : j' = j := by omega
        subst hjj'
        obtain ⟨i, hi, hwi⟩ := hor_true ho
        obtain ⟨ia, hia, hA⟩ := (ih i (hRB' i hi) hwi).2 b (hins i hi)
        exact ⟨ia, hia, hor_mem ho i hi _ hA⟩

end B6579

theorem t6579 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Bool → Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x3 → (∀ (x6 : Bool), ∀ x7 ∈ x4 x6, x7 < x1 + x2 ∧ Decidable.decide (x1 ≤ x7) = x6 ∨ ∃ x9 < x3.size, x7 = x1 + x2 + x9 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x10 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).inputs, x10 ∈ x4 x6) → (∀ x7 < x3.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : ℕ) (x11 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x7).inputs = [x10, x11] ∧ x10 ∈ x4 Bool.false ∧ x11 ∈ x4 Bool.true) → PEqualNP.ReadK.IsReadK (x1 + x2) x3 (1 : ℕ) := by
  intro x1 x2 C x4 hC hx4 hand S hS
  have hout : PEqualNP.Outside.L_meta_7684.B6579.s2230_W (x1 + x2) C (PEqualNP.ReadK.setInput S)
      C.output = true := hS.1
  obtain ⟨⟨v, hv, hle⟩, _⟩ :=
    PEqualNP.Outside.L_meta_7684.B6579.inv x1 x2 C x4 hC hx4 hand S C.output hout
  unfold PEqualNP.ReadK.readsAtMost
  apply List.any_eq_true.2
  refine ⟨v, hv, ?_⟩
  apply List.all_eq_true.2
  intro a ha
  exact decide_eq_true (hle a ha)

end PEqualNP.Outside.L_meta_7684

theorem PEqualNP.Outside.L_meta_7684 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)), (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧ x7.size ≤ x3.card + x4.card + x5.card - (1 : ℕ) ∧ (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x3 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) ∧ PEqualNP.ReadK.IsReadK (x1 + x2) x7 (1 : ℕ) := by
  intro x1 x2 x3 x4 x5 hcov
  obtain ⟨C, F, hao, hsize, hfun, hF1, hF2⟩ := PEqualNP.Outside.L_meta_7684.t3692 x1 x2 x3 x4 x5 hcov
  exact ⟨C, hao, hsize, hfun, PEqualNP.Outside.L_meta_7684.t6579 x1 x2 C F hao hF1 hF2⟩

namespace PEqualNP.Outside.L_meta_4897

def cross {m n : ℕ} (E : Finset (Fin m × Fin n)) : (Fin m ⊕ Fin n) → (Fin m ⊕ Fin n) → Prop
  | .inl p, .inr q => (p,q) ∈ E
  | .inr q, .inl p => (p,q) ∈ E
  | _, _ => False

def graph {m n : ℕ} (E : Finset (Fin m × Fin n)) : SimpleGraph (Fin (m+n)) where
  Adj u v := cross E (finSumFinEquiv.symm u) (finSumFinEquiv.symm v)
  symm := ⟨by
    intro u v
    cases finSumFinEquiv.symm u <;> cases finSumFinEquiv.symm v <;> simp [cross]⟩
  loopless := ⟨by
    intro u
    cases finSumFinEquiv.symm u <;> simp [cross]⟩


end PEqualNP.Outside.L_meta_4897


namespace IncidenceCover
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4897 (graph cross)
open IncidenceBudget

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

theorem graph_computes {P L} {E : Finset (Fin P × Fin L)} {C : Circuit}
    (f : computes E C) :
    letI := Classical.decRel (graph E).Adj
    circuitFun (P+L) C=graphFun (graph E) ∅ := by
  classical
  funext z
  rw [f]
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or]
  congr 1
  apply propext
  constructor
  · rintro ⟨a,b,edge,ha,hb⟩
    exact ⟨Fin.castAdd L a,Fin.natAdd P b,by simpa [graph,cross] using edge,ha,hb⟩
  · rintro ⟨a,b,edge,ha,hb⟩
    cases a using Fin.addCases <;> cases b using Fin.addCases <;> simp [graph,cross] at edge
    · exact ⟨_,_,edge,ha,hb⟩
    · exact ⟨_,_,edge,hb,ha⟩

theorem support_count {P L : ℕ} (E : Finset (Fin P × Fin L)) :
    letI := Classical.decRel (graph E).Adj
    (E.image Prod.fst).card+(E.image Prod.snd).card ≤ (used (graph E)).card := by
  classical
  let s := (E.image Prod.fst).disjSum (E.image Prod.snd)
  have h : ∀ i∈s, (finSumFinEquiv i : Fin (P+L)).val ∈ used (graph E) := by
    intro i hi
    apply Finset.mem_image.mpr
    refine ⟨finSumFinEquiv i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
    cases i with
    | inl p =>
      obtain ⟨⟨a,b⟩,he,rfl⟩ := Finset.mem_image.mp (Finset.inl_mem_disjSum.mp hi)
      exact ⟨Fin.natAdd P b,by simpa [graph,cross] using he⟩
    | inr l =>
      obtain ⟨⟨a,b⟩,he,rfl⟩ := Finset.mem_image.mp (Finset.inr_mem_disjSum.mp hi)
      exact ⟨Fin.castAdd L a,by simpa [graph,cross] using he⟩
  have b := Finset.card_le_card_of_injOn (fun i => (finSumFinEquiv i : Fin (P+L)).val) h
    (fun _ _ _ _ eq => finSumFinEquiv.injective (Fin.ext eq))
  simpa [s] using b

theorem support_bound {P L : ℕ} {E : Finset (Fin P × Fin L)} {C : Circuit}
    (ao : IsAO2 (P+L) C) (works : computes E C) :
    (E.image Prod.fst).card+(E.image Prod.snd).card≤C.size+1 := by
  classical
  exact (support_count E).trans (support_lower ao (graph_computes works))

theorem path_bound {P L : ℕ} {E : Finset (Fin P × Fin L)} {C : Circuit}
    (ao : IsAO2 (P+L) C) (works : computes E C) {p q : Fin P} {l m : Fin L}
    (e : (p,l)∈E) (f : (p,m)∈E) (g : (q,l)∈E) (mp : m≠l) (qp : q≠p) (diag : (q,m)∉E) :
    (E.image Prod.fst).card+(E.image Prod.snd).card≤C.size := by
  classical
  apply (support_count E).trans
  apply p4_budget (graph E) C ao (graph_computes works)
    (u:=Fin.castAdd L p) (v:=Fin.natAdd P l) (s:=Fin.natAdd P m) (t:=Fin.castAdd L q)
  all_goals simp_all [graph,cross]

theorem unique_columns {P L : ℕ} {E : Finset (Fin P × Fin L)} {C : Circuit}
    (ao : IsAO2 (P+L) C) (works : computes E C)
    (uniq : Set.InjOn Prod.snd (↑E : Set (Fin P × Fin L))) : replacement E C := by
  apply from_cover (E.image Prod.fst) ∅ (fun e he => Or.inl (Finset.mem_image_of_mem _ he))
  have h := support_bound ao works
  have eq := Finset.card_image_of_injOn uniq
  simp only [Finset.card_empty, Nat.add_zero]
  omega
end IncidenceCover


namespace IncidenceCover
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

def rectangleFree {P L} (E : Finset (Fin P × Fin L)) :=
  ∀ p q l m, p≠q → l≠m → ¬ ((p,l)∈E ∧ (p,m)∈E ∧ (q,l)∈E ∧ (q,m)∈E)

theorem with_distinct_columns {P L} (E : Finset (Fin P × Fin L))
    (h : ¬∃ p q l, p≠q ∧ (p,l)∈E ∧ (q,l)∈E) :
    Set.InjOn Prod.snd (↑E : Set (Fin P × Fin L)) := by
  rintro ⟨p,l⟩ hp ⟨q,m⟩ hq hm
  change l=m at hm
  subst m
  congr 1
  by_contra ne
  exact h ⟨p,q,l,ne,hp,hq⟩

theorem at_most_one_extra {P L} {E : Finset (Fin P × Fin L)} {C : Circuit}
    (rect : rectangleFree E) (ao : IsAO2 (P+L) C) (works : computes E C)
    (extra : E.card≤(E.image Prod.snd).card+1) : replacement E C := by
  classical
  by_cases share : ∃ p q l, p≠q ∧ (p,l)∈E ∧ (q,l)∈E
  swap
  · exact unique_columns ao works (with_distinct_columns E share)
  obtain ⟨p,q,l,pq,pl,ql⟩ := share
  let A := E.image Prod.fst
  have pa : p∈A := Finset.mem_image_of_mem Prod.fst pl
  have qa : q∈A := Finset.mem_image_of_mem Prod.fst ql
  have row (i j : Fin P) (ne : i≠j) (il : (i,l)∈E) (jl : (j,l)∈E)
      (other : ∃ m, m≠l ∧ (i,m)∈E) : replacement E C := by
    obtain ⟨m,ml,im⟩ := other
    have diag : (j,m)∉E := fun jm => rect i j l m ne ml.symm ⟨il,im,jl,jm⟩
    have budget := path_bound ao works il im jl ml ne.symm diag
    apply from_cover (E.image Prod.fst) ∅ (fun a ha => Or.inl (Finset.mem_image_of_mem _ ha))
    simp only [Finset.card_empty, Nat.add_zero]
    omega
  by_cases op : ∃ m, m≠l ∧ (p,m)∈E
  · exact row p q pq pl ql op
  by_cases oq : ∃ m, m≠l ∧ (q,m)∈E
  · exact row q p pq.symm ql pl oq
  apply from_cover ((A.erase p).erase q) {l}
  · rintro ⟨i,j⟩ he
    by_cases jl : j=l
    · exact Or.inr (by simpa)
    · left
      have ip : i≠p := by rintro rfl; exact op ⟨j,jl,he⟩
      have iq : i≠q := by rintro rfl; exact oq ⟨j,jl,he⟩
      exact Finset.mem_erase.mpr ⟨iq,Finset.mem_erase.mpr ⟨ip,Finset.mem_image_of_mem Prod.fst he⟩⟩
  · have eq1 := Finset.card_erase_add_one pa
    have eq2 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨pq.symm,qa⟩ : q∈A.erase p)
    have budget := support_bound ao works
    change A.card+_≤_ at budget
    simp only [Finset.card_singleton]
    omega

theorem two_rows_extra {P L} (E : Finset (Fin P × Fin L)) (rect : rectangleFree E)
    (two : (E.image Prod.fst).card≤2) :
    E.card ≤ (E.image Prod.snd).card+1 := by
  classical
  by_cases overlapping : ∃ p q l, p≠q ∧ (p,l)∈E ∧ (q,l)∈E
  swap
  · have eq := Finset.card_image_of_injOn (with_distinct_columns E overlapping)
    omega
  obtain ⟨p,q,l,pq,pl,ql⟩ := overlapping
  have eqRows : ({p,q} : Finset (Fin P))=E.image Prod.fst := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      rcases Finset.mem_insert.mp hi with ep|eq
      · exact ep ▸ Finset.mem_image_of_mem Prod.fst pl
      · exact (Finset.mem_singleton.mp eq) ▸ Finset.mem_image_of_mem Prod.fst ql
    · simpa [pq] using two
  have sides (i : Fin P) (m : Fin L) (h : (i,m)∈E) : i=p ∨ i=q := by
    have hi : i∈E.image Prod.fst := Finset.mem_image_of_mem Prod.fst h
    simpa [←eqRows] using hi
  let F := E.erase (p,l)
  have inj : Set.InjOn Prod.snd (↑F : Set (Fin P × Fin L)) := by
    apply with_distinct_columns
    rintro ⟨a,b,m,ab,am,bm⟩
    obtain ⟨an,ae⟩ := Finset.mem_erase.mp am
    obtain ⟨bn,be⟩ := Finset.mem_erase.mp bm
    have bad (pm : (p,m)∈E) (qm : (q,m)∈E) (ne : (p,m)≠(p,l)) : False :=
      rect p q l m pq (by rintro rfl; exact ne rfl) ⟨pl,pm,ql,qm⟩
    rcases sides a m ae with a_p|a_q <;> rcases sides b m be with b_p|b_q
    · exact ab (a_p.trans b_p.symm)
    · subst a; subst b; exact bad ae be an
    · subst a; subst b; exact bad be ae bn
    · exact ab (a_q.trans b_q.symm)
  have eq := Finset.card_image_of_injOn inj
  have le : (F.image Prod.snd).card ≤ (E.image Prod.snd).card :=
    Finset.card_le_card (Finset.image_mono Prod.snd (Finset.erase_subset _ _))
  have cnt := Finset.card_erase_add_one pl
  change F.card+1=E.card at cnt
  omega

theorem two_rows {L} (E : Finset (Fin 2 × Fin L)) (rect : rectangleFree E) (C : Circuit)
    (ao : IsAO2 (2+L) C) (works : computes E C) : replacement E C :=
  at_most_one_extra rect ao works (two_rows_extra E rect (by simpa using (Finset.card_le_univ (E.image Prod.fst))))

end IncidenceCover

namespace IncidenceCover
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

def Cover {P L : ℕ} (E : Finset (Fin P × Fin L)) (k : ℕ) :=
  ∃ A : Finset (Fin P), ∃ B : Finset (Fin L),
    (∀ e∈E,e.1∈A ∨ e.2∈B) ∧ E.card+A.card+B.card≤k+1

structure Budget {P L : ℕ} (E : Finset (Fin P × Fin L)) (k : ℕ) : Prop where
  support : (E.image Prod.fst).card+(E.image Prod.snd).card≤k+1
  path : ∀ {p q : Fin P} {l m : Fin L}, (p,l)∈E → (p,m)∈E → (q,l)∈E →
    m≠l → q≠p → (q,m)∉E → (E.image Prod.fst).card+(E.image Prod.snd).card≤k

theorem circuit_budget {P L} {E : Finset (Fin P × Fin L)} {C : Circuit}
    (ao : IsAO2 (P+L) C) (works : computes E C) : Budget E C.size :=
  ⟨support_bound ao works,fun e f g mp qp diag => path_bound ao works e f g mp qp diag⟩

theorem one_extra_cover {P L k} {E : Finset (Fin P × Fin L)}
    (rect : rectangleFree E) (bounds : Budget E k)
    (extra : E.card≤(E.image Prod.snd).card+1) : Cover E k := by
  classical
  by_cases share : ∃ p q l, p≠q ∧ (p,l)∈E ∧ (q,l)∈E
  swap
  · refine ⟨E.image Prod.fst,∅,fun e he => Or.inl (Finset.mem_image_of_mem _ he),?_⟩
    have eq := Finset.card_image_of_injOn (with_distinct_columns E share)
    have b := bounds.support
    simp only [Finset.card_empty,Nat.add_zero]
    omega
  obtain ⟨p,q,l,pq,pl,ql⟩ := share
  let A := E.image Prod.fst
  have pa : p∈A := Finset.mem_image_of_mem Prod.fst pl
  have qa : q∈A := Finset.mem_image_of_mem Prod.fst ql
  have row (i j : Fin P) (ne : i≠j) (il : (i,l)∈E) (jl : (j,l)∈E)
      (other : ∃ m, m≠l ∧ (i,m)∈E) : Cover E k := by
    obtain ⟨m,ml,im⟩ := other
    have diag : (j,m)∉E := fun jm => rect i j l m ne ml.symm ⟨il,im,jl,jm⟩
    have budget := bounds.path il im jl ml ne.symm diag
    refine ⟨E.image Prod.fst, ∅, fun a ha => Or.inl (Finset.mem_image_of_mem _ ha), ?_⟩
    simp only [Finset.card_empty, Nat.add_zero]
    omega
  by_cases op : ∃ m, m≠l ∧ (p,m)∈E
  · exact row p q pq pl ql op
  by_cases oq : ∃ m, m≠l ∧ (q,m)∈E
  · exact row q p pq.symm ql pl oq
  refine ⟨(A.erase p).erase q,{l},?_,?_⟩
  · rintro ⟨i,j⟩ he
    by_cases jl : j=l
    · exact Or.inr (by simpa)
    · left
      have ip : i≠p := by rintro rfl; exact op ⟨j,jl,he⟩
      have iq : i≠q := by rintro rfl; exact oq ⟨j,jl,he⟩
      exact Finset.mem_erase.mpr ⟨iq,Finset.mem_erase.mpr ⟨ip,Finset.mem_image_of_mem Prod.fst he⟩⟩
  · have eq1 := Finset.card_erase_add_one pa
    have eq2 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨pq.symm,qa⟩ : q∈A.erase p)
    have budget := bounds.support
    change A.card+_≤_ at budget
    simp only [Finset.card_singleton]
    omega


def flip {P L} (E : Finset (Fin P × Fin L)) := E.map (Equiv.prodComm _ _).toEmbedding

@[simp] theorem flip_mem {P L} {E : Finset (Fin P × Fin L)} {p l} :
    (l,p)∈flip E ↔ (p,l)∈E := by simp [flip]
@[simp] theorem flip_card {P L} (E : Finset (Fin P × Fin L)) : (flip E).card=E.card := by simp [flip]
@[simp] theorem flip_left {P L} (E : Finset (Fin P × Fin L)) :
    (flip E).image Prod.fst=E.image Prod.snd := by
  ext a
  simp only [Finset.mem_image,Prod.exists,flip_mem]
  aesop
@[simp] theorem flip_right {P L} (E : Finset (Fin P × Fin L)) :
    (flip E).image Prod.snd=E.image Prod.fst := by
  ext a
  simp only [Finset.mem_image,Prod.exists,flip_mem]
  aesop

theorem rect_flip {P L} {E : Finset (Fin P × Fin L)} (r : rectangleFree E) : rectangleFree (flip E) := by
  intro l m p q lm pq h
  simp only [flip_mem] at h
  exact r p q l m pq lm ⟨h.1,h.2.2.1,h.2.1,h.2.2.2⟩

theorem budget_flip {P L k} {E : Finset (Fin P × Fin L)} (b : Budget E k) : Budget (flip E) k := by
  refine ⟨by simpa [Nat.add_comm] using b.support,?_⟩
  intro l m p q e f g qp ml diag
  simp only [flip_mem] at e f g diag
  simpa [Nat.add_comm] using b.path e g f ml qp diag

theorem cover_unflip {P L k} {E : Finset (Fin P × Fin L)} (h : Cover (flip E) k) : Cover E k := by
  obtain ⟨B,A,hit,bound⟩ := h
  refine ⟨A,B,?_,?_⟩
  · rintro ⟨p,l⟩ e
    exact (hit (l,p) (flip_mem.mpr e)).symm
  · rw [flip_card] at bound; omega

theorem symmetric_case {P L} {E : Finset (Fin P × Fin L)} {C : Circuit}
    (rect : rectangleFree E) (ao : IsAO2 (P+L) C) (works : computes E C)
    (easy : E.card≤(E.image Prod.snd).card+1 ∨ E.card≤(E.image Prod.fst).card+1 ∨
        (E.image Prod.fst).card≤2 ∨ (E.image Prod.snd).card≤2) : replacement E C := by
  have b := circuit_budget ao works
  suffices h : Cover E C.size by obtain ⟨A,B,hit,bd⟩ := h; exact from_cover A B hit bd
  rcases easy with h|h|h|h
  · exact one_extra_cover rect b h
  · exact cover_unflip (one_extra_cover (rect_flip rect) (budget_flip b) (by simpa using h))
  · exact one_extra_cover rect b (two_rows_extra E rect h)
  · exact cover_unflip (one_extra_cover (rect_flip rect) (budget_flip b)
      (two_rows_extra _ (rect_flip rect) (by simpa using h)))

end IncidenceCover


namespace IncidenceCover
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

theorem cross_count {P L} {E : Finset (Fin P × Fin L)} {p : Fin P} {l : Fin L}
    (hit : ∀ e∈E, e.1=p ∨ e.2=l) (pa : p∈E.image Prod.fst) (la : l∈E.image Prod.snd) :
    (E.erase (p,l)).card+2≤(E.image Prod.fst).card+(E.image Prod.snd).card := by
  classical
  let A := E.image Prod.fst
  let B := E.image Prod.snd
  let f : Fin P × Fin L → Fin P ⊕ Fin L := fun e => if e.1=p then .inr e.2 else .inl e.1
  have maps : ∀ e∈E.erase (p,l),f e∈(A.erase p).disjSum (B.erase l) := by
    rintro ⟨i,j⟩ he
    obtain ⟨ne,ij⟩ := Finset.mem_erase.mp he
    by_cases ip : i=p
    · subst i
      have jl : j≠l := by rintro rfl; exact ne rfl
      simpa [f] using (show j≠l ∧ j∈B from ⟨jl,Finset.mem_image_of_mem Prod.snd ij⟩)
    · simpa [f,ip] using (show i≠p ∧ i∈A from ⟨ip,Finset.mem_image_of_mem Prod.fst ij⟩)
  have inj : Set.InjOn f (↑(E.erase (p,l)) : Set (Fin P × Fin L)) := by
    rintro ⟨i,j⟩ he ⟨a,b⟩ hg eq
    have one := hit (i,j) (Finset.mem_of_mem_erase he)
    have two := hit (a,b) (Finset.mem_of_mem_erase hg)
    change i=p ∨ j=l at one
    change a=p ∨ b=l at two
    by_cases ip : i=p <;> by_cases ap : a=p <;> simp_all [f]
  have le := Finset.card_le_card_of_injOn f maps inj
  rw [Finset.card_disjSum] at le
  have one := Finset.card_erase_add_one pa
  have two := Finset.card_erase_add_one la
  change (E.erase (p,l)).card+2≤A.card+B.card
  change (A.erase p).card+1=A.card at one
  change (B.erase l).card+1=B.card at two
  omega

theorem mixed_centers {P L} {E : Finset (Fin P × Fin L)} {C : Circuit}
    (ao : IsAO2 (P+L) C) (works : computes E C) (p : Fin P) (l : Fin L)
    (hit : ∀ e∈E, e.1=p ∨ e.2=l) : replacement E C := by
  classical
  have b := circuit_budget ao works
  by_cases op : ∃ m, m≠l ∧ (p,m)∈E
  swap
  · apply from_cover ∅ {l}
    · rintro ⟨i,j⟩ e
      right
      rcases hit (i,j) e with eq|eq
      · change i=p at eq; subst i
        by_contra nope
        exact op ⟨j,by simpa using nope,e⟩
      · exact Finset.mem_singleton.mpr eq
    · have uniq : Set.InjOn Prod.fst (↑E : Set (Fin P × Fin L)) := by
        rintro ⟨i,j⟩ e ⟨a,b⟩ h eq
        change i=a at eq
        subst a
        have same (j : Fin L) (ij : (i,j)∈E) : j=l := by
          rcases hit (i,j) ij with ep|el
          · change i=p at ep; subst i; by_contra jl; exact op ⟨j,jl,ij⟩
          · exact el
        rw [same j e,same b h]
      have eq := Finset.card_image_of_injOn uniq
      by_cases em : E=∅
      · simp [em]
      · obtain ⟨e,he⟩ := Finset.nonempty_iff_ne_empty.mpr em
        have pos := Finset.card_pos.mpr ((Finset.nonempty_iff_ne_empty.mpr em).image Prod.snd)
        have bd := b.support
        simp only [Finset.card_empty,Finset.card_singleton,Nat.add_zero]
        omega
  obtain ⟨m,ml,pm⟩ := op
  by_cases oq : ∃ q, q≠p ∧ (q,l)∈E
  swap
  · apply unique_columns ao works
    rintro ⟨i,j⟩ he ⟨a,b⟩ hg eq
    change j=b at eq
    subst b
    have same (a : Fin P) (aj : (a,j)∈E) : a=p := by
      rcases hit (a,j) aj with ep|el
      · exact ep
      · change j=l at el; subst j; by_contra ap; exact oq ⟨a,ap,aj⟩
    rw [same i he,same a hg]
  obtain ⟨q,qp,ql⟩ := oq
  have count := cross_count hit (Finset.mem_image_of_mem Prod.fst pm) (Finset.mem_image_of_mem Prod.snd ql)
  apply from_cover {p} {l}
  · exact fun e he => by simpa using hit e he
  · simp only [Finset.card_singleton]
    by_cases center : (p,l)∈E
    · have diag : (q,m)∉E := fun e => (hit (q,m) e).elim qp ml
      have bd := b.path center pm ql ml qp diag
      have eq := Finset.card_erase_add_one center
      omega
    · rw [Finset.erase_eq_of_notMem center] at count
      have bd := b.support
      omega

end IncidenceCover

namespace IncidenceCover
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

theorem small_cover {P L} {E : Finset (Fin P × Fin L)} {C : Circuit}
    (rect : rectangleFree E) (ao : IsAO2 (P+L) C) (works : computes E C)
    (A : Finset (Fin P)) (B : Finset (Fin L)) (hit : ∀ e∈E, e.1∈A ∨ e.2∈B)
    (small : A.card+B.card≤2) : replacement E C := by
  classical
  by_cases ea : A=∅
  · subst A
    have sub : E.image Prod.snd ⊆ B := by
      intro l hl
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hl
      simpa using hit e he
    exact symmetric_case rect ao works (Or.inr (Or.inr (Or.inr ((Finset.card_le_card sub).trans (by simpa using small)))))
  by_cases eb : B=∅
  · subst B
    have sub : E.image Prod.fst ⊆ A := by
      intro p hp
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hp
      simpa using hit e he
    exact symmetric_case rect ao works (Or.inr (Or.inr (Or.inl ((Finset.card_le_card sub).trans (by simpa using small)))))
  have ap := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr ea)
  have bp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr eb)
  obtain ⟨p,rfl⟩ := Finset.card_eq_one.mp (show A.card=1 by omega)
  obtain ⟨l,rfl⟩ := Finset.card_eq_one.mp (show B.card=1 by omega)
  exact mixed_centers ao works p l (by simpa using hit)

theorem posted_small_cover (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit)
    (rect : ∀ p p' l l',p≠p' → l≠l' → ¬(I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (ao : IsAO2 (P+L) C) (works : ∀ z, PEqualNP.MetaComplexity.circuitFun (P+L) C z =
      decide (∃ p l,I p l ∧ z (Fin.castAdd L p)=true ∧ z (Fin.natAdd P l)=true))
    (A : Finset (Fin P)) (B : Finset (Fin L)) (hit : ∀ p l, I p l → p∈A ∨ l∈B)
    (small : A.card+B.card≤2) :
    ∃ D : Circuit, IsAO2 (P+L) D ∧
      (∀ z,PEqualNP.MetaComplexity.circuitFun (P+L) D z =
        decide (∃ p l,I p l ∧ z (Fin.castAdd L p)=true ∧ z (Fin.natAdd P l)=true)) ∧
      D.size≤C.size ∧ PEqualNP.ReadK.IsReadK (P+L) D 1 := by
  let E := Finset.univ.filter (fun e : Fin P × Fin L => I e.1 e.2)
  have r : rectangleFree E := by simpa [rectangleFree,E] using rect
  have w : computes E C := by simpa [computes,E] using works
  have h : ∀ e∈E,e.1∈A ∨ e.2∈B := by
    rintro ⟨p,l⟩ he
    exact hit p l (by simpa [E] using he)
  simpa [replacement,computes,E] using small_cover r ao w A B h small

end IncidenceCover

#print axioms IncidenceCover.posted_small_cover
#print axioms IncidenceCover.symmetric_case
