import TightTree3722
import PEqualNP.Defs
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

#print axioms output_budget
#print axioms project_lin
end IncidenceBudget
