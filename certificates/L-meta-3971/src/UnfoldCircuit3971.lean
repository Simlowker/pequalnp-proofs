import UnsharedTree3971
import PEqualNP.Defs
namespace PetersenNegated3971
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def arg3971 (ws : List Expr3971) (ls : List Nat) (j : Nat) (empty : Expr3971) : Expr3971 :=
  match ls[j]? with
  | none => empty
  | some i => ws.getD i (.atom 10)

def node3971 (ws : List Expr3971) (g : Gate) : Expr3971 :=
  let a := arg3971 ws g.inputs
  match g.op with
  | .and => .gate true (a 0 (.atom 11)) (a 1 (.atom 11))
  | .or => .gate false (a 0 (.atom 10)) (a 1 (.atom 10))
  | .not => .invert (a 0 (.atom 10))
  | _ => .atom 10

def sizeNode3971 (s : List (Nat × Nat)) (g : Gate) :=
  let col := fun j => (g.inputs[j]?.bind fun i => s[i]?).getD (1,0)
  let a := col 0
  let b := col 1
  ite (g.op.eval [false]=true) (a.1,a.2+1) (a.1+b.1,a.2+b.2)

def goodGate3971 (g : Gate) := (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2

theorem read_stat3971 (ws : List Expr3971) (ls : List Nat) (j : Nat) (d : Fin 12) :
  (arg3971 ws ls j (.atom d)).stat = (ls[j]?.bind fun i => (ws.map Expr3971.stat)[i]?).getD (1,0) := by
  unfold arg3971
  cases h : ls[j]? with
  | none => rfl
  | some i =>
    simp only [Option.bind_some,List.getElem?_map,List.getD_eq_getElem?_getD]
    cases ws[i]? <;> rfl

theorem project_stat3971 (ws : List Expr3971) (g : Gate) (h : goodGate3971 g) :
    (node3971 ws g).stat=sizeNode3971 (ws.map Expr3971.stat) g := by
  obtain ⟨op,l⟩ := g
  obtain ⟨h,_⟩ := h
  rcases h with h|h|h <;> change op=_ at h <;> subst op <;>
    simp [node3971,Expr3971.stat,read_stat3971,sizeNode3971,GateOp.eval]

theorem read_val3971 (ws : List Expr3971) (i r : Nat) :
    (ws.getD i (.atom 10)).ev r=(ws.map (Expr3971.ev r)).getD i false := by
  exact (List.getD_map (l:=ws) (n:=i) (d:=.atom 10) (Expr3971.ev r)).symm

theorem ev_getD3971 (x : Option Expr3971) (r : Nat) :
    (x.getD (.atom 10)).ev r=(x.map (Expr3971.ev r)).getD false := by cases x <;> rfl

theorem project_val3971 (ws : List Expr3971) (g : Gate) (h : goodGate3971 g) (r : Nat) :
  (node3971 ws g).ev r = g.op.eval (g.inputs.map fun i => (ws.map (Expr3971.ev r)).getD i false) := by
  obtain ⟨op,l⟩ := g
  obtain ⟨h,sz⟩ := h
  have shapes : l=[] ∨ (∃ a,l=[a]) ∨ ∃ a b,l=[a,b] := by
    change l.length≤2 at sz
    cases l with
    | nil => simp
    | cons a l =>
      cases l with
      | nil => simp
      | cons b l =>
        cases l with
        | nil => simp
        | cons c l => simp at sz
  rcases h with h|h|h <;> change op=_ at h <;> subst op <;>
    rcases shapes with e|⟨a,e⟩|⟨a,b,e⟩ <;> subst l <;>
    simp [node3971,arg3971,Expr3971.ev,opBool,ev_getD3971,GateOp.eval,leafValue,literal]

def treeInit3971 : List Expr3971 := ([1,0,4,7,5,2,8,6,3,9] : List (Fin 12)).map Expr3971.atom
def treeStep3971 (ws : List Expr3971) (g : Gate) := ws++[node3971 ws g]
def unfold3971 (C : Circuit) := (C.gates.foldl treeStep3971 treeInit3971).getD C.output (.atom 10)

theorem fold_map3971 {α : Type} (p : Expr3971 → α) (q : List α → Gate → α)
    (project : ∀ ws g, goodGate3971 g → p (node3971 ws g)=q (ws.map p) g)
    (gs : List Gate) (std : ∀ g∈gs, goodGate3971 g) (ws : List Expr3971) :
    (gs.foldl treeStep3971 ws).map p=gs.foldl (fun s g => s++[q s g]) (ws.map p) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,List.foldl_cons,ih (fun a h => std a (List.mem_cons_of_mem _ h))]
    simp only [treeStep3971,List.map_append,List.map_cons,List.map_nil,project ws g (std g List.mem_cons_self)]

end PetersenNegated3971
