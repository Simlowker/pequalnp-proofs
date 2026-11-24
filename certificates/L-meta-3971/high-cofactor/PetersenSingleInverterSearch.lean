import Mathlib.Tactic
import Mathlib.Data.Nat.Bitwise
import PEqualNP.Defs

/-!
# A finite search for the Petersen circuit with one inverter

Each word records a wire on all 512 inputs. A counterexample to L-meta-3971
would produce a straight-line program with at most twelve ordinary binary
operations, one complement, and one operation adjoining the distinguished
input by OR. Each instruction introduces a new truth column. Binary
operands are strictly ordered. The distinguished OR must have an operand
which is false on rows 10, 26 and 74.
-/

namespace PetersenProgram3971

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Inst := Nat × Nat × Nat
def neg (g : Gate) := g.op.eval [false]
def touch (g : Gate) := (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any (fun i => decide (i=6))
def standard (g : Gate) := g.op=.and ∨ g.op=.or ∨ g.op=.not
def tag (g : Gate) : Nat := if touch g then 3 else if neg g then 2 else 0
def category (g : Inst) : Nat := if g.1<2 then 0 else g.1
def applyOp (ones toggle : Nat) (g : Inst) : Nat :=
  match g.1 with
  | 0 => g.2.1 &&& g.2.2
  | 1 => g.2.1 ||| g.2.2
  | 2 => ones ^^^ g.2.1
  | _ => toggle ||| g.2.1

def legal (vs : List Nat) (g : Inst) : Prop :=
  g.1<4 ∧ g.2.1∈vs ∧ (if g.1<2 then g.2.2∈vs ∧ g.2.1<g.2.2 else g.2.2=0)

def value (ones : Nat) (r : Nat → Nat) (g : Gate) : Nat :=
  match g.op with
  | .and => (g.inputs.map r).foldr (· &&& ·) ones
  | .or => (g.inputs.map r).foldr (· ||| ·) 0
  | .not => ones ^^^ ((g.inputs.map r).headD 0)
  | _ => 0

theorem unique_reader (C : Circuit) (num : C.gates.countP touch≤1)
    (someOr : ∃ g∈C.gates, g.op=.or ∧ 6∈g.inputs) :
    ∀ g∈C.gates, touch g=true → g.op=.or := by
  obtain ⟨o,ho,op,read⟩ := someOr
  have hit : touch o=true := by simp [touch,op,GateOp.eval,read]
  let hits := C.gates.filter touch
  have n : hits.length≤1 := by simpa [hits,List.countP_eq_length_filter] using num
  have mem : o∈hits := List.mem_filter.mpr ⟨ho,hit⟩
  have single : hits.length=1 := by have p := List.length_pos_of_mem mem; omega
  obtain ⟨j,eq⟩ := List.length_eq_one_iff.mp single
  intro g hg h
  have good : g∈hits := List.mem_filter.mpr ⟨hg,h⟩
  rw [eq] at good mem
  simpa only [List.mem_singleton.mp good,List.mem_singleton.mp mem] using op

def Next (ones t : Nat) (vs : List Nat) (k y : Nat) : Prop :=
  y ∈ vs ∨ ∃ g : Inst, legal vs g ∧ category g=k ∧ applyOp ones t g=y

theorem unary (ones t : Nat) (vs : List Nat) (k a : Nat) (ha : a∈vs) (hk : k=2 ∨ k=3) :
    Next ones t vs k (if k=2 then ones ^^^ a else t ||| a) := by
  right
  refine ⟨(k,a,0),?_,?_,?_⟩ <;> rcases hk with rfl|rfl <;> simp [legal,category,applyOp,ha]

theorem binary (ones t : Nat) (vs : List Nat) (o : Bool) (a b : Nat) (ha : a∈vs) (hb : b∈vs) :
    Next ones t vs 0 (if o then a &&& b else a ||| b) := by
  by_cases h : a=b
  · subst b; left; cases o <;> simpa using ha
  right
  let g : Inst := (if o then 0 else 1,min a b,max a b)
  refine ⟨g,?_,?_,?_⟩
  · cases o <;> rcases le_total a b with le|le <;>
      simp [g,legal,ha,hb,le] <;> omega
  · cases o <;> rfl
  · cases o <;> rcases le_total a b with le|le <;>
      simp [g,applyOp,le,Nat.and_comm,Nat.or_comm]

theorem transition (ones t : Nat) (vs : List Nat) (r : Nat → Nat) (g : Gate)
    (zero : 0∈vs) (full : ones∈vs) (old : ∀ i, i≠6 → r i∈vs) (at6 : r 6=t)
    (bounded : ∀ i, r i &&& ones=r i) (std : standard g) (ar : g.inputs.length≤2)
    (onlyOr : touch g=true → g.op=.or) : Next ones t vs (tag g) (value ones r g) := by
  obtain ⟨op,ls⟩ := g
  rcases std with h|h|h <;> change op=_ at h <;> subst op
  · have nt : touch (⟨.and,ls⟩ : Gate)=false := by
      cases h : touch (⟨.and,ls⟩ : Gate)
      · rfl
      · cases onlyOr h
    have no : 6∉ls := by
      intro bad
      have yes : touch (⟨.and,ls⟩ : Gate)=true := by simp [touch,GateOp.eval,bad]
      rw [nt] at yes
      contradiction
    simp only [tag,nt,neg,GateOp.eval, Bool.false_eq_true,ite_false,List.all_cons,List.all_nil,Bool.and_true,id_eq]
    cases ls with
    | nil => exact Or.inl full
    | cons a as =>
      have ha : a≠6 := by rintro rfl; exact no (by simp)
      cases as with
      | nil => left; simpa [value,bounded] using old a ha
      | cons b bs =>
        have hb : b≠6 := by rintro rfl; exact no (by simp)
        have eb : bs=[] := by simpa using ar
        subst bs
        simpa [value,bounded] using binary ones t vs true _ _ (old a ha) (old b hb)
  · cases ls with
    | nil => exact Or.inl zero
    | cons a as =>
      cases as with
      | nil =>
        by_cases h : a=6
        · subst a
          simpa [tag,touch,neg,GateOp.eval,value,at6] using unary ones t vs 3 0 zero (Or.inr rfl)
        · left; simpa [value] using old a h
      | cons b bs =>
        have eb : bs=[] := by simpa using ar
        subst bs
        by_cases ha : a=6
        · subst a
          by_cases hb : b=6
          · subst b
            simpa [tag,touch,neg,GateOp.eval,value,at6] using unary ones t vs 3 0 zero (Or.inr rfl)
          · simpa [tag,touch,neg,GateOp.eval,value,at6] using unary ones t vs 3 (r b) (old _ hb) (Or.inr rfl)
        · by_cases hb : b=6
          · subst b
            simpa [tag,touch,neg,GateOp.eval,value,at6,ha,Nat.or_comm] using unary ones t vs 3 (r a) (old _ ha) (Or.inr rfl)
          · simpa [tag,touch,neg,GateOp.eval,value,ha,hb] using binary ones t vs false _ _ (old a ha) (old b hb)
  · cases ls with
    | nil => simpa [tag,touch,neg,GateOp.eval,value] using unary ones t vs 2 0 zero (Or.inl rfl)
    | cons a as =>
      have ha : a≠6 := by
        rintro rfl
        cases onlyOr (by simp [touch,GateOp.eval])
      simpa [tag,touch,neg,GateOp.eval,value,ha] using unary ones t vs 2 (r a) (old a ha) (Or.inl rfl)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def limit := 2^512
def ones := limit-1
def W (pool : List Nat) := ∀ a∈pool, a<limit
def wires (pool orig : List Nat) := ∀ i, i≠6 → orig.getD i 0 ∈ pool
def evalWord (t : Nat) (xs : List Nat) (g : Inst) := xs++[applyOp ones t g]
def good (t : Nat) (pool : List Nat) : List Inst → Prop
  | [] => True
  | g::gs => legal pool g ∧ applyOp ones t g∉pool ∧ good t (evalWord t pool g) gs
def evalGate (xs : List Nat) (g : Gate) := xs++[value ones (fun i => xs.getD i 0) g]

set_option maxRecDepth 4000 in
theorem step_bound {pool : List Nat} (h : W pool) (t : Nat) (ht : t<limit) (g : Inst)
    (well : legal pool g) : applyOp ones t g<limit := by
  obtain ⟨n,a,b⟩ := g
  obtain ⟨lt,mem,side⟩ := well
  have ha := h a mem
  change n<4 at lt
  interval_cases n
  · exact lt_of_le_of_lt Nat.and_le_left ha
  · have hb : b∈pool ∧ a<b := by simpa only [Nat.reduceLT,ite_true] using side
    exact Nat.or_lt_two_pow (n:=512) ha (h b hb.1)
  · exact Nat.xor_lt_two_pow (n:=512) (Nat.sub_lt (Nat.two_pow_pos _) (by decide)) ha
  · exact Nat.or_lt_two_pow (n:=512) ht ha

theorem extendW {pool : List Nat} (h : W pool) {a} (ha : a<limit) : W (pool++[a]) := by
  intro x hx
  rcases List.mem_append.mp hx with o|n
  · exact h _ o
  · simpa [List.mem_singleton.mp n] using ha

theorem append_wires {xs pool newpool : List Nat} {y} (old : wires pool xs)
    (incl : ∀ a∈pool,a∈newpool) (mem : y∈newpool) (zero : 0∈newpool) : wires newpool (xs++[y]) := by
  intro i hi
  by_cases low : i<xs.length
  · rw [List.getD_append _ _ _ _ low]
    exact incl _ (old i hi)
  by_cases eq : i=xs.length
  · subst i
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simpa using mem
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    exact zero

set_option maxRecDepth 4000 in
theorem simulate (t : Nat) (ht : t<limit) (gs : List Gate)
    (shape : ∀ g∈gs, standard g ∧ g.inputs.length≤2 ∧ (touch g=true → g.op=.or))
    (xs pool : List Nat) (well : W pool) (start : wires pool xs)
    (len : 6<xs.length) (bit : xs.getD 6 0=t) (zero : 0∈pool) (full : ones∈pool) :
    ∃ p : List Inst, good t pool p ∧
      (∀ k : Nat, p.countP (fun i => decide (category i=k)) ≤ gs.countP (fun i => decide (tag i=k))) ∧
      wires (p.foldl (evalWord t) pool) (gs.foldl evalGate xs) := by
  induction gs generalizing xs pool with
  | nil => exact ⟨[],by trivial,fun _ => le_rfl,start⟩
  | cons g rest ih =>
    have ⟨std,ar,onlyOr⟩ := shape g List.mem_cons_self
    let r := fun i => xs.getD i 0
    have small (i : Nat) : r i<limit := by
      by_cases h : i=6
      · subst i; change xs.getD 6 0<limit; rw [bit]; exact ht
      · exact well _ (start i h)
    have bounds (i : Nat) : r i &&& ones=r i := Nat.and_two_pow_sub_one_of_lt_two_pow (n:=512) (small i)
    let y := value ones r g
    have step := transition ones t pool r g zero full start bit bounds std ar onlyOr
    have shape' := fun u (hu : u∈rest) => shape u (List.mem_cons_of_mem _ hu)
    have len' : 6<(xs++[y]).length := by simp; omega
    have bit' : (xs++[y]).getD 6 0=t := (List.getD_append _ _ _ _ len).trans bit
    by_cases mem : y∈pool
    · obtain ⟨p,gp,ct,ws⟩ := ih shape' (xs++[y]) pool well (append_wires start (fun _ h => h) mem zero) len' bit' zero full
      refine ⟨p,gp,?_,ws⟩
      intro k
      have b := ct k
      rw [List.countP_cons]
      split <;> omega
    · obtain ⟨j,legal',cat,val⟩ := step.resolve_left mem
      change applyOp ones t j=y at val
      have eqv : evalWord t pool j=pool++[y] := by simp [evalWord,val,y]
      have z := List.mem_append_left [y] zero
      have f := List.mem_append_left [y] full
      obtain ⟨p,gp,ct,ws⟩ := ih shape' (xs++[y]) (pool++[y])
        (extendW well (by rw [←val]; exact step_bound well t ht j legal'))
        (append_wires start (fun _ h => List.mem_append_left _ h) (by simp) z) len' bit' z f
      refine ⟨j::p,⟨legal',by rwa [val],by rwa [eqv]⟩,?_,?_⟩
      · intro k
        have bound := ct k
        simp only [List.countP_cons,cat]
        omega
      · simpa only [List.foldl_cons,eqv,evalGate] using ws

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def sample (q : Nat) : Fin 8 → Bool := fun i => q.testBit i.val
def inputs (t : Bool) (x : Fin 8 → Bool) : List Bool := [x 1,x 0,x 4,x 7,x 5,x 2,t,x 6,x 3,x 1 || t]
def baseEdge (x : Fin 8 → Bool) := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 ||
  x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4
def answer (q : Nat) := baseEdge (sample q) || (q.testBit 8 && ((sample q) 0 || (sample q) 3))
def readBit (q x : Nat) := x.testBit q

set_option maxRecDepth 4000 in
theorem ones_bit {q : Nat} (hq : q<512) : readBit q ones=true := by
  exact (Nat.testBit_two_pow_sub_one 512 q).trans (decide_eq_true hq)

set_option maxRecDepth 4000 in
theorem gate_bit (O : Nat) (g : Gate) (r : Nat → Nat) (q : Nat) (hq : readBit q O=true) (std : standard g) :
    readBit q (value O r g)=g.op.eval (g.inputs.map fun i => readBit q (r i)) := by
  obtain ⟨op,ls⟩ := g
  rcases std with h|h|h <;> change op=_ at h <;> subst op
  · induction ls with
    | nil => exact hq
    | cons a l ih =>
      change ((r a) &&& _).testBit q = (_ && _)
      rw [Nat.testBit_and]
      exact congrArg (fun b => (r a).testBit q && b) ih
  · induction ls with
    | nil => simp [readBit,value,GateOp.eval]
    | cons a l ih =>
      change ((r a) ||| _).testBit q = (_ || _)
      rw [Nat.testBit_or]
      exact congrArg (fun b => (r a).testBit q || b) ih
  · cases ls with
    | nil => simpa [value,GateOp.eval,readBit] using hq
    | cons a l =>
      change (O ^^^ r a).testBit q = !(r a).testBit q
      rw [Nat.testBit_xor,show O.testBit q=true from hq]
      cases (r a).testBit q <;> rfl

def boolStep (ws : List Bool) (g : Gate) := ws++[g.op.eval (g.inputs.map fun i => ws.getD i false)]
theorem projects (gs : List Gate) (shape : ∀ g∈gs, standard g) (xs : List Nat) (q : Nat) (hq : q<512) :
    (gs.foldl evalGate xs).map (readBit q) = gs.foldl boolStep (xs.map (readBit q)) := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g rest ih =>
    simp only [List.foldl_cons]
    rw [ih (fun a ha => shape a (List.mem_cons_of_mem _ ha))]
    apply congrArg (rest.foldl boolStep)
    simp only [evalGate,boolStep,List.map_append,List.map_cons,List.map_nil,
      gate_bit ones _ _ _ (ones_bit hq) (shape g List.mem_cons_self)]
    congr 2
    apply congrArg g.op.eval
    apply List.map_congr_left
    intro i _
    simpa only [readBit,Nat.zero_testBit] using (List.getD_map (l:=xs) (d:=0) (n:=i) (readBit q)).symm

theorem bounds_count (gs : List Gate) (std : ∀ g∈gs, standard g ∧ (touch g=true → g.op=.or)) :
    gs.countP (fun g => decide (tag g=0)) + gs.countP neg + gs.countP touch = gs.length ∧
    gs.countP (fun g => decide (tag g=2)) = gs.countP neg ∧
    gs.countP (fun g => decide (tag g=3)) = gs.countP touch := by
  induction gs with
  | nil => decide
  | cons g l ih =>
    obtain ⟨a,b,c⟩ := ih (fun x hx => std x (List.mem_cons_of_mem _ hx))
    have local' := (std g List.mem_cons_self).2
    simp only [List.countP_cons,List.length_cons]
    by_cases h : touch g=true
    · have n : neg g=false := by simp [neg,local' h,GateOp.eval]
      have tg : tag g=3 := by simp [tag,h]
      simp [tg,h,n] <;> omega
    · cases n : neg g
      · have tg : tag g=0 := by simp [tag,h,n]
        simp [tg,h,n] <;> omega
      · have tg : tag g=2 := by simp [tag,h,n]
        simp [tg,h,n] <;> omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def origin : List Nat := [10726246343954077679659219998564676901983492656473914702178849154977411224058837581441499438533522742152025486549188840683003106249557255957146919204867276,8938538619961731399716016665470564084986243880394928918482374295814509353382364651201249532111268951793354572124324033902502588541297713297622432670722730,13407603346151304507647333602124270744930157291580986197148043437687863763597662002711256755796972443613438635551055889478487182262900810351549134401372160,13407807929942597099574024998205846127439963814395998898511282403621620416268583029620646167694378705270794824322841769944638336182637648515027502377205760,13407807926820848549984871490950625460264621687587329935306297008442977448960781863686381587396241115434734742314166555940848600484775015044616064818216960,12619113345828326681952023527723149296451167831145782002563351947032248498892750095813528751215909108414147631234339812568238948528890889361349316711608560,13407807929942597099574024998205846127479365820592393377723561443721764030073431184712636981971479856705023170278632780869088242247907112362425735876444160,13407807929942597098847186273910239236969444018900783322580063136098668673514857287274768220802268387129003177701362428774192761570871467260109520434626560,13355637471071225126423931515722554897411352724014212858744092333045803858750303603351283347590378511628981150567083381395178964979993470452478654262869760,13407807929942597099574024998205846127479365820592393377723561443721764030073523818384026834927818713493030120604915396856820754699138678429632066380156108]
def seed : List Nat := [0,ones,10726246343954077679659219998564676901983492656473914702178849154977411224058837581441499438533522742152025486549188840683003106249557255957146919204867276,8938538619961731399716016665470564084986243880394928918482374295814509353382364651201249532111268951793354572124324033902502588541297713297622432670722730,13407603346151304507647333602124270744930157291580986197148043437687863763597662002711256755796972443613438635551055889478487182262900810351549134401372160,13407807929942597099574024998205846127439963814395998898511282403621620416268583029620646167694378705270794824322841769944638336182637648515027502377205760,13407807926820848549984871490950625460264621687587329935306297008442977448960781863686381587396241115434734742314166555940848600484775015044616064818216960,12619113345828326681952023527723149296451167831145782002563351947032248498892750095813528751215909108414147631234339812568238948528890889361349316711608560,13407807929942597098847186273910239236969444018900783322580063136098668673514857287274768220802268387129003177701362428774192761570871467260109520434626560,13355637471071225126423931515722554897411352724014212858744092333045803858750303603351283347590378511628981150567083381395178964979993470452478654262869760,13407807929942597099574024998205846127479365820592393377723561443721764030073523818384026834927818713493030120604915396856820754699138678429632066380156108]
def toggle : Nat := 13407807929942597099574024998205846127479365820592393377723561443721764030073431184712636981971479856705023170278632780869088242247907112362425735876444160
def target : Nat := 13407807929942597095939831376727811673905304651018912648022854022873869787405066962725179222507908767667956533170508564710083788841651696458571261487544520

set_option maxRecDepth 5000 in
theorem data_ok : W seed ∧ toggle<limit ∧ origin.getD 6 0=toggle ∧
    0∈seed ∧ ones∈seed ∧ 6<origin.length ∧ target<limit := by
  unfold W
  decide +kernel

theorem orig_wires : wires seed origin := by
  intro i ne
  by_cases lt : i<10
  · have a : ∀ j : Fin 10, j.val≠6 → origin.getD j.val 0∈seed := by decide +kernel
    exact a ⟨i,lt⟩ ne
  · rw [List.getD_eq_default _ _ (by change (10 : Nat) ≤ i; omega)]
    exact data_ok.2.2.2.1

set_option maxRecDepth 5000 in
theorem data_bits : ∀ q : Fin 512,
    origin.map (readBit q.val) = inputs (q.val.testBit 8) (sample q.val) ∧
    readBit q.val target=answer q.val := by decide +kernel

theorem preserved6 (xs : List Nat) (gates : List Gate) (h : 6<xs.length) :
    (gates.foldl evalGate xs).getD 6 0=xs.getD 6 0 := by
  induction gates generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,ih (evalGate xs g) (by simp [evalGate]; omega)]
    exact List.getD_append _ _ _ _ h

theorem prog_bounds (pool : List Nat) (h : W pool) (gs : List Inst) (good' : good toggle pool gs) :
    W (gs.foldl (evalWord toggle) pool) := by
  induction gs generalizing pool with
  | nil => exact h
  | cons g gs ih =>
    exact ih _ (extendW h (step_bound h toggle data_ok.2.1 g good'.1)) good'.2.2

def solution (p : List Inst) := good toggle seed p ∧
  p.countP (fun i => decide (category i=0))≤12 ∧
  p.countP (fun i => decide (category i=2))≤1 ∧
  p.countP (fun i => decide (category i=3))≤1 ∧ target∈p.foldl (evalWord toggle) seed

set_option maxRecDepth 5000 in
theorem running (C : Circuit) (fit : FanInTwo C) (sz : C.size=14)
    (one : C.gates.countP neg=1) (rd : C.gates.countP touch≤1)
    (reader : ∃ g∈C.gates,g.op=.or ∧ 6∈g.inputs)
    (lo : ∀ x, C.eval (inputs false x)=baseEdge x)
    (hi : ∀ x, C.eval (inputs true x)=(baseEdge x || x 0 || x 3)) :
    ∃ p, solution p := by
  have onlyOr := unique_reader C rd reader
  have shape (g) (hg : g∈C.gates) : standard g ∧ g.inputs.length≤2 ∧ (touch g=true → g.op=.or) := by
    exact ⟨(fit g hg).1,(fit g hg).2,onlyOr g hg⟩
  obtain ⟨well,ht,bit,z,f,len,bound⟩ := data_ok
  obtain ⟨p,legal',ct,ws⟩ := simulate toggle ht C.gates shape origin seed well orig_wires len bit z f
  let all := C.gates.foldl evalGate origin
  let y := all.getD C.output 0
  have obs (q : Fin 512) : readBit q.val y=readBit q.val target := by
    have pr := projects C.gates (fun g hg => (shape g hg).1) origin q.val q.isLt
    rw [(data_bits q).1] at pr
    have pr' := congrArg (fun l : List Bool => l.getD C.output false) pr
    change (all.map (readBit q.val)).getD C.output false = C.eval (inputs (q.val.testBit 8) (sample q.val)) at pr'
    have lhs : (all.map (readBit q.val)).getD C.output false = readBit q.val y := by
      simpa only [readBit,Nat.zero_testBit] using (List.getD_map (l:=all) (d:=0) (n:=C.output) (readBit q.val))
    rw [lhs] at pr'
    rw [pr',(data_bits q).2]
    cases h : q.val.testBit 8
    · simpa [answer,h] using lo (sample q.val)
    · simpa [answer,h,Bool.or_assoc] using hi (sample q.val)
  have diff : C.output ≠ 6 := by
    intro bad
    have h := obs (⟨256,by decide⟩ : Fin 512)
    change (all.getD C.output 0).testBit 256=target.testBit 256 at h
    rw [bad,show all.getD 6 0=toggle from (preserved6 origin C.gates len).trans bit] at h
    exact (by decide : ¬(toggle.testBit 256=target.testBit 256)) h
  have ys : y∈p.foldl (evalWord toggle) seed := ws _ diff
  have small := prog_bounds seed well p legal' y ys
  have eq : y=target := by
    apply Nat.eq_of_testBit_eq
    intro q
    by_cases low : q<512
    · exact obs ⟨q,low⟩
    · have top : limit≤2^q := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le small top),Nat.testBit_lt_two_pow (lt_of_lt_of_le bound top)]
  obtain ⟨gs,g2,g3⟩ := bounds_count C.gates fun g hg => ⟨(shape g hg).1,onlyOr g hg⟩
  have has : 0<C.gates.countP touch := by
    obtain ⟨g,hg,op,rr⟩ := reader
    exact List.countP_pos_iff.mpr ⟨g,hg,by simp [touch,op,GateOp.eval,rr]⟩
  have c0 := ct 0
  have c2 := ct 2
  have c3 := ct 3
  change C.gates.length=14 at sz
  exact ⟨p,legal',by omega,by omega,by omega,eq ▸ ys⟩

def fixed (r : Nat) (a : Nat) := a.testBit r=a.testBit (r+256)
def stable (r : Nat) (pool : List Nat) := ∀ a∈pool, fixed r a
def critical : List Nat := [10,26,74]

theorem step_fixed (r : Nat) (pool : List Nat) (g : Inst) (yr : stable r pool)
    (one : fixed r ones) (leg : legal pool g) (patch : g.1=3 → g.2.1.testBit r=true) :
    fixed r (applyOp ones toggle g) := by
  obtain ⟨n,a,b⟩ := g
  obtain ⟨lt,ha,other⟩ := leg
  change n<4 at lt
  have ea := yr a ha
  unfold fixed at ea one ⊢
  interval_cases n
  · have hb : b∈pool ∧ a<b := by simpa using other
    have eb : b.testBit r=b.testBit (r+256) := yr b hb.1
    simp only [applyOp,Nat.testBit_and,ea,eb]
  · have hb : b∈pool ∧ a<b := by simpa using other
    have eb : b.testBit r=b.testBit (r+256) := yr b hb.1
    simp only [applyOp,Nat.testBit_or,ea,eb]
  · simp only [applyOp,Nat.testBit_xor,ea,one]
  · have on' : a.testBit r=true := patch rfl
    have also : a.testBit (r+256)=true := ea.symm.trans on'
    simp [applyOp,on',also]

theorem forced (p : List Inst) (sp : solution p) (r : Nat) (hr : r∈critical) :
    ∃ g∈p, g.1=3 ∧ g.2.1.testBit r=false := by
  obtain ⟨gp,_b,_n,_c,mem⟩ := sp
  have facts : ∀ q∈critical, (∀ a∈seed,a.testBit q=a.testBit (q+256)) ∧
      ones.testBit q=ones.testBit (q+256) ∧ target.testBit q≠target.testBit (q+256) := by
    decide +kernel
  obtain ⟨st,one,tar⟩ := facts r hr
  by_contra! h
  have all (xs : List Inst) (pool : List Nat) (g : good toggle pool xs)
      (initial : stable r pool) (patch : ∀ a∈xs, a.1=3 → a.2.1.testBit r=true) :
      stable r (xs.foldl (evalWord toggle) pool) := by
    induction xs generalizing pool with
    | nil => exact initial
    | cons a l ih =>
      apply ih _ g.2.2 _ (fun z hz => patch z (List.mem_cons_of_mem _ hz))
      intro b hb
      rcases List.mem_append.mp hb with old|new'
      · exact initial b old
      · obtain rfl := List.mem_singleton.mp new'
        exact step_fixed r pool a initial one g.1 (patch a List.mem_cons_self)
  apply tar
  exact all p seed gp st (by intro a ha eq; have no := h a ha eq; simpa using no) target mem

theorem patch_mask (p : List Inst) (sp : solution p) :
    ∃ g∈p, g.1=3 ∧ ∀ r∈critical, g.2.1.testBit r=false := by
  obtain ⟨g,hg,op,_⟩ := forced p sp 10 (by decide)
  refine ⟨g,hg,op,?_⟩
  intro r hr
  obtain ⟨j,hj,jo,off⟩ := forced p sp r hr
  let hits := p.filter (fun k => decide (category k=3))
  have n : hits.length≤1 := by simpa only [hits,← List.countP_eq_length_filter] using sp.2.2.2.1
  have mg : g∈hits := by simp [hits,hg,category,op]
  have mj : j∈hits := by simp [hits,hj,category,jo]
  obtain ⟨k,eq⟩ := List.length_eq_one_iff.mp (show hits.length=1 by have := List.length_pos_of_mem mg; omega)
  rw [eq] at mg mj
  have same := (List.mem_singleton.mp mg).trans (List.mem_singleton.mp mj).symm
  simpa only [same] using off

end PetersenProgram3971

theorem PetersenProgram3971.reduction (finite : ∀ p, PetersenProgram3971.solution p →
    (∃ g∈p, g.1=3 ∧ ∀ r∈PetersenProgram3971.critical,g.2.1.testBit r=false) → False) :
  have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) => x3 (0 : Fin (8 : ℕ)) && x3 (1 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (2 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (3 : Fin (8 : ℕ)) || x3 (0 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (5 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (3 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (4 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (5 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (7 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size = (14 : ℕ) → List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => x7.op.eval [Bool.false]) x4.gates = (1 : ℕ) → List.countP x1 x4.gates ≤ (1 : ℕ) → (∃ x9 ∈ x4.gates, x9.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (6 : ℕ) ∈ x9.inputs) → (∀ (x10 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.false x10) = x3 x10) → ∃ (x11 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.true x11) ≠ (x3 x11 || x11 (0 : Fin (8 : ℕ)) || x11 (3 : Fin (8 : ℕ))) := by
  dsimp only
  intro C fit sz one rd reader lo
  by_contra! hi
  obtain ⟨p,sp⟩ := PetersenProgram3971.running C fit sz one rd reader lo hi
  exact finite p sp (PetersenProgram3971.patch_mask p sp)

#print axioms PetersenProgram3971.reduction
