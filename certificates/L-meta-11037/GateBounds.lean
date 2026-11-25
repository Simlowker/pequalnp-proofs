import PEqualNP.Outside.L_meta_3223
import PEqualNP.Outside.L_meta_6678
import PEqualNP.Outside.L_meta_8459

/-!
Partial results for L-meta-11037, relative to open-goat/pequalnp-proofs
at e66310d1cc29f331ad387407e643704735c28e37.

The optimum of the assigned nine-input function is 15 or 16. In the 15-gate
case, the third input feeds only one effective OR with an earlier non-input
wire. Its partner must vanish on all 20 positive sensitivities. In particular,
splicing one OR into a private star formula for the restriction cannot work.
The existence of a 15-gate circuit remains open in this file.
-/

namespace NineGraph
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3223
def target (x : Fin 9 → Bool) := (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 5) || (x 1 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8)
def base (x : Fin 8 → Bool) := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 7) || (x 6 && x 7)
def witness : Circuit := ⟨[⟨.or,[4,7]⟩, ⟨.or,[9,8]⟩, ⟨.and,[0,10]⟩, ⟨.or,[1,2]⟩, ⟨.or,[12,8]⟩, ⟨.and,[5,13]⟩, ⟨.or,[1,3]⟩, ⟨.and,[6,15]⟩, ⟨.or,[1,4]⟩, ⟨.and,[7,17]⟩, ⟨.or,[2,3]⟩, ⟨.and,[8,19]⟩, ⟨.or,[11,14]⟩, ⟨.or,[21,16]⟩, ⟨.or,[22,18]⟩, ⟨.or,[23,20]⟩],24⟩
theorem upper : HasCircuitSize 9 target 16 := by
  refine ⟨witness,?_,by decide,?_⟩
  · intro g hg
    simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel

def projection : List (Option (Fin 8)) := [some 0,some 4,none,some 6,some 2,some 5,some 7,some 1,some 3]
def lift (x : Fin 8 → Bool) : Fin 9 → Bool := ![x 0,x 4,false,x 6,x 2,x 5,x 7,x 1,x 3]
theorem lift_list : ∀ x, proj projection x=List.ofFn (lift x) := by decide +kernel
theorem lift_target : ∀ x, target (lift x)=base x := by decide +kernel
def test (r : ℕ) (i : Fin 9) := r.testBit i.val
def eight (r : ℕ) (i : Fin 8) := r.testBit i.val
def Correct (C : Circuit) := ∀ x : Fin 9 → Bool, C.eval (List.ofFn x)=target x
abbrev BaseLower := ∀ t, HasCircuitSize 8 base t → 14 ≤ t

theorem restricted (C : Circuit) (hc : Correct C) (x : Fin 8 → Bool) :
    C.eval (proj projection x) = base x := by rw [lift_list,hc,lift_target]
theorem varies (C : Circuit) (hc : Correct C) :
    ∃ x y, C.eval (proj projection x) ≠ C.eval (proj projection y) :=
  ⟨eight 0,eight 3,by rw [restricted C hc,restricted C hc];decide +kernel⟩
theorem sensitive (C : Circuit) (hc : Correct C) :
    ∃ a b : List Bool, a.length=projection.length ∧ b.length=projection.length ∧
      (∀ i,i≠2 → a.getD i false=b.getD i false) ∧ C.eval a ≠ C.eval b := by
  refine ⟨List.ofFn (test 32),List.ofFn (test 36),rfl,rfl,?_,?_⟩
  · intro i hi
    by_cases h : i<9
    · interval_cases i <;> first | contradiction | decide
    · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
  · rw [hc,hc];decide +kernel

theorem floor (lb : BaseLower) (C : Circuit) (hf : FanInTwo C) (hc : Correct C)
    (b : Nat) (small : b ≤ 1) (noOr : b=1 → ∀ g ∈ C.gates, g.op=.or → 2 ∉ g.inputs) :
    14+(b+1) ≤ C.size := by
  obtain ⟨D,df,ds,de⟩ := PEqualNP.Outside.L_meta_3223 8 C projection 2 b hf rfl small noOr
    (sensitive C hc) (varies C hc)
  have lower := lb D.size ⟨D,df,le_rfl,fun x => (de x).trans (restricted C hc x)⟩
  omega

theorem needs_or (lb : BaseLower) (C : Circuit) (hf : FanInTwo C) (hc : Correct C)
    (size : C.size≤15) : ∃ g ∈ C.gates, g.op=.or ∧ 2∈g.inputs := by
  by_contra! h
  have bound := floor lb C hf hc 1 (by decide) (fun _ => h)
  omega
end NineGraph

namespace NineGraph
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3223
def uses (g : Gate) := decide (2 ∈ g.inputs)

theorem count_pass (m : Nat) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (ok : ∀ g ∈ gs, NOkGate g) (raw : 2 < acc.1.length)
    (tag2 : acc.1.getD 2 (.inl false) = .inl false) :
    (elimPass m gs acc).2.length + gs.countP uses ≤ acc.2.length + gs.length := by
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
    by_cases read : 2∈g.inputs
    · have gok := ok g List.mem_cons_self
      have z : opt=none := simplifyGate_none_of_const _ _ _ gok.1.1 (by simpa [hv] using gok.1.2)
        (fun h => by simpa [hv] using gok.2 h) ⟨false,List.mem_map.mpr ⟨2,read,tag2⟩⟩
      rw [z] at tailBound
      simp [List.countP_cons,uses,read] at tailBound ⊢
      omega
    · have bound := toList_opt_len_le opt
      simp [List.countP_cons,uses,read] at tailBound ⊢
      omega

theorem reads_budget (lb : BaseLower) (C : Circuit) (hf : FanInTwo C) (hc : Correct C) :
    14 + (C.gates.map normGate).countP uses ≤ C.size := by
  obtain ⟨D,df,ds,de⟩ := extract C projection hf (varies C hc)
  have low := lb D.size ⟨D,df,le_rfl,fun x => (de x).trans (restricted C hc x)⟩
  have bound := count_pass 8 (C.gates.map normGate) (start projection) (by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact normGate_nok a (hf a ha)) (by decide) (by decide)
  change D.size = (elimPass 8 (C.gates.map normGate) (start projection)).2.length at ds
  rw [ds] at low
  simp only [start,List.length_nil,zero_add,List.length_map] at bound low
  change 14 + _ ≤ C.gates.length
  omega

theorem shape (lb : BaseLower) (C : Circuit) (hf : FanInTwo C) (hc : Correct C)
    (hs : C.size ≤ 15) :
    ∃ pre g post, C.gates.map normGate = pre ++ g :: post ∧ g.op=.or ∧ 2 ∈ g.inputs ∧
      (∀ a∈pre, 2∉a.inputs) ∧ (∀ a∈post, 2∉a.inputs) := by
  obtain ⟨g,hg,op,read⟩ := needs_or lb C hf hc hs
  have same : normGate g=g := by cases g with | mk op' ins => change op' = .or at op; subst op';rfl
  have hit : g∈C.gates.map normGate := List.mem_map.mpr ⟨g,hg,same⟩
  obtain ⟨pre,post,eq⟩ := List.append_of_mem hit
  have cnt := reads_budget lb C hf hc
  rw [eq,List.countP_append,List.countP_cons] at cnt
  simp only [uses,read,decide_true,ite_true] at cnt
  have a : pre.countP uses=0 := by omega
  have b : post.countP uses=0 := by omega
  refine ⟨pre,g,post,eq,op,read,?_,?_⟩
  · simpa [List.countP_eq_zero,uses] using a
  · simpa [List.countP_eq_zero,uses] using b
end NineGraph

namespace NineGraph
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3223

def normalized (C : Circuit) : Circuit := ⟨C.gates.map normGate,C.output⟩
theorem norm_eval (C : Circuit) (x : List Bool) : (normalized C).eval x = C.eval x := by
  unfold Circuit.eval
  change (wiresFrom (C.gates.map normGate) x).getD _ _ = _
  rw [wiresFrom_norm];rfl
theorem norm_size (C : Circuit) : (normalized C).size = C.size := by simp [normalized,Circuit.size]
theorem norm_fan (C : Circuit) (hf : FanInTwo C) : FanInTwo (normalized C) := by
  intro g hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  exact (normGate_nok a (hf _ ha)).1

def same2 (x y : List Bool) := ∀ i : Nat, i≠2 → x.getD i false=y.getD i false
theorem same_append (x y : List Bool) (h : same2 x y) (len : x.length=y.length) (b : Bool) :
    same2 (x++[b]) (y++[b]) := by
  intro i off
  by_cases last : i=x.length
  · rw [getD_snoc_eq _ _ _ _ last,getD_snoc_eq _ _ _ _ (last.trans len)]
  · rw [getD_snoc_ne _ _ _ _ last,getD_snoc_ne _ _ _ _ (by omega)]; exact h i off

theorem no_read (gs : List Gate) (free : ∀ a∈gs,2∉a.inputs) (x y : List Bool)
    (h : same2 x y) (len : x.length=y.length) : same2 (wiresFrom gs x) (wiresFrom gs y) := by
  induction gs generalizing x y with
  | nil => exact h
  | cons g gs ih =>
    have e : (g.inputs.map fun i => x.getD i false)=(g.inputs.map fun i => y.getD i false) :=
      List.map_congr_left (fun i hi => h i (fun eq => free g List.mem_cons_self (eq ▸ hi)))
    rw [wiresFrom_cons,wiresFrom_cons,e]
    exact ih (fun a ha => free _ (List.mem_cons_of_mem _ ha)) _ _ (same_append _ _ h len _) (by simp [len])

theorem raw_get {n} (x : Fin n → Bool) (i : Fin n) : (List.ofFn x).getD i.val false=x i := by
  simp [List.getD_eq_getElem?_getD]

def wire (gs : List Gate) (x : Fin 9 → Bool) (i : Nat) :=
  (wiresFrom gs (List.ofFn x)).getD i false
theorem raw_wire (gs : List Gate) (x : Fin 9 → Bool) (j : Fin 9) : wire gs x j.val = x j := by
  rw [wire,wiresFrom_getD_lt _ _ _ (by simp)]; exact raw_get x j

theorem target_not_raw (D : Circuit) (hc : Correct D) : D.output ≠ 2 := by
  intro he
  have h := hc (test 17)
  change wire D.gates (test 17) D.output = _ at h
  rw [he,show (2:Nat)=(2:Fin 9).val by rfl,raw_wire] at h
  exact (by decide : test 17 2 ≠ target (test 17)) h

def sens (x : Fin 9 → Bool) := target x=false ∧ target (Function.update x 2 true)=true

theorem other_off (D : Circuit) (hc : Correct D) {pre g post}
    (split : D.gates=pre++g::post) (orop : g.op=.or)
    (before : ∀ a∈pre,2∉a.inputs) (after_ : ∀ a∈post,2∉a.inputs)
    (j : Nat) (mem : j∈g.inputs) (ne : j≠2) (x : Fin 9 → Bool) (hx : sens x) :
    wire pre x j = false := by
  let y := Function.update x (2 : Fin 9) true
  have baseeq : same2 (List.ofFn x) (List.ofFn y) := by
    intro i hn
    by_cases h : i<9
    · change (List.ofFn x).getD (⟨i,h⟩ : Fin 9).val false = (List.ofFn y).getD (⟨i,h⟩ : Fin 9).val false
      rw [raw_get,raw_get, show y=Function.update x 2 true from rfl,Function.update_of_ne (fun eq => hn (congrArg Fin.val eq))]
    · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]
  have beforeEq := no_read pre before _ _ baseeq (by simp)
  by_contra! bad
  have t : wire pre x j = true := by simpa using bad
  have ty : wire pre y j=true := (beforeEq j ne).symm.trans t
  have gateTrue (z : Fin 9 → Bool) (hz : wire pre z j=true) :
      g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn z)).getD i false)=true := by
    simp only [orop,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_def,id_eq]
    exact ⟨j,mem,hz⟩
  have out (z : Fin 9 → Bool) (hz : wire pre z j=true) :
      D.eval (List.ofFn z)=(wiresFrom post (wiresFrom pre (List.ofFn z)++[true])).getD D.output false := by
    change (wiresFrom D.gates _).getD _ _ = _
    rw [split,wiresFrom_append,wiresFrom_cons,gateTrue z hz]
  have len : (wiresFrom pre (List.ofFn x)).length=(wiresFrom pre (List.ofFn y)).length := by simp [wiresFrom_length]
  have tail := no_read post after_ _ _ (same_append _ _ beforeEq len true) (by simp only [List.length_append,len])
  have eq : D.eval (List.ofFn x)=D.eval (List.ofFn y) := (out x t).trans ((tail _ (target_not_raw D hc)).trans (out y ty).symm)
  rw [hc,hc,hx.1,show target y = true from hx.2] at eq
  contradiction

theorem all_other_bits : ∀ j : Fin 9, j≠2 → ∃ r : Fin 512, sens (test r.val) ∧ test r.val j=true := by
  unfold sens; decide +kernel

theorem no_raw_partner (D : Circuit) (hc : Correct D) {pre g post}
    (split : D.gates=pre++g::post) (orop : g.op=.or) (before : ∀ a∈pre,2∉a.inputs)
    (after_ : ∀ a∈post,2∉a.inputs) (v : Fin 9) (ne : v≠2) : v.val∉g.inputs := by
  intro mem
  obtain ⟨r,s,hit⟩ := all_other_bits v ne
  have no := other_off D hc split orop before after_ v.val mem (fun eq => ne (Fin.ext eq)) (test r.val) s
  rw [raw_wire,hit] at no; contradiction

end NineGraph

namespace NineGraph
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3223

theorem exact_base : BaseLower := PEqualNP.Outside.L_meta_8459

theorem lower : ∀ s, HasCircuitSize 9 target s → 15 ≤ s := by
  rintro s ⟨C,hf,hs,hc⟩
  have b := floor exact_base C hf hc 0 (by decide) (by intro h; omega)
  omega

theorem observed (D : Circuit) {pre g post} (split : D.gates=pre++g::post) (x : Fin 9 → Bool) :
    (D.wires (List.ofFn x)).getD (9+pre.length) false =
      g.op.eval (g.inputs.map fun i => wire pre x i) := by
  have len : (wiresFrom pre (List.ofFn x)).length = 9+pre.length := by rw [wiresFrom_length,List.length_ofFn]
  change (wiresFrom D.gates _).getD _ _ = _
  rw [split,wiresFrom_append,wiresFrom_cons,wiresFrom_getD_lt _ _ _ (by simp only [List.length_append,len,List.length_singleton];omega)]
  exact getD_snoc_eq _ _ _ _ len.symm

theorem forbidden_copy (D : Circuit) (hf : FanInTwo D) (hc : Correct D) (ds : D.size ≤ 15)
    {pre g post} (split : D.gates=pre++g::post)
    (copy : ∀ x : Fin 9 → Bool, g.op.eval (g.inputs.map fun i => wire pre x i)=x 2) : False := by
  have smaller :=  PEqualNP.Outside.L_meta_6678 9 D id {pre.length} hf (Or.inl rfl) (by
    refine ⟨test 0,test 17,?_⟩
    change D.eval (List.ofFn (test 0)) ≠ D.eval (List.ofFn (test 17))
    rw [hc,hc];decide +kernel) (by
      intro j hj
      obtain rfl := Finset.mem_singleton.mp hj
      refine ⟨by rw [split,List.length_append,List.length_cons];omega,Or.inr ⟨2,by omega,?_⟩⟩
      intro x
      change (D.wires (List.ofFn x)).getD _ false=wire D.gates x (2:Fin 9).val
      rw [raw_wire,observed D split,copy])
  have eq : (fun x : Fin 9→Bool => D.eval (List.ofFn (id x)))=target := funext hc
  rw [eq,Finset.card_singleton] at smaller
  have b := lower _ smaller
  omega

theorem computed_partner (D : Circuit) (hf : FanInTwo D) (hc : Correct D) (size : D.size≤15)
    {pre g post} (eq : D.gates=pre++g::post) (op : g.op=.or) (read : 2∈g.inputs)
    (bp : ∀ a∈pre,2∉a.inputs) (bs : ∀ a∈post,2∉a.inputs) :
    ∃ j ∈ g.inputs, 9 ≤ j ∧ j < 9+pre.length := by
  by_contra! nh
  apply forbidden_copy D hf hc size eq
  intro x
  have others (i : Nat) (hi : i∈g.inputs) (ne : i≠2) : wire pre x i = false := by
    by_cases raw : i<9
    · exact False.elim ((no_raw_partner D hc eq op bp bs ⟨i,raw⟩ (fun e => ne (congrArg Fin.val e))) hi)
    · have big := nh i hi (by omega)
      unfold wire
      apply List.getD_eq_default
      rw [wiresFrom_length,List.length_ofFn]; omega
  rw [op]
  cases hx : x 2 with
  | false =>
    simp only [GateOp.eval,List.any_map,List.any_eq_false,Function.comp_def,id_eq]
    intro i hi
    by_cases ne : i=2
    · subst i; simp only [Bool.not_eq_true]; exact (raw_wire pre x (2:Fin 9)).trans hx
    · simp [others i hi ne]
  | true =>
    simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_def,id_eq]
    exact ⟨2,read,(raw_wire pre x (2:Fin 9)).trans hx⟩

theorem lift_required (C : Circuit) (hf : FanInTwo C) (hc : Correct C) (hs : C.size ≤ 15) :
    C.size=15 ∧ ∃ pre g post j, (normalized C).gates=pre++g::post ∧ g.op=.or ∧
      (g.inputs=[2,j] ∨ g.inputs=[j,2]) ∧ 9≤j ∧ j<9+pre.length ∧
      (∀ a∈pre,2∉a.inputs) ∧ (∀ a∈post,2∉a.inputs) ∧
      ∀ x : Fin 9 → Bool, sens x → wire pre x j=false := by
  have lo := lower C.size ⟨C,hf,le_rfl,hc⟩
  obtain ⟨pre,g,post,eq,op,r,bp,bs⟩ := shape exact_base C hf hc hs
  let D := normalized C
  have split : D.gates=pre++g::post := eq
  have correct : Correct D := fun x => (norm_eval C _).trans (hc x)
  have fan := norm_fan C hf
  obtain ⟨j,hj,lb,ub⟩ := computed_partner D fan correct (by simpa [D,norm_size] using hs) split op r bp bs
  have len := (fan g (split ▸ List.mem_append_right _ List.mem_cons_self)).2
  have pair : g.inputs=[2,j] ∨ g.inputs=[j,2] := by
    rcases h : g.inputs with _|⟨a,_|⟨b,_|⟨c,more⟩⟩⟩ <;> simp_all
    all_goals omega
  exact ⟨by omega,pre,g,post,j,eq,op,pair,lb,ub,bp,bs,other_off D correct split op bp bs _ hj (by omega)⟩

theorem optimal_restriction (C : Circuit) (hf : FanInTwo C) (hc : Correct C) (hs : C.size ≤ 15) :
    ∃ D : Circuit, FanInTwo D ∧ D.size=14 ∧ ∀ x : Fin 8 → Bool, D.eval (List.ofFn x)=base x := by
  obtain ⟨D,df,ds,de⟩ := PEqualNP.Outside.L_meta_3223 8 C projection 2 0 hf rfl (by decide)
    (by intro h; omega) (sensitive C hc) (varies C hc)
  have ok : ∀ x : Fin 8 → Bool, D.eval (List.ofFn x)=base x :=
    fun x => (de x).trans (restricted C hc x)
  have lb := exact_base D.size ⟨D,df,le_rfl,ok⟩
  exact ⟨D,df,by omega,ok⟩

end NineGraph

namespace NineGraph

def sensitiveMasks : List (Fin 512) := (List.finRange 512).filter fun r =>
  !target (test r.val) && target (Function.update (test r.val) 2 true)

theorem count_sensitive : sensitiveMasks.length = 20 := by decide +kernel

theorem mask_iff (r : Fin 512) : r ∈ sensitiveMasks ↔ sens (test r.val) := by
  simp [sensitiveMasks,sens]

def candidatePairs : List (Fin 9 × Fin 9) :=
  [(0,1),(0,4),(0,7),(0,8),(1,3),(1,5),(1,6),(1,7),(3,6),(3,8),(4,7),(5,8)]

/-- Exhausts the two-literal positive conjunctions insensitive on the required rows. -/
theorem pair_test : ∀ a b : Fin 9, a≠2 → b≠2 → a<b →
    ((∀ r ∈ sensitiveMasks, (test r.val a && test r.val b)=false) ↔ (a,b) ∈ candidatePairs) := by
  decide +kernel

theorem sensitive_zero : ∀ a : Fin 9, a≠2 →
    ∃ r ∈ sensitiveMasks, test r.val a=false := by decide +kernel

/-- Inserting the new input inside a private neighbour-OR tree contributes just one centre. -/
theorem one_centre_insufficient : ∀ c : Fin 9, ∃ r : Fin 512,
    target (test r.val) ≠ (target (Function.update (test r.val) 2 false) ||
      (test r.val 2 && test r.val c)) := by decide +kernel

end NineGraph

namespace NineGraph.Star
inductive Expr where
  | var (i : Fin 9)
  | either (a b : Expr)
  | both (a b : Expr)

def value (x : Fin 9 → Bool) : Expr → Bool
  | .var i => x i
  | .either a b => value x a || value x b
  | .both a b => value x a && value x b

/-- Place one OR with the new variable on the output of any existing gate of a formula. -/
inductive Insert : Expr → Expr → Prop where
  | atOr a b : Insert (.either a b) (.either (.var 2) (.either a b))
  | atAnd a b : Insert (.both a b) (.either (.var 2) (.both a b))
  | orL {a d} (b) : Insert a d → Insert (.either a b) (.either d b)
  | orR (a) {b d} : Insert b d → Insert (.either a b) (.either a d)
  | andL {a d} (b) : Insert a d → Insert (.both a b) (.both d b)
  | andR (a) {b d} : Insert b d → Insert (.both a b) (.both a d)

inductive Tree (α : Type) where
  | leaf (a : α)
  | fork (a b : Tree α)

def neighbours : Tree (Fin 9) → Expr
  | .leaf i => .var i
  | .fork a b => .either (neighbours a) (neighbours b)

def stars : Tree (Fin 9 × Tree (Fin 9)) → Expr
  | .leaf (c,t) => .both (.var c) (neighbours t)
  | .fork a b => .either (stars a) (stars b)

theorem inside (t : Tree (Fin 9)) {z : Expr} (h : Insert (neighbours t) z) :
    ∀ x, value x z = (x 2 || value x (neighbours t)) := by
  induction t generalizing z with
  | leaf i => cases h
  | fork a b ia ib =>
    change Insert (.either (neighbours a) (neighbours b)) z at h
    cases h with
    | atOr => exact fun _ => rfl
    | orL _ e => intro x; simp [neighbours,value,ia e x,Bool.or_assoc]
    | orR _ e => intro x; simp [neighbours,value,ib e x,Bool.or_left_comm]

def Effect (c : Option (Fin 9)) (x : Fin 9 → Bool) : Bool :=
  match c with
  | none => x 2
  | some i => x 2 && x i

theorem outside (t : Tree (Fin 9 × Tree (Fin 9))) {z : Expr} (h : Insert (stars t) z) :
    ∃ c : Option (Fin 9), ∀ x, value x z = (Effect c x || value x (stars t)) := by
  induction t generalizing z with
  | leaf p =>
    rcases p with ⟨c,t⟩
    change Insert (.both (.var c) (neighbours t)) z at h
    cases h with
    | atAnd => exact ⟨none,fun _ => rfl⟩
    | andL _ h => cases h
    | andR _ h =>
      refine ⟨some c, fun x => ?_⟩
      simp [stars,value,Effect,inside _ h x,Bool.and_or_distrib_left,Bool.and_comm]
  | fork a b ia ib =>
    change Insert (.either (stars a) (stars b)) z at h
    cases h with
    | atOr => exact ⟨none,fun _ => rfl⟩
    | orL _ e =>
      obtain ⟨c,ih⟩ := ia e
      exact ⟨c,fun x => by simp [stars,value,ih x,Bool.or_assoc]⟩
    | orR _ e =>
      obtain ⟨c,ih⟩ := ib e
      exact ⟨c,fun x => by simp [stars,value,ih x,Bool.or_left_comm]⟩

theorem impossible (t : Tree (Fin 9 × Tree (Fin 9)))
    (base_ok : ∀ x, value x (stars t)=target (Function.update x 2 false))
    {z : Expr} (edit : Insert (stars t) z) : ¬ ∀ x, value x z=target x := by
  intro good
  obtain ⟨c,effect⟩ := outside _ edit
  cases c with
  | none =>
    have h := effect (test 4)
    rw [good,base_ok] at h
    exact (by decide +kernel : target (test 4) ≠ (Effect none (test 4) || target (Function.update (test 4) 2 false))) h
  | some i =>
    obtain ⟨r,bad⟩ := one_centre_insufficient i
    have h := effect (test r.val)
    rw [good,base_ok] at h
    exact bad (h.trans (Bool.or_comm _ _))

end NineGraph.Star

#print axioms NineGraph.upper
#print axioms NineGraph.lower
#print axioms NineGraph.lift_required
#print axioms NineGraph.optimal_restriction
#print axioms NineGraph.count_sensitive
#print axioms NineGraph.pair_test
#print axioms NineGraph.Star.impossible
