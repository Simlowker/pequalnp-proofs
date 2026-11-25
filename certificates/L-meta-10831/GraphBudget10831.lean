import PEqualNP.Outside.L_meta_3223
import PEqualNP.Outside.L_meta_6678
import PEqualNP.Outside.L_meta_8439

/-!
For the specific nine-vertex eleven-edge graph of L-meta-10831.
An explicit circuit gives an upper bound of fifteen. Fixing input 3 to false
leaves the eight-vertex instance of L-meta-8439 and gives a lower bound of
fourteen with arbitrary AND, OR and NOT gates. In a fourteen-gate circuit,
the sole effective reader of input 3 must be an OR with an earlier computed
wire which is false on each of nineteen specified sensitive inputs.

A weighted rectangle certificate proves that a monotone formula needs sixteen
leaves. The star formula attains sixteen. The formula result counts separately
each occurrence of a reused computation when a circuit is unfolded.

The cofactor analysis specializes the L-meta-11037 argument to this graph.
The weighted rectangle induction follows the earlier L-meta-10726 certificate.
The weights, circuit, function-sensitive tests and restriction are specific to
this instance. The unrestricted fifteen-gate lower bound is outside this file.

Upstream definitions and dependencies were taken from commit
c5fe0f918c0bb79c1799969d44cf83a8f5f5db28 of open-goat/pequalnp-proofs.
-/

namespace Graph10831
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3223
def target (x : Fin 9 → Bool) := (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8)
def base (x : Fin 8 → Bool) := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 7) || (x 6 && x 7)
def witness : Circuit := ⟨[⟨.or,[4,6]⟩, ⟨.or,[9,7]⟩, ⟨.and,[0,10]⟩, ⟨.or,[5,6]⟩, ⟨.and,[1,12]⟩, ⟨.or,[6,8]⟩, ⟨.and,[2,14]⟩, ⟨.or,[3,4]⟩, ⟨.and,[7,16]⟩, ⟨.or,[3,5]⟩, ⟨.and,[8,18]⟩, ⟨.or,[11,13]⟩, ⟨.or,[20,15]⟩, ⟨.or,[21,17]⟩, ⟨.or,[22,19]⟩],23⟩
theorem upper : HasCircuitSize 9 target 15 := by
  refine ⟨witness,?_,by decide,?_⟩
  · intro g hg
    simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel

def projection : List (Option (Fin 8)) := [some 0,some 4,some 5,none,some 1,some 6,some 3,some 2,some 7]
def lift (x : Fin 8 → Bool) : Fin 9 → Bool := ![x 0,x 4,x 5,false,x 1,x 6,x 3,x 2,x 7]
theorem lift_list : ∀ x, proj projection x=List.ofFn (lift x) := by decide +kernel
theorem lift_target : ∀ x, target (lift x)=base x := by decide +kernel
def test (r : ℕ) (i : Fin 9) := r.testBit i.val
def eight (r : ℕ) (i : Fin 8) := r.testBit i.val
def Correct (C : Circuit) := ∀ x : Fin 9 → Bool, C.eval (List.ofFn x)=target x
abbrev BaseLower := ∀ t, HasCircuitSize 8 base t → 13 ≤ t

theorem restricted (C : Circuit) (hc : Correct C) (x : Fin 8 → Bool) :
    C.eval (proj projection x) = base x := by rw [lift_list,hc,lift_target]
theorem varies (C : Circuit) (hc : Correct C) :
    ∃ x y, C.eval (proj projection x) ≠ C.eval (proj projection y) :=
  ⟨eight 0,eight 3,by rw [restricted C hc,restricted C hc];decide +kernel⟩
theorem sensitive (C : Circuit) (hc : Correct C) :
    ∃ a b : List Bool, a.length=projection.length ∧ b.length=projection.length ∧
      (∀ i,i≠3 → a.getD i false=b.getD i false) ∧ C.eval a ≠ C.eval b := by
  refine ⟨List.ofFn (test 128),List.ofFn (test 136),rfl,rfl,?_,?_⟩
  · intro i hi
    by_cases h : i<9
    · interval_cases i <;> first | contradiction | decide
    · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
  · rw [hc,hc];decide +kernel

theorem floor (lb : BaseLower) (C : Circuit) (hf : FanInTwo C) (hc : Correct C)
    (b : Nat) (small : b ≤ 1) (noOr : b=1 → ∀ g ∈ C.gates, g.op=.or → 3 ∉ g.inputs) :
    13+(b+1) ≤ C.size := by
  obtain ⟨D,df,ds,de⟩ := PEqualNP.Outside.L_meta_3223 8 C projection 3 b hf rfl small noOr
    (sensitive C hc) (varies C hc)
  have lower := lb D.size ⟨D,df,le_rfl,fun x => (de x).trans (restricted C hc x)⟩
  omega

theorem needs_or (lb : BaseLower) (C : Circuit) (hf : FanInTwo C) (hc : Correct C)
    (size : C.size≤14) : ∃ g ∈ C.gates, g.op=.or ∧ 3∈g.inputs := by
  by_contra! h
  have bound := floor lb C hf hc 1 (by decide) (fun _ => h)
  omega
end Graph10831

namespace Graph10831
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3223
def uses (g : Gate) := decide (3 ∈ g.inputs)

theorem count_pass (m : Nat) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (ok : ∀ g ∈ gs, NOkGate g) (raw : 3 < acc.1.length)
    (tag2 : acc.1.getD 3 (.inl false) = .inl false) :
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
    by_cases read : 3∈g.inputs
    · have gok := ok g List.mem_cons_self
      have z : opt=none := simplifyGate_none_of_const _ _ _ gok.1.1 (by simpa [hv] using gok.1.2)
        (fun h => by simpa [hv] using gok.2 h) ⟨false,List.mem_map.mpr ⟨3,read,tag2⟩⟩
      rw [z] at tailBound
      simp [List.countP_cons,uses,read] at tailBound ⊢
      omega
    · have bound := toList_opt_len_le opt
      simp [List.countP_cons,uses,read] at tailBound ⊢
      omega

theorem reads_budget (lb : BaseLower) (C : Circuit) (hf : FanInTwo C) (hc : Correct C) :
    13 + (C.gates.map normGate).countP uses ≤ C.size := by
  obtain ⟨D,df,ds,de⟩ := extract C projection hf (varies C hc)
  have low := lb D.size ⟨D,df,le_rfl,fun x => (de x).trans (restricted C hc x)⟩
  have bound := count_pass 8 (C.gates.map normGate) (start projection) (by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact normGate_nok a (hf a ha)) (by decide) (by decide)
  change D.size = (elimPass 8 (C.gates.map normGate) (start projection)).2.length at ds
  rw [ds] at low
  simp only [start,List.length_nil,zero_add,List.length_map] at bound low
  change 13 + _ ≤ C.gates.length
  omega

theorem shape (lb : BaseLower) (C : Circuit) (hf : FanInTwo C) (hc : Correct C)
    (hs : C.size ≤ 14) :
    ∃ pre g post, C.gates.map normGate = pre ++ g :: post ∧ g.op=.or ∧ 3 ∈ g.inputs ∧
      (∀ a∈pre, 3∉a.inputs) ∧ (∀ a∈post, 3∉a.inputs) := by
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
end Graph10831

namespace Graph10831
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

def same2 (x y : List Bool) := ∀ i : Nat, i≠3 → x.getD i false=y.getD i false
theorem same_append (x y : List Bool) (h : same2 x y) (len : x.length=y.length) (b : Bool) :
    same2 (x++[b]) (y++[b]) := by
  intro i off
  by_cases last : i=x.length
  · rw [getD_snoc_eq _ _ _ _ last,getD_snoc_eq _ _ _ _ (last.trans len)]
  · rw [getD_snoc_ne _ _ _ _ last,getD_snoc_ne _ _ _ _ (by omega)]; exact h i off

theorem no_read (gs : List Gate) (free : ∀ a∈gs,3∉a.inputs) (x y : List Bool)
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

theorem target_not_raw (D : Circuit) (hc : Correct D) : D.output ≠ 3 := by
  intro he
  have h := hc (test 17)
  change wire D.gates (test 17) D.output = _ at h
  rw [he,show (3:Nat)=(3:Fin 9).val by rfl,raw_wire] at h
  exact (by decide : test 17 3 ≠ target (test 17)) h

def sens (x : Fin 9 → Bool) := target x=false ∧ target (Function.update x 3 true)=true

theorem other_off (D : Circuit) (hc : Correct D) {pre g post}
    (split : D.gates=pre++g::post) (orop : g.op=.or)
    (before : ∀ a∈pre,3∉a.inputs) (after_ : ∀ a∈post,3∉a.inputs)
    (j : Nat) (mem : j∈g.inputs) (ne : j≠3) (x : Fin 9 → Bool) (hx : sens x) :
    wire pre x j = false := by
  let y := Function.update x (3 : Fin 9) true
  have baseeq : same2 (List.ofFn x) (List.ofFn y) := by
    intro i hn
    by_cases h : i<9
    · change (List.ofFn x).getD (⟨i,h⟩ : Fin 9).val false = (List.ofFn y).getD (⟨i,h⟩ : Fin 9).val false
      rw [raw_get,raw_get, show y=Function.update x 3 true from rfl,Function.update_of_ne (fun eq => hn (congrArg Fin.val eq))]
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

theorem all_other_bits : ∀ j : Fin 9, j≠3 → ∃ r : Fin 512, sens (test r.val) ∧ test r.val j=true := by
  unfold sens; decide +kernel

theorem no_raw_partner (D : Circuit) (hc : Correct D) {pre g post}
    (split : D.gates=pre++g::post) (orop : g.op=.or) (before : ∀ a∈pre,3∉a.inputs)
    (after_ : ∀ a∈post,3∉a.inputs) (v : Fin 9) (ne : v≠3) : v.val∉g.inputs := by
  intro mem
  obtain ⟨r,s,hit⟩ := all_other_bits v ne
  have no := other_off D hc split orop before after_ v.val mem (fun eq => ne (Fin.ext eq)) (test r.val) s
  rw [raw_wire,hit] at no; contradiction

end Graph10831

namespace Graph10831
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3223

theorem exact_base : BaseLower := PEqualNP.Outside.L_meta_8439

theorem lower : ∀ s, HasCircuitSize 9 target s → 14 ≤ s := by
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

theorem forbidden_copy (D : Circuit) (hf : FanInTwo D) (hc : Correct D) (ds : D.size ≤ 14)
    {pre g post} (split : D.gates=pre++g::post)
    (copy : ∀ x : Fin 9 → Bool, g.op.eval (g.inputs.map fun i => wire pre x i)=x 3) : False := by
  have smaller :=  PEqualNP.Outside.L_meta_6678 9 D id {pre.length} hf (Or.inl rfl) (by
    refine ⟨test 0,test 17,?_⟩
    change D.eval (List.ofFn (test 0)) ≠ D.eval (List.ofFn (test 17))
    rw [hc,hc];decide +kernel) (by
      intro j hj
      obtain rfl := Finset.mem_singleton.mp hj
      refine ⟨by rw [split,List.length_append,List.length_cons];omega,Or.inr ⟨3,by omega,?_⟩⟩
      intro x
      change (D.wires (List.ofFn x)).getD _ false=wire D.gates x (3:Fin 9).val
      rw [raw_wire,observed D split,copy])
  have eq : (fun x : Fin 9→Bool => D.eval (List.ofFn (id x)))=target := funext hc
  rw [eq,Finset.card_singleton] at smaller
  have b := lower _ smaller
  omega

theorem computed_partner (D : Circuit) (hf : FanInTwo D) (hc : Correct D) (size : D.size≤14)
    {pre g post} (eq : D.gates=pre++g::post) (op : g.op=.or) (read : 3∈g.inputs)
    (bp : ∀ a∈pre,3∉a.inputs) (bs : ∀ a∈post,3∉a.inputs) :
    ∃ j ∈ g.inputs, 9 ≤ j ∧ j < 9+pre.length := by
  by_contra! nh
  apply forbidden_copy D hf hc size eq
  intro x
  have others (i : Nat) (hi : i∈g.inputs) (ne : i≠3) : wire pre x i = false := by
    by_cases raw : i<9
    · exact False.elim ((no_raw_partner D hc eq op bp bs ⟨i,raw⟩ (fun e => ne (congrArg Fin.val e))) hi)
    · have big := nh i hi (by omega)
      unfold wire
      apply List.getD_eq_default
      rw [wiresFrom_length,List.length_ofFn]; omega
  rw [op]
  cases hx : x 3 with
  | false =>
    simp only [GateOp.eval,List.any_map,List.any_eq_false,Function.comp_def,id_eq]
    intro i hi
    by_cases ne : i=3
    · subst i; simp only [Bool.not_eq_true]; exact (raw_wire pre x (3:Fin 9)).trans hx
    · simp [others i hi ne]
  | true =>
    simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_def,id_eq]
    exact ⟨3,read,(raw_wire pre x (3:Fin 9)).trans hx⟩

theorem lift_required (C : Circuit) (hf : FanInTwo C) (hc : Correct C) (hs : C.size ≤ 14) :
    C.size=14 ∧ ∃ pre g post j, (normalized C).gates=pre++g::post ∧ g.op=.or ∧
      (g.inputs=[3,j] ∨ g.inputs=[j,3]) ∧ 9≤j ∧ j<9+pre.length ∧
      (∀ a∈pre,3∉a.inputs) ∧ (∀ a∈post,3∉a.inputs) ∧
      ∀ x : Fin 9 → Bool, sens x → wire pre x j=false := by
  have lo := lower C.size ⟨C,hf,le_rfl,hc⟩
  obtain ⟨pre,g,post,eq,op,r,bp,bs⟩ := shape exact_base C hf hc hs
  let D := normalized C
  have split : D.gates=pre++g::post := eq
  have correct : Correct D := fun x => (norm_eval C _).trans (hc x)
  have fan := norm_fan C hf
  obtain ⟨j,hj,lb,ub⟩ := computed_partner D fan correct (by simpa [D,norm_size] using hs) split op r bp bs
  have len := (fan g (split ▸ List.mem_append_right _ List.mem_cons_self)).2
  have pair : g.inputs=[3,j] ∨ g.inputs=[j,3] := by
    rcases h : g.inputs with _|⟨a,_|⟨b,_|⟨c,more⟩⟩⟩ <;> simp_all
    all_goals omega
  exact ⟨by omega,pre,g,post,j,eq,op,pair,lb,ub,bp,bs,other_off D correct split op bp bs _ hj (by omega)⟩

theorem optimal_restriction (C : Circuit) (hf : FanInTwo C) (hc : Correct C) (hs : C.size ≤ 14) :
    ∃ D : Circuit, FanInTwo D ∧ D.size=13 ∧ ∀ x : Fin 8 → Bool, D.eval (List.ofFn x)=base x := by
  obtain ⟨D,df,ds,de⟩ := PEqualNP.Outside.L_meta_3223 8 C projection 3 0 hf rfl (by decide)
    (by intro h; omega) (sensitive C hc) (varies C hc)
  have ok : ∀ x : Fin 8 → Bool, D.eval (List.ofFn x)=base x :=
    fun x => (de x).trans (restricted C hc x)
  have lb := exact_base D.size ⟨D,df,le_rfl,ok⟩
  exact ⟨D,df,by omega,ok⟩

end Graph10831

namespace Graph10831

def sensitiveMasks : List (Fin 512) := (List.finRange 512).filter fun r =>
  !target (test r.val) && target (Function.update (test r.val) 3 true)

theorem count_sensitive : sensitiveMasks.length = 19 := by decide +kernel

theorem mask_iff (r : Fin 512) : r ∈ sensitiveMasks ↔ sens (test r.val) := by
  simp [sensitiveMasks,sens]

def candidatePairs : List (Fin 9 × Fin 9) :=
  [(0,2),(0,4),(0,5),(0,6),(0,7),(1,5),(1,6),(2,4),(2,6),(2,8),(4,5),(4,7),(5,8)]

/-- Exhausts the two-literal positive conjunctions insensitive on the required rows. -/
theorem pair_test : ∀ a b : Fin 9, a≠3 → b≠3 → a<b →
    ((∀ r ∈ sensitiveMasks, (test r.val a && test r.val b)=false) ↔ (a,b) ∈ candidatePairs) := by
  decide +kernel

theorem sensitive_zero : ∀ a : Fin 9, a≠3 →
    ∃ r ∈ sensitiveMasks, test r.val a=false := by decide +kernel

/-- Inserting the new input inside a private neighbour-OR tree contributes just one centre. -/
theorem one_centre_insufficient : ∀ c : Fin 9, ∃ r : Fin 512,
    target (test r.val) ≠ (target (Function.update (test r.val) 3 false) ||
      (test r.val 3 && test r.val c)) := by decide +kernel

end Graph10831

namespace Graph10831.Star
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
  | atOr a b : Insert (.either a b) (.either (.var 3) (.either a b))
  | atAnd a b : Insert (.both a b) (.either (.var 3) (.both a b))
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
    ∀ x, value x z = (x 3 || value x (neighbours t)) := by
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
  | none => x 3
  | some i => x 3 && x i

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
    (base_ok : ∀ x, value x (stars t)=target (Function.update x 3 false))
    {z : Expr} (edit : Insert (stars t) z) : ¬ ∀ x, value x z=target x := by
  intro good
  obtain ⟨c,effect⟩ := outside _ edit
  cases c with
  | none =>
    have h := effect (test 8)
    rw [good,base_ok] at h
    exact (by decide +kernel : target (test 8) ≠ (Effect none (test 8) || target (Function.update (test 8) 3 false))) h
  | some i =>
    obtain ⟨r,bad⟩ := one_centre_insufficient i
    have h := effect (test r.val)
    rw [good,base_ok] at h
    exact bad (h.trans (Bool.or_comm _ _))

end Graph10831.Star

namespace Graph10831.Weight


abbrev Matrix := Nat → Nat → Int

def col (w : Matrix) (rows : List Nat) (j : Nat) :=
  (rows.map (fun i => w i j)).sum

def rect (w : Matrix) (rows cols : List Nat) :=
  (cols.map (col w rows)).sum

def upper (w : Matrix) (rows cols : List Nat) :=
  (cols.map (fun j => max 0 (col w rows j))).sum

theorem upper_nonneg (w : Matrix) (a b) : 0 ≤ upper w a b := by
  induction b with
  | nil => rfl
  | cons j js ih =>
    simp only [upper,List.map_cons,List.sum_cons] at *
    omega

theorem rect_le_upper (w : Matrix) (a : List Nat) {b c : List Nat} (h : b.Sublist c) :
    rect w a b ≤ upper w a c := by
  induction h with
  | slnil => rfl
  | cons x _ ih =>
    simp only [upper,List.map_cons,List.sum_cons] at *
    omega
  | cons_cons x _ ih =>
    simp only [upper,rect,List.map_cons,List.sum_cons] at *
    omega

theorem split (xs : List Nat) (f : Nat → Int) (p : Nat → Bool) :
    (xs.map f).sum = ((xs.filter p).map f).sum + ((xs.filter (fun i => !p i)).map f).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : p x <;> simp [h] <;> omega

theorem split_cols (w : Matrix) (a b : List Nat) (p : Nat → Bool) :
    rect w a b = rect w a (b.filter p) + rect w a (b.filter (fun i => !p i)) :=
  split b (col w a) p

theorem split_rows (w : Matrix) (a b : List Nat) (p : Nat → Bool) :
    rect w a b = rect w (a.filter p) b + rect w (a.filter (fun i => !p i)) b := by
  induction b with
  | nil => rfl
  | cons j js ih =>
    have h : col w a j = col w (a.filter p) j + col w (a.filter (fun i => !p i)) j :=
      split a (fun i => w i j) p
    simp only [rect, List.map_cons, List.sum_cons] at *
    omega

inductive Formula where
  | var (i : Fin 11)
  | disj (l r : Formula)
  | conj (l r : Formula)

def Formula.eval (v : Fin 11 → Bool) : Formula → Bool
  | .var i => v i
  | .disj l r => l.eval v || r.eval v
  | .conj l r => l.eval v && r.eval v

def Formula.cost (c : Fin 11 → Int) : Formula → Int
  | .var i => c i
  | .disj l r | .conj l r => l.cost c + r.cost c

theorem variable_filter {xs ys : List Nat} (h : xs.Sublist ys) (p : Nat → Bool)
    (yes : ∀ i ∈ xs, p i = true) : xs.Sublist (ys.filter p) := by
  have hh := h.filter p
  rwa [List.filter_eq_self.mpr yes] at hh

theorem formula_bound (w : Matrix) (rows cols : List Nat) (yes no : Nat → Fin 11 → Bool)
    (cost : Fin 11 → Int)
    (cert : ∀ v a b, a.Sublist (rows.filter fun i => yes i v) →
      b.Sublist (cols.filter fun j => !no j v) → rect w a b ≤ cost v)
    (f : Formula) {a b : List Nat} (ha : a.Sublist rows) (hb : b.Sublist cols)
    (hy : ∀ i ∈ a, f.eval (yes i) = true) (hn : ∀ j ∈ b, f.eval (no j) = false) :
    rect w a b ≤ f.cost cost := by
  induction f generalizing a b with
  | var v =>
    exact cert v a b (variable_filter ha _ hy)
      (variable_filter hb _ (fun j hj => by have h : no j v=false := hn j hj; simp [h]))
  | conj l r il ir =>
    let p := fun j => !(l.eval (no j))
    have hl := il ha ((List.filter_sublist (p := p)).trans hb)
      (fun i hi => (Bool.and_eq_true_iff.mp (hy i hi)).1) (by
        intro j hj
        simpa [p] using (List.mem_filter.mp hj).2)
    have hr := ir ha ((List.filter_sublist (p := fun j => !p j)).trans hb)
      (fun i hi => (Bool.and_eq_true_iff.mp (hy i hi)).2) (by
        intro j hj
        have hp : l.eval (no j) = true := by simpa [p] using (List.mem_filter.mp hj).2
        simpa [Formula.eval,hp] using hn j (List.mem_filter.mp hj).1)
    change rect w a b ≤ l.cost cost + r.cost cost
    rw [split_cols w a b p]
    exact add_le_add hl hr
  | disj l r il ir =>
    let p := fun i => l.eval (yes i)
    have hl := il ((List.filter_sublist (p := p)).trans ha) hb
      (fun i hi => (List.mem_filter.mp hi).2)
      (fun j hj => (Bool.or_eq_false_iff.mp (hn j hj)).1)
    have hr := ir ((List.filter_sublist (p := fun i => !p i)).trans ha) hb (by
        intro i hi
        have hp : l.eval (yes i) = false := by simpa [p] using (List.mem_filter.mp hi).2
        simpa [Formula.eval,hp] using hy i (List.mem_filter.mp hi).1)
      (fun j hj => (Bool.or_eq_false_iff.mp (hn j hj)).2)
    change rect w a b ≤ l.cost cost + r.cost cost
    rw [split_rows w a b p]
    exact add_le_add hl hr


def tr (w : Matrix) : Matrix := fun a b => w b a

theorem rect_cons_row (w : Matrix) (i : Nat) (a b : List Nat) :
    rect w (i::a) b = col (tr w) b i + rect w a b := by
  induction b with
  | nil => simp [rect,col]
  | cons j js ih =>
    change col w (i::a) j + rect w (i::a) js = _ + (col w a j + rect w a js)
    rw [ih]
    simp [col,tr]
    omega

theorem transpose (w : Matrix) (a b : List Nat) : rect w a b=rect (tr w) b a := by
  induction a with
  | nil => induction b <;> simp_all [rect,col]
  | cons i is ih => rw [rect_cons_row,ih]; rfl

def rowInput : List Nat := [17, 34, 65, 66, 68, 129, 136, 144, 260, 264, 288]
def colInput : List Nat := [15, 30, 45, 60, 120, 134, 164, 224, 259, 274, 336, 386, 448]
def rows := List.range rowInput.length
def cols := List.range colInput.length
def weights : List (List Int) := [[0, 0, 5, 1, 5, 0, 0, 0, 5, 4, 0, 0, -5], [1, 9, 6, 0, 1, 0, 3, 0, 0, 0, 0, 0, -1], [0, 0, 6, -1, 5, 0, -5, 0, 4, -4, 0, 0, 5], [0, 0, -6, 0, 9, 0, -3, 0, 6, 4, 0, 0, 1], [0, 0, 4, 1, 6, 0, 5, 4, -4, 0, 0, 0, 0], [0, 0, 5, 0, -5, 0, 5, 0, 0, 0, 0, 0, 5], [0, 0, 5, 0, 5, 0, 10, 0, 0, -5, 0, 0, 0], [0, 0, -5, 0, 5, 0, 0, 0, 0, 5, 0, 0, 10], [0, 5, 0, 0, -6, 0, 5, 0, 4, 6, 0, 0, 0], [0, 5, 0, 0, 5, 0, -5, 0, 5, 5, 0, 0, 0], [0, -9, 0, 0, 5, 0, 5, 0, 0, 0, 9, 0, 1]]
def wmat : Matrix := fun i j => (weights.getD i []).getD j 0
def price : Int := 10
def literal (input : Nat) (i : Fin 11) : Bool :=
  if i.val<9 then input.testBit i.val else decide (i.val=10)
def positive (r : Nat) := literal (rowInput.getD r 0)
def negative (r : Nat) := literal (colInput.getD r 0)

def cap (v : Fin 11) : Bool :=
  let rs := rows.filter fun i => positive i v
  let cs := cols.filter fun j => !negative j v
  if rs.isEmpty || cs.isEmpty then true else
  if rs.length ≤ cs.length then rs.sublists.all fun a => decide (upper wmat a cs ≤ price)
  else cs.sublists.all fun b => decide (upper (tr wmat) b rs ≤ price)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem caps : ∀ v : Fin 11, cap v = true := by decide +kernel

theorem literal_bound (v : Fin 11) (a b : List Nat)
    (ha : a.Sublist (rows.filter fun i => positive i v))
    (hb : b.Sublist (cols.filter fun j => !negative j v)) : rect wmat a b ≤ price := by
  have hc := caps v
  dsimp only [cap] at hc
  split at hc
  · rename_i h
    rcases Bool.or_eq_true_iff.mp h with h|h
    · rw [List.isEmpty_iff.mp h] at ha
      have e : a=[] := List.sublist_nil.mp ha
      rw [e,transpose];simp [rect,price]
    · rw [List.isEmpty_iff.mp h] at hb
      have e : b=[] := List.sublist_nil.mp hb
      rw [e];simp [rect,price]
  · split at hc
    · exact (rect_le_upper _ _ hb).trans (decide_eq_true_iff.mp (List.all_eq_true.mp hc _ (List.mem_sublists.mpr ha)))
    · rw [transpose]
      exact (rect_le_upper _ _ ha).trans (decide_eq_true_iff.mp (List.all_eq_true.mp hc _ (List.mem_sublists.mpr hb)))

theorem total : rect wmat rows cols = 151 := by decide +kernel

def Formula.leaves : Formula → Nat
  | .var _ => 1
  | .conj a b | .disj a b => a.leaves+b.leaves

theorem cost_eq (e : Formula) : e.cost (fun _ => price) = price*(e.leaves:Int) := by
  induction e with
  | var _ => simp [Formula.cost,Formula.leaves]
  | conj a b ih jh | disj a b ih jh => simp [Formula.cost,Formula.leaves,ih,jh,mul_add]

theorem trueRows : ∀ r ∈ rowInput, Graph10831.target (Graph10831.test r)=true := by decide +kernel
theorem falseCols : ∀ r ∈ colInput, Graph10831.target (Graph10831.test r)=false := by decide +kernel

theorem getD_in {xs : List Nat} {i : Nat} (hi : i < xs.length) : xs.getD i 0 ∈ xs := by
  simp [List.getD_eq_getElem?_getD,hi]

theorem lower (e : Formula) (ok : ∀ r, e.eval (literal r)=Graph10831.target (Graph10831.test r)) :
    16 ≤ e.leaves := by
  have h := formula_bound wmat rows cols positive negative (fun _ => price) literal_bound e
    (List.Sublist.refl _) (List.Sublist.refl _)
    (fun i hi => (ok _).trans (trueRows _ (getD_in (List.mem_range.mp hi))))
    (fun j hj => (ok _).trans (falseCols _ (getD_in (List.mem_range.mp hj))))
  rw [total,cost_eq] at h
  unfold price at h
  omega
def stars : Formula := (.disj (.disj (.disj (.disj (.conj (.var 0) (.disj (.disj (.var 4) (.var 6)) (.var 7))) (.conj (.var 1) (.disj (.var 5) (.var 6)))) (.conj (.var 2) (.disj (.var 6) (.var 8)))) (.conj (.var 7) (.disj (.var 3) (.var 4)))) (.conj (.var 8) (.disj (.var 3) (.var 5))))
theorem stars_leaves : stars.leaves=16 := rfl
def vector (x : Fin 9 → Bool) (v : Fin 11) : Bool := if h : v.val<9 then x ⟨v.val,h⟩ else decide (v.val=10)
theorem stars_compute : ∀ x : Fin 9 → Bool, stars.eval (vector x)=Graph10831.target x := by decide +kernel
theorem stars_agree (r : Nat) : stars.eval (literal r)=Graph10831.target (Graph10831.test r) := stars_compute (Graph10831.test r)
end Graph10831.Weight

namespace Graph10831.Weight.Unfold
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def base (x : Fin 9 → Bool) (i : Fin 11) := if h : i.val<9 then x ⟨i.val,h⟩ else decide (i.val=10)
def init : List Formula := List.ofFn fun i : Fin 9 => Formula.var ⟨i.val,by omega⟩
def readF (ws : List Formula) (j : Nat) := ws.getD j (.var 9)
def two (f : Formula → Formula → Formula) (k : Fin 11) (ws : List Formula) : List Nat → Formula
  | [] => .var k
  | [a] => readF ws a
  | a::b::_ => f (readF ws a) (readF ws b)
def gateF (ws : List Formula) (g : Gate) : Formula :=
  match g.op with
  | .and => two .conj 10 ws g.inputs
  | .or => two .disj 9 ws g.inputs
  | _ => .var 9
def stepF (ws : List Formula) (g : Gate) := ws++[gateF ws g]
def expand (c : Circuit) := readF (c.gates.foldl stepF init) c.output
def realStep (xs : List Bool) (g : Gate) := xs++[g.op.eval (g.inputs.map fun i => xs.getD i false)]
theorem read_eval (x : Fin 9 → Bool) (ws : List Formula) (j : Nat) :
    (readF ws j).eval (base x)=(ws.map (fun f => f.eval (base x))).getD j false := by
  simp only [readF,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[j]? <;> rfl
theorem gate_eval (x : Fin 9 → Bool) (ws : List Formula) (g : Gate)
    (h : (g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2) :
    (gateF ws g).eval (base x)=g.op.eval (g.inputs.map fun i => (ws.map (fun f => f.eval (base x))).getD i false) := by
  rcases g with ⟨op,ls⟩
  rcases h with ⟨hp,hl⟩
  change op=.and ∨ op=.or at hp
  change ls.length≤2 at hl
  rcases hp with rfl|rfl <;> rcases ls with _|⟨a,_|⟨b,_|⟨c,rest⟩⟩⟩ <;>
    simp_all [gateF,two,Formula.eval,base,GateOp.eval,read_eval]
theorem fold_eval (x : Fin 9 → Bool) (gs : List Gate)
    (h : ∀ g ∈ gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2) (ws : List Formula) :
    (gs.foldl stepF ws).map (fun f => f.eval (base x))=gs.foldl realStep (ws.map (fun f => f.eval (base x))) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,List.foldl_cons, ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]
    simp [stepF,realStep,gate_eval x ws g (h g List.mem_cons_self)]
theorem expand_eval (C : Circuit) (hm : Monotone2 C) (x : Fin 9 → Bool) :
    (expand C).eval (base x) = C.eval (List.ofFn x) := by
  rw [expand,read_eval,fold_eval _ _ (fun g hg => hm g hg)]
  have eq : init.map (fun f => f.eval (base x))=List.ofFn x := by
    rw [init,← List.ofFn_comp']
    rfl
  rw [eq]
  rfl
theorem expanded_lower (C : Circuit) (hm : Monotone2 C) (hc : Graph10831.Correct C) :
    16 ≤ (expand C).leaves := by
  apply Graph10831.Weight.lower
  intro r
  exact (expand_eval C hm (Graph10831.test r)).trans (hc _)
end Graph10831.Weight.Unfold

#print axioms Graph10831.upper
#print axioms Graph10831.lower
#print axioms Graph10831.lift_required
#print axioms Graph10831.optimal_restriction
#print axioms Graph10831.count_sensitive
#print axioms Graph10831.pair_test
#print axioms Graph10831.Star.impossible
#print axioms Graph10831.Weight.lower
#print axioms Graph10831.Weight.stars_agree
#print axioms Graph10831.Weight.Unfold.expanded_lower
