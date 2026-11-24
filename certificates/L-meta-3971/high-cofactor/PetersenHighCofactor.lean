import PetersenSingleInverterSearch

/-!
Setting the distinguished input to one forces at least one ordinary binary gate of every normalized candidate to take a constant operand. Projection drops every such gate and the mandatory reader. The same circuit then computes the high-input function with at most eleven ordinary binary gates and one NOT.
-/


namespace PetersenProgram3971
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
def mask8 : Nat := 2^256-1
def hi8 (a : Nat) := (a >>> 256) &&& mask8
def HConst (a : Nat) := hi8 a=0 ∨ hi8 a=mask8
def HRed (g : Inst) := g.1<2 ∧ (HConst g.2.1 ∨ HConst g.2.2)
def barrier (a : Nat) := fixed 10 a ∨ HConst a

theorem hi8_and (a b : Nat) : hi8 (a &&& b)=hi8 a &&& hi8 b := by
  simp only [hi8,Nat.shiftRight_and_distrib]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and]
  cases mask8.testBit j <;> simp
theorem hi8_or (a b : Nat) : hi8 (a ||| b)=hi8 a ||| hi8 b := by
  simp only [hi8,Nat.shiftRight_or_distrib,Nat.and_or_distrib_right]
theorem hi8_xor (a b : Nat) : hi8 (a ^^^ b)=hi8 a ^^^ hi8 b := by
  simp only [hi8,Nat.shiftRight_xor_distrib,Nat.and_xor_distrib_right]

theorem hi8_mask (a : Nat) : mask8 &&& hi8 a=hi8 a := by
  unfold hi8
  rw [Nat.and_left_comm,Nat.and_self]

theorem hi8_absorb (a : Nat) : mask8 ||| hi8 a=mask8 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or,hi8,Nat.testBit_and]
  cases mask8.testBit i <;> simp

theorem slice_facts : hi8 ones=mask8 ∧ hi8 toggle=mask8 ∧
    (∀ a∈seed,barrier a) ∧ ¬barrier target := by
  unfold barrier HConst fixed
  decide +kernel

theorem fixedAnd10 (a b : Nat) (ha : fixed 10 a) (hb : fixed 10 b) : fixed 10 (a &&& b) := by
  unfold fixed at *; rw [Nat.testBit_and,Nat.testBit_and,ha,hb]
theorem fixedOr10 (a b : Nat) (ha : fixed 10 a) (hb : fixed 10 b) : fixed 10 (a ||| b) := by
  unfold fixed at *; rw [Nat.testBit_or,Nat.testBit_or,ha,hb]
theorem ones_fixed10 : fixed 10 ones := by unfold fixed; decide +kernel
theorem fixedNeg10 (a : Nat) (h : fixed 10 a) : fixed 10 (ones ^^^ a) := by
  have q := ones_fixed10
  unfold fixed at *; rw [Nat.testBit_xor,Nat.testBit_xor,q,h]
theorem constNeg8 (a : Nat) (h : HConst a) : HConst (ones ^^^ a) := by
  rcases h with z|m
  · right; rw [hi8_xor,slice_facts.1,z,Nat.xor_zero]
  · left; rw [hi8_xor,slice_facts.1,m,Nat.xor_self]
theorem highPatch8 (a : Nat) : hi8 (toggle ||| a)=mask8 := by rw [hi8_or,slice_facts.2.1,hi8_absorb]
end PetersenProgram3971

namespace PetersenProgram3971
set_option maxRecDepth 6000
theorem abstract_gate (O T : Nat) (g : Inst) (ok : g.1<4)
    (af : barrier g.2.1) (bf : g.1<2 → barrier g.2.2) (keep : ¬HRed g)
    (negate : ∀ a, barrier a → barrier (O ^^^ a))
    (patch : ∀ a, barrier (T ||| a)) : barrier (applyOp O T g) := by
  obtain ⟨k,a,b⟩ := g
  have input (h : k<2) : fixed 10 a ∧ fixed 10 b := by
    have neither : ¬(HConst a ∨ HConst b) := fun red => keep ⟨h,red⟩
    exact ⟨af.resolve_right (fun x => neither (.inl x)),(bf h).resolve_right (fun x => neither (.inr x))⟩
  cases k with
  | zero => exact Or.inl (fixedAnd10 a b (input (by decide)).1 (input (by decide)).2)
  | succ k =>
    cases k with
    | zero => exact Or.inl (fixedOr10 a b (input (by decide)).1 (input (by decide)).2)
    | succ k =>
      cases k with
      | zero => exact negate a af
      | succ k => exact patch a

theorem barrier_step (g : Inst) (pool : List Nat) (ok : legal pool g)
    (hs : ∀ a∈pool,barrier a) (keep : ¬HRed g) : barrier (applyOp ones toggle g) := by
  have bf (k : g.1<2) : barrier g.2.2 := by
    have mem := (show g.2.2∈pool ∧ g.2.1<g.2.2 from by simpa [k] using ok.2.2).1
    exact hs _ mem
  exact abstract_gate ones toggle g ok.1 (hs _ ok.2.1) bf keep
    (fun a ha => ha.imp (fixedNeg10 a) (constNeg8 a))
    (fun a => Or.inr (Or.inr (highPatch8 a)))

theorem high_gate_collapses (p : List Inst) (sp : solution p) : ∃ g∈p, HRed g := by
  by_contra! none
  have propagate (gs : List Inst) (pool : List Nat) (ok : good toggle pool gs)
      (hs : ∀ a∈pool,barrier a) (no : ∀ g∈gs, ¬HRed g) :
      ∀ a∈gs.foldl (evalWord toggle) pool, barrier a := by
    induction gs generalizing pool with
    | nil => exact hs
    | cons g gs ih =>
      apply ih _ ok.2.2 _ (fun i hi => no i (List.mem_cons_of_mem _ hi))
      intro a ha
      rcases List.mem_append.mp ha with old|new'
      · exact hs a old
      · obtain rfl := List.mem_singleton.mp new'
        exact barrier_step g pool ok.1 hs (no g List.mem_cons_self)
  exact slice_facts.2.2.2 (propagate p seed sp.1 slice_facts.2.2.1 none target sp.2.2.2.2)
end PetersenProgram3971

namespace PetersenProgram3971
set_option maxRecDepth 6000
set_option maxHeartbeats 1200000

instance (g : Inst) : Decidable (HRed g) := by unfold HRed HConst; infer_instance
def keep8 (g : Inst) : Bool := decide (g.1<3 ∧ ¬HRed g)
def cutInst (g : Inst) : Inst := (g.1,hi8 g.2.1,hi8 g.2.2)
def cutProg (p : List Inst) := (p.filter keep8).map cutInst
def eval8 (pool : List Nat) (g : Inst) := pool++[applyOp mask8 0 g]
def valid8 (pool : List Nat) : List Inst → Prop
  | [] => True
  | g::rest => g.1<3 ∧ g.2.1∈pool ∧ (g.1<2 → g.2.2∈pool) ∧ valid8 (eval8 pool g) rest

theorem hi8_step (g : Inst) (h : g.1<3) :
    hi8 (applyOp ones toggle g)=applyOp mask8 0 (cutInst g) := by
  have opcase : g.1=0 ∨ g.1=1 ∨ g.1=2 := by omega
  rcases opcase with z|o|n
  · simp only [applyOp,cutInst,z]; exact hi8_and _ _
  · simp only [applyOp,cutInst,o]; exact hi8_or _ _
  · simp only [applyOp,cutInst,n,hi8_xor,slice_facts.1]

theorem patch_eq8 (g : Inst) (t : g.1=3) : hi8 (applyOp ones toggle g)=mask8 := by
  simp only [applyOp,t,highPatch8]

theorem const_step (g : Inst) (pool : List Nat) (ha : hi8 g.2.1∈pool)
    (hb : g.1<2 → hi8 g.2.2∈pool) (z : 0∈pool) (m : mask8∈pool) (h : HRed g) :
    hi8 (applyOp ones toggle g)∈pool := by
  obtain ⟨k,a,b⟩ := g; obtain ⟨lt,con⟩ := h; change k<2 at lt
  have bmem := hb lt
  change hi8 a∈pool at ha
  change hi8 b∈pool at bmem
  change HConst a ∨ HConst b at con
  interval_cases k
  · change hi8 (a &&& b)∈pool; rw [hi8_and]
    rcases con with (h|h)|(h|h)
    · simpa [h] using z
    · simpa [h,hi8_mask] using bmem
    · simpa [h] using z
    · simpa [h,Nat.and_comm,hi8_mask] using ha
  · change hi8 (a ||| b)∈pool; rw [hi8_or]
    rcases con with (h|h)|(h|h)
    · simpa [h] using bmem
    · simpa [h,hi8_absorb] using m
    · simpa [h] using ha
    · simpa [h,Nat.or_comm,hi8_absorb] using m

theorem project8 (p : List Inst) (src dst : List Nat) (hs : good toggle src p)
    (incl : ∀ a∈src,hi8 a∈dst) (z : 0∈dst) (m : mask8∈dst) :
    valid8 dst (cutProg p) ∧ ∀ y∈p.foldl (evalWord toggle) src, hi8 y∈(cutProg p).foldl eval8 dst := by
  induction p generalizing src dst with
  | nil => exact ⟨trivial,incl⟩
  | cons g gs ih =>
    have ha := incl _ hs.1.2.1
    have hb (b : g.1<2) : hi8 g.2.2∈dst := incl _ (show g.2.2∈src ∧ g.2.1<g.2.2 from by simpa [b] using hs.1.2.2).1
    by_cases h : keep8 g=true
    · have kp := of_decide_eq_true h
      have eq : cutProg (g::gs)=cutInst g::cutProg gs := by simp [cutProg,h]
      rw [eq]
      have inc (a) (mem : a∈evalWord toggle src g) : hi8 a∈eval8 dst (cutInst g) := by
        rcases List.mem_append.mp mem with old|new'
        · exact List.mem_append_left _ (incl _ old)
        · obtain rfl := List.mem_singleton.mp new'
          exact List.mem_append_right _ (List.mem_singleton.mpr (hi8_step g kp.1))
      have rest := ih _ _ hs.2.2 inc (List.mem_append_left _ z) (List.mem_append_left _ m)
      exact ⟨⟨kp.1,ha,hb,rest.1⟩,rest.2⟩
    · have eq : cutProg (g::gs)=cutProg gs := by simp [cutProg,h]
      rw [eq]
      apply ih _ _ hs.2.2 _ z m
      intro a mem
      rcases List.mem_append.mp mem with old|new'
      · exact incl _ old
      · obtain rfl := List.mem_singleton.mp new'
        by_cases red : HRed g
        · exact const_step g dst ha hb z m red
        · have k : g.1=3 := by
            have l := hs.1.1
            have n : ¬g.1<3 := fun x => h (decide_eq_true ⟨x,red⟩)
            omega
          rw [patch_eq8 g k]; exact m

def seed8 := (List.range 8).map (fun i => (List.range 256).foldr (fun r n => Nat.bit (r.testBit i) n) 0) ++ [0,mask8]
def highGraph (r : Nat) := r.testBit 0 || r.testBit 3 ||
  ([(1,2),(1,5),(2,6),(6,4),(4,7),(7,5)] : List (Nat × Nat)).any (fun e => r.testBit e.1 && r.testBit e.2)
theorem high_data : (∀ a∈seed, hi8 a∈seed8) ∧ 0∈seed8 ∧ mask8∈seed8 ∧
    ∀ r : Fin 256, (hi8 target).testBit r.val=highGraph r.val := by decide +kernel

def bin8 (g : Inst) := decide (category g=0)
def neg8 (g : Inst) := decide (category g=2)
def lost8 (g : Inst) := decide (HRed g)

theorem count8 (p : List Inst) :
    (cutProg p).countP bin8 + p.countP lost8=p.countP bin8 ∧
    (cutProg p).countP neg8=p.countP neg8 := by
  induction p with
  | nil => simp [cutProg]
  | cons g gs ih =>
    have c : bin8 (cutInst g)=bin8 g := rfl
    have n : neg8 (cutInst g)=neg8 g := rfl
    by_cases k : keep8 g=true
    · have hg := of_decide_eq_true k
      have eq : cutProg (g::gs)=cutInst g::cutProg gs := by simp [cutProg,k]
      have no : lost8 g=false := decide_eq_false hg.2
      cases bg : bin8 g <;> cases ng : neg8 g <;>
        simp only [eq,List.countP_cons,c,n,no,bg,ng,Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] <;>
        constructor <;> omega
    · have eq : cutProg (g::gs)=cutProg gs := by simp [cutProg,k]
      simp only [eq,List.countP_cons]
      by_cases r : HRed g
      · have b := r.1
        simp [lost8,r,bin8,neg8,category,b,ih.1,ih.2,show g.1<2 from b] <;> omega
      · have l : ¬g.1<3 := fun x => k (decide_eq_true ⟨x,r⟩)
        have b : ¬g.1<2 := by omega
        have x : g.1≠2 := by omega
        have y : g.1≠0 := by omega
        simp [lost8,r,bin8,neg8,category,b,x,y,ih.1,ih.2]

theorem high_restriction (p : List Inst) (sp : solution p) :
    ∃ q : List Inst, valid8 seed8 q ∧ q.countP bin8≤11 ∧ q.countP neg8≤1 ∧
      hi8 target∈q.foldl eval8 seed8 := by
  obtain ⟨fit,out⟩ := project8 p seed seed8 sp.1 high_data.1 high_data.2.1 high_data.2.2.1
  obtain ⟨j,hj,h⟩ := high_gate_collapses p sp
  have pos := List.countP_pos_iff.mpr (show ∃ a∈p,lost8 a=true from ⟨j,hj,decide_eq_true h⟩)
  obtain ⟨b,n⟩ := count8 p
  have cb : p.countP bin8≤12 := sp.2.1
  have cn : p.countP neg8≤1 := sp.2.2.1
  exact ⟨cutProg p,fit,by omega,by omega,out _ sp.2.2.2.2⟩
end PetersenProgram3971

#print axioms PetersenProgram3971.high_gate_collapses
#print axioms PetersenProgram3971.high_restriction
