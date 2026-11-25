import PEqualNP.Outside.L_meta_12118
import PEqualNP.Outside.L_meta_9526
import PEqualNP.MetaComplexity.Helpers.ExactMaj3

-- The majority-of-five lower bound is due to tylerburleigh in L-meta-12118.
-- The circuit elimination and input remapping lemmas are due to hilelyos in L-meta-9526.
-- This file derives exact cofactor costs and reader constraints for L-meta-12119.
-- It checks the one-port modifications of four specified ten-gate constructions
-- and gives explicit optimal circuits for a family of nearby six-input functions.


namespace Simlowker.Cofactors12119
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_12118
open PEqualNP.MetaComplexity.Helpers.ExactMaj3

def side (b : Bool) (x : Fin 5 → Bool) := f (Fin.snoc x b)
def majority5 (x : Fin 5 → Bool) : Bool :=
  decide (3 ≤ (Finset.univ.filter fun i : Fin 5 => x i = true).card)
def low (x : Fin 5 → Bool) : Bool :=
  maj3 (fun i : Fin 3 => x i.castSucc.castSucc) && (x 3 || x 4)

theorem high_formula : ∀ x, side true x = majority5 x := by decide +kernel
theorem low_formula : ∀ x, side false x = low x := by decide +kernel

def highWitness : Circuit := ⟨[
  ⟨.and,[0,1]⟩, ⟨.and,[3,4]⟩, ⟨.or,[5,6]⟩, ⟨.and,[2,7]⟩,
  ⟨.or,[3,4]⟩, ⟨.or,[0,1]⟩, ⟨.or,[2,7]⟩, ⟨.and,[10,11]⟩,
  ⟨.and,[9,12]⟩, ⟨.or,[8,13]⟩],14⟩
def lowWitness : Circuit := ⟨[
  ⟨.and,[0,1]⟩, ⟨.or,[0,1]⟩, ⟨.and,[6,2]⟩, ⟨.or,[5,7]⟩,
  ⟨.or,[3,4]⟩, ⟨.and,[8,9]⟩],10⟩

theorem highWitness_ok : Monotone2 highWitness ∧ FanInTwo highWitness := by
  simp [Monotone2,FanInTwo,highWitness]
theorem lowWitness_ok : Monotone2 lowWitness ∧ FanInTwo lowWitness := by
  simp [Monotone2,FanInTwo,lowWitness]
theorem highWitness_correct : ∀ x, highWitness.eval (List.ofFn x) = side true x := by decide +kernel
theorem lowWitness_correct : ∀ x, lowWitness.eval (List.ofFn x) = side false x := by decide +kernel

def emb (i : Fin 5) : Fin 7 := i.castLE (by decide)
def fiveVars : List BF := List.ofFn fun i : Fin 5 => var (emb i)

theorem lower_high (s : ℕ) (h : HasCircuitSize 5 (side true) s) : 10 ≤ s := by
  obtain ⟨C,legal,cost,comp⟩ := h
  have agree : ∀ x : Fin 7 → Bool, majority x = side true (fun i => x (emb i)) := by decide +kernel
  have htarget : (wiresF C.gates fiveVars).getD C.output zF = majority := by
    funext x
    rw [agree, ← comp, ← getD_map_x, ← wires_eq]
    simp only [Circuit.eval, Circuit.wires, fiveVars, List.map_ofFn]
    rfl
  have used := trans_binary C.gates fiveVars (sourceVars firstFive) (show GOK C.gates from legal) (by
    intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact Or.inr ⟨emb i, (by decide +kernel : ∀ j, emb j ∈ firstFive) i, ori_zp rfl⟩) C.output
  rw [htarget,ori_zp (by decide : majority (fun _ => false) = false)] at used
  obtain zero | good := used
  · exact False.elim ((by decide : majority (assignment 7) ≠ false) (congrFun zero (assignment 7)))
  · have n := countBinary_le C.gates
    change C.gates.length ≤ s at cost
    by_contra! small
    exact majority_binary (UC_le (by omega) good)

theorem lower_low (s : ℕ) (h : HasCircuitSize 5 (side false) s) : 6 ≤ s := by
  obtain ⟨t,hst,ht⟩ := PEqualNP.Outside.L_meta_9526.gate_elim_one 4 (side false) false s
    ⟨fun i => decide (i.val < 3),by decide +kernel⟩
    ⟨fun _ => false,fun _ => true,by decide +kernel⟩ h
  obtain ⟨u,htu,hu⟩ := PEqualNP.Outside.L_meta_9526.gate_elim_one 3
    (fun z : Fin 4 → Bool => side false (Fin.snoc z false)) true t
    ⟨fun i => decide (i.val < 3),by decide +kernel⟩
    ⟨fun _ => false,fun _ => true,by decide +kernel⟩ ht
  have eq : (fun z : Fin 3 → Bool => side false (Fin.snoc (Fin.snoc z true) false)) = maj3 := by
    funext z
    exact (by decide +kernel : ∀ v : Fin 3 → Bool, side false (Fin.snoc (Fin.snoc v true) false) = maj3 v) z
  rw [eq] at hu
  have := (maj3_size u).1 hu
  omega

theorem exact_cofactors (b : Bool) (s : ℕ) :
    HasCircuitSize 5 (side b) s ↔ (if b then 10 else 6) ≤ s := by
  cases b
  · exact ⟨lower_low s, fun h => ⟨lowWitness, lowWitness_ok.2, h, lowWitness_correct⟩⟩
  · exact ⟨lower_high s, fun h => ⟨highWitness, highWitness_ok.2, h, highWitness_correct⟩⟩

theorem negated_assignment_is_false : ¬ ¬ (∀ s : ℕ, HasCircuitSize 6 f s →
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = f x) :=
  fun impossible => impossible PEqualNP.Outside.L_meta_12118

end Simlowker.Cofactors12119


namespace Simlowker.Cofactors12119
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_9526

def uses (k : ℕ) (g : Gate) := decide (k ∈ g.inputs)

theorem count_pass (n k : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (ok : ∀ g ∈ gs, NOk g) (raw : k < acc.1.length)
    (tag : ∃ b : Bool, acc.1.getD k (.inl false) = .inl b) :
    (elim n gs acc).2.length + gs.countP (uses k) ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elim]
  | cons g gs ih =>
    rw [elim_cons]
    have tail := ih (elimStep n acc g) (fun g' hg => ok _ (List.mem_cons_of_mem _ hg))
      (by simp [elimStep]; omega) (by
        obtain ⟨b,hb⟩ := tag
        refine ⟨b,?_⟩
        simp only [elimStep]
        rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hb)
    set vals := g.inputs.map fun i => acc.1.getD i (.inl false) with hv
    set opt := (simplify g.op (n+acc.2.length) vals).1 with ho
    have len : (elimStep n acc g).2.length = acc.2.length + opt.toList.length := by
      simp [elimStep,ho,hv]
    rw [len] at tail
    by_cases read : k ∈ g.inputs
    · obtain ⟨b,hb⟩ := tag
      have gok := ok g List.mem_cons_self
      have gone : opt = none := simplify_count _ _ _ gok.1.1 (by simpa [hv] using gok.1.2)
        (fun h => by simpa [hv] using gok.2 h) ⟨b,List.mem_map.mpr ⟨k,read,hb⟩⟩
      rw [gone] at tail
      simp [List.countP_cons,uses,read] at tail ⊢
      omega
    · have bound := toList_length_le opt
      simp [List.countP_cons,uses,read] at tail ⊢
      omega

theorem restrict_count (n : ℕ) (f : BFn (n+1)) (b : Bool) (C : Circuit)
    (ok : FanInTwo C) (comp : ∀ x, C.eval (List.ofFn x) = f x)
    (hnc : ∃ x y : Fin n → Bool, f (Fin.snoc x b) ≠ f (Fin.snoc y b)) :
    ∃ t, t + (C.gates.map normGate).countP (uses n) ≤ C.size ∧
      HasCircuitSize n (fun y => f (Fin.snoc y b)) t := by
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g₀,h₀,rfl⟩ := List.mem_map.mp hg
    exact normGate_nok g₀ (ok g₀ h₀)
  have hevg : ∀ x : Fin (n+1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x; rw [hgs,wiresFrom_norm,← comp]; rfl
  set acc := elim n gs (initStats n b,[]) with hacc
  have hinv : ∀ y : Fin n → Bool, Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b))) acc := by
    intro y; rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool, statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (.inl false)) =
      f (Fin.snoc y b) := by
    intro y; rw [((hinv y).2 C.output).2,hevg]
  cases hout : acc.1.getD C.output (.inl false) with
  | inl c =>
    obtain ⟨x,y,hxy⟩ := hnc
    exact False.elim (hxy (by rw [← hval x,← hval y,hout]; rfl))
  | inr j =>
    have budget := count_pass n n gs (initStats n b,[]) hnok
      (by simp [initStats]) ⟨b,getD_snoc_len _ _ _ _ (by simp)⟩
    have bound : acc.2.length + gs.countP (uses n) ≤ C.size := by
      rw [← hacc] at budget
      simpa [hgs,Circuit.size] using budget
    refine ⟨acc.2.length,bound,⟨acc.2,j⟩,elim_ok n gs _ (by simp),le_rfl,?_⟩
    intro y
    have := hval y
    rw [hout] at this
    exact this

open PEqualNP.Outside.L_meta_12118 in
theorem sixth_reader_budget (C : Circuit) (ok : FanInTwo C)
    (hc : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = f x) :
    10 + (C.gates.map normGate).countP (uses 5) ≤ C.size := by
  obtain ⟨t,h,ht⟩ := restrict_count 5 f true C ok hc
    ⟨fun _ => false,fun _ => true,by decide +kernel⟩
  have lo := lower_high t ht
  omega
end Simlowker.Cofactors12119

namespace Simlowker.Cofactors12119
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9526
-- Directional form of hilelyos's two-gate argument in L-meta-9526.
theorem two_saved_at (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Sum.inl false) ≠ Sum.inl c) :
    ∀ b₀ : Bool, (∀ g ∈ gs, n ∈ g.inputs → fixBit g = b₀) → (elim n gs (initStats n b₀, [])).2.length + 2 ≤ gs.length := by
  intro b₀ same
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Sum.inl false) = Sum.inl b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Sum.inl false)
      = Sum.inl b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · have a1 : (elim n pre (initStats n b₀, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n b₀, []) hpren (by simp [initStats])
        ⟨b₀, initStats_last n b₀⟩ h1
    have := hF b₀
    have := hB2 b₀
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n b₀, [])) g) hpostn
      (by rw [hBl]; omega) ⟨b₀, hBn b₀⟩ h2
    have := hA2 b₀
    have := hB2 b₀
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  have bit := same g hg hng
  rw [← bit]
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

theorem gate_elim_two_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (C : Circuit) (b₀ : Bool)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (ok : FanInTwo C) (hev : ∀ x, C.eval (List.ofFn x) = f x)
    (same : ∀ g ∈ C.gates.map normGate, n ∈ g.inputs → fixBit g = b₀) :
    ∃ s', s' + 2 ≤ C.size ∧ HasCircuitSize n (fun y => f (Fin.snoc y b₀)) s' := by
  have hsz' : C.gates.length = C.size := rfl
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      statVal (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y))
        ((elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) ≠ Sum.inl c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  have hb := two_saved_at n gs hnok C.output hsupp hout b₀ same
  cases hst : (elim n gs (initStats n b₀, [])).1.getD C.output (Sum.inl false) with
  | inl c => exact absurd hst (hout b₀ c)
  | inr j =>
    refine ⟨(elim n gs (initStats n b₀, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b₀, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b₀ y
    rw [hst] at this
    exact this

open PEqualNP.Outside.L_meta_12118 in
theorem tight_reader (C : Circuit) (legal : FanInTwo C)
    (hc : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = f x) (small : C.size ≤ 11) :
    Monotone2 C ∧ (C.gates.map normGate).countP (uses 5) = 1 ∧
    ∃ g ∈ C.gates, 5 ∈ g.inputs ∧ g.op = GateOp.and := by
  have noNot : ¬ ∃ g ∈ C.gates, g.op = GateOp.not := by
    intro h
    have lb := binary_lower C legal hc
    have lt := countBinary_lt C.gates h
    change C.gates.length ≤ 11 at small
    omega
  have mono : Monotone2 C := by
    intro g hg
    obtain ⟨ops,arity⟩ := legal g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ops ⊢
    exact ⟨ops.imp_right (fun h => h.resolve_right (fun hn => noNot ⟨g,hg,hn⟩)),arity⟩
  have sameGate : ∀ g ∈ C.gates, normGate g = g := by
    intro g hg
    have ops := (mono g hg).1
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops
    rcases g with ⟨o,ins⟩
    rcases ops with h | h <;> dsimp at h <;> subst o <;> rfl
  have needed : ∃ g ∈ C.gates, 5 ∈ g.inputs ∧ g.op = GateOp.and := by
    by_contra h
    obtain ⟨t,ht,cf⟩ := gate_elim_two_at 5 f C true
      ⟨fun i => decide (i.val < 3),by decide +kernel⟩
      (by intro b; exact ⟨fun _ => false, fun _ => true, (by decide +kernel : ∀ b : Bool, f (Fin.snoc (fun _ : Fin 5 => false) b) ≠ f (Fin.snoc (fun _ : Fin 5 => true) b)) b⟩)
      legal hc (by
        intro g hg reads
        obtain ⟨orig,mem,rfl⟩ := List.mem_map.mp hg
        rw [sameGate orig mem] at reads ⊢
        have ops := (mono orig mem).1
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops
        have op := ops.resolve_left (fun ha => h ⟨orig,mem,reads,ha⟩)
        simp [fixBit,op])
    have := lower_high t cf
    omega
  obtain ⟨g,mem,reads,op⟩ := needed
  have occ : g ∈ C.gates.map normGate := List.mem_map.mpr ⟨g,mem,sameGate g mem⟩
  have pos : 0 < (C.gates.map normGate).countP (uses 5) :=
    List.countP_pos_iff.mpr ⟨g,occ,by simpa [uses] using reads⟩
  have bound := sixth_reader_budget C legal hc
  exact ⟨mono,by omega,g,mem,reads,op⟩
end Simlowker.Cofactors12119


namespace Simlowker.Cofactors12119.Guard
open PEqualNP.Outside.L_meta_12118
def pivotal (v : Fin 5 → Bool) := side false v != side true v

theorem pivotal_rows : ∀ v : Fin 5 → Bool,
    pivotal v = decide (PEqualNP.MetaComplexity.tableIndex v ∈ ([7,25,26,28] : List Nat)) := by decide +kernel

theorem and_guard (h : (Fin 5 → Bool) → Bool) :
    (∀ b v, side b v = side (b && h v) v) ↔
    (∀ v, pivotal v = true → h v = true) := by
  constructor
  · intro hv v hp
    specialize hv true v
    cases hh : h v
    · simp [hh] at hv
      simp [pivotal,hv] at hp
    · rfl
  · intro hv b v
    cases hh : h v
    · have eq : side false v = side true v := by
        by_contra hn
        have bad := hv v (by simpa [pivotal] using hn)
        simp [hh] at bad
      cases b <;> simp [hh,eq]
    · simp [hh]

theorem single_gate_guard : ∀ (i j : Fin 5) (useOr : Bool),
    (∀ v : Fin 5 → Bool, pivotal v = true → (if useOr then v i || v j else v i && v j) = true)
      ↔ (useOr = true ∧ ((i.val < 3 ∧ 3 ≤ j.val) ∨ (j.val < 3 ∧ 3 ≤ i.val))) := by decide +kernel

abbrev Step := Bool × Nat × Nat
def templates : List (List Step) := [
  [(false, 0, 1), (false, 2, 3), (true, 0, 1), (true, 2, 3), (false, 7, 8), (false, 4, 9), (true, 4, 9), (true, 5, 10), (true, 6, 12), (false, 11, 13)],
  [(false, 0, 1), (false, 2, 3), (true, 0, 1), (true, 2, 3), (false, 7, 8), (true, 5, 6), (false, 4, 10), (true, 4, 10), (false, 9, 12), (true, 11, 13)],
  [(false, 0, 1), (false, 2, 3), (true, 0, 1), (true, 2, 3), (false, 7, 8), (true, 5, 6), (false, 4, 10), (true, 4, 10), (true, 9, 11), (false, 12, 13)],
  [(false, 0, 1), (false, 2, 3), (true, 0, 1), (true, 2, 3), (false, 7, 8), (true, 5, 6), (false, 9, 10), (true, 9, 10), (false, 4, 12), (true, 11, 13)]
]
-- Each pair of ports reads an AND or OR gate. Port 20 reads the output.
def readPorts (gs : List Step) (wire : Nat) : List Nat :=
  ((gs.flatMap fun (g : Step) => [g.2.1,g.2.2]) ++ [14]).zipIdx.filterMap
    fun (i,port) => if i = wire then some port else none

def nonemptyCuts (gs : List Step) : List (List Nat) :=
  (List.range 15).flatMap fun wire => (readPorts gs wire).sublists.filter (fun s => !s.isEmpty)

def cutValue (gs : List Step) (dual : Bool) (ports : List Nat) (r : Nat) : Bool :=
  let roots := (List.range 5).map fun i => r.testBit i
  let vals := gs.zipIdx.foldl (fun (ws : List Bool) (g,k) =>
    let readAt := fun i j => !(ports.contains j) && ws.getD i false
    let a := readAt g.2.1 (2*k)
    let b := readAt g.2.2 (2*k+1)
    ws ++ [if g.1 != dual then a || b else a && b]) roots
  !(ports.contains 20) && vals.getD 14 false

def pairLow (p q r : Nat) : Bool :=
  (r.testBit p || r.testBit q) &&
    decide (2 ≤ ((List.range 5).filter fun i => i != p && i != q && r.testBit i).length)

def pairs : List (Nat × Nat) :=
  (List.range 5).flatMap fun i => ((List.range i).map fun j => (j,i))

-- A witness row for each template, polarity, pair of special inputs and selectable cut.
def check (gs : List Step) (dual : Bool) (pq : Nat × Nat) (rs : List Nat) : Bool :=
  let cs := nonemptyCuts gs
  cs.length == rs.length && (cs.zip rs).all fun (c,r) =>
    decide (r < 32) && (cutValue gs dual c r != pairLow pq.1 pq.2 r)

def rows00 : List (List Nat) := [
  [28, 7, 13, 28, 7, 14, 7, 11, 11, 7, 7, 7, 7, 7, 7, 28, 7, 13, 13, 7, 13, 13, 7, 13, 21, 13, 13],
  [11, 7, 11, 11, 7, 11, 7, 13, 14, 7, 7, 7, 7, 7, 7, 11, 7, 11, 11, 7, 11, 11, 7, 11, 11, 11, 11],
  [11, 7, 11, 11, 7, 11, 7, 14, 13, 7, 7, 7, 7, 7, 7, 11, 7, 11, 11, 7, 11, 11, 7, 11, 11, 11, 11],
  [7, 11, 7, 7, 11, 7, 11, 7, 7, 11, 13, 14, 11, 11, 11, 7, 11, 7, 7, 11, 7, 7, 11, 7, 7, 7, 7],
  [7, 11, 7, 7, 11, 7, 11, 7, 7, 11, 14, 13, 11, 11, 11, 7, 11, 7, 7, 11, 7, 7, 11, 7, 7, 7, 7],
  [7, 14, 7, 7, 13, 7, 19, 7, 7, 19, 11, 11, 13, 13, 13, 7, 19, 7, 7, 13, 7, 7, 13, 7, 7, 7, 7],
  [7, 13, 7, 7, 19, 7, 13, 7, 7, 13, 11, 11, 14, 14, 14, 7, 13, 7, 7, 14, 7, 7, 14, 7, 7, 7, 7],
  [7, 19, 7, 7, 13, 7, 14, 7, 7, 14, 11, 11, 13, 13, 13, 7, 14, 7, 7, 13, 7, 7, 13, 7, 7, 7, 7],
  [7, 11, 7, 7, 11, 7, 11, 7, 7, 11, 21, 13, 11, 11, 11, 7, 11, 7, 7, 11, 7, 7, 11, 7, 7, 7, 7],
  [11, 7, 11, 11, 7, 11, 7, 21, 13, 7, 7, 7, 7, 7, 7, 11, 7, 11, 11, 7, 11, 11, 7, 11, 11, 11, 11]
]
set_option maxHeartbeats 0 in
theorem checked00 : (pairs.zip rows00).all (fun (pq,rs) => check (templates.getD 0 []) false pq rs) = true := by decide +kernel

def rows01 : List (List Nat) := [
  [7, 28, 13, 7, 28, 14, 11, 7, 11, 7, 7, 7, 7, 7, 7, 13, 13, 28, 7, 13, 7, 13, 13, 7, 13, 13, 13],
  [7, 11, 11, 7, 11, 11, 13, 7, 14, 7, 7, 7, 7, 7, 7, 11, 11, 11, 7, 11, 7, 11, 11, 7, 11, 11, 11],
  [7, 11, 11, 7, 11, 11, 14, 7, 13, 7, 7, 7, 7, 7, 7, 11, 11, 11, 7, 11, 7, 11, 11, 7, 11, 11, 11],
  [11, 7, 7, 11, 7, 7, 7, 11, 7, 13, 11, 14, 11, 11, 11, 7, 7, 7, 11, 7, 11, 7, 7, 11, 7, 7, 7],
  [11, 7, 7, 11, 7, 7, 7, 11, 7, 14, 11, 13, 11, 11, 11, 7, 7, 7, 11, 7, 11, 7, 7, 11, 7, 7, 7],
  [14, 7, 7, 13, 7, 7, 7, 19, 7, 11, 19, 11, 13, 13, 13, 7, 7, 7, 19, 7, 13, 7, 7, 13, 7, 7, 7],
  [13, 7, 7, 19, 7, 7, 7, 13, 7, 11, 13, 11, 14, 14, 14, 7, 7, 7, 13, 7, 14, 7, 7, 14, 7, 7, 7],
  [19, 7, 7, 13, 7, 7, 7, 14, 7, 11, 14, 11, 13, 13, 13, 7, 7, 7, 14, 7, 13, 7, 7, 13, 7, 7, 7],
  [11, 7, 7, 11, 7, 7, 7, 11, 7, 21, 11, 13, 11, 11, 11, 7, 7, 7, 11, 7, 11, 7, 7, 11, 7, 7, 7],
  [7, 11, 11, 7, 11, 11, 21, 7, 13, 7, 7, 7, 7, 7, 7, 11, 11, 11, 7, 11, 7, 11, 11, 7, 11, 11, 11]
]
set_option maxHeartbeats 0 in
theorem checked01 : (pairs.zip rows01).all (fun (pq,rs) => check (templates.getD 0 []) true pq rs) = true := by decide +kernel

def rows10 : List (List Nat) := [
  [28, 7, 13, 28, 7, 14, 7, 11, 11, 7, 7, 7, 7, 7, 7, 28, 7, 13, 13, 13, 7, 13, 13, 7, 13, 13, 13],
  [11, 7, 11, 11, 7, 11, 7, 13, 14, 7, 7, 7, 7, 7, 7, 11, 7, 11, 11, 11, 7, 11, 11, 7, 11, 11, 11],
  [11, 7, 11, 11, 7, 11, 7, 14, 13, 7, 7, 7, 7, 7, 7, 11, 7, 11, 11, 11, 7, 11, 11, 7, 11, 11, 11],
  [7, 11, 7, 7, 11, 7, 11, 7, 7, 11, 13, 14, 11, 11, 11, 7, 11, 7, 7, 7, 11, 7, 7, 11, 7, 7, 7],
  [7, 11, 7, 7, 11, 7, 11, 7, 7, 11, 14, 13, 11, 11, 11, 7, 11, 7, 7, 7, 11, 7, 7, 11, 7, 7, 7],
  [7, 14, 7, 7, 13, 7, 19, 7, 7, 19, 11, 11, 13, 13, 13, 7, 19, 7, 7, 7, 13, 7, 7, 13, 7, 7, 7],
  [7, 13, 7, 7, 19, 7, 13, 7, 7, 13, 11, 11, 14, 14, 14, 7, 13, 7, 7, 7, 14, 7, 7, 14, 7, 7, 7],
  [7, 19, 7, 7, 13, 7, 14, 7, 7, 14, 11, 11, 13, 13, 13, 7, 14, 7, 7, 7, 13, 7, 7, 13, 7, 7, 7],
  [7, 11, 7, 7, 11, 7, 11, 7, 7, 11, 21, 13, 11, 11, 11, 7, 11, 7, 7, 7, 11, 7, 7, 11, 7, 7, 7],
  [11, 7, 11, 11, 7, 11, 7, 21, 13, 7, 7, 7, 7, 7, 7, 11, 7, 11, 11, 11, 7, 11, 11, 7, 11, 11, 11]
]
set_option maxHeartbeats 0 in
theorem checked10 : (pairs.zip rows10).all (fun (pq,rs) => check (templates.getD 1 []) false pq rs) = true := by decide +kernel

def rows11 : List (List Nat) := [
  [7, 28, 13, 7, 28, 14, 11, 7, 11, 7, 7, 7, 7, 7, 7, 13, 13, 28, 7, 13, 13, 7, 13, 13, 7, 13, 13],
  [7, 11, 11, 7, 11, 11, 13, 7, 14, 7, 7, 7, 7, 7, 7, 11, 11, 11, 7, 11, 11, 7, 11, 11, 7, 11, 11],
  [7, 11, 11, 7, 11, 11, 14, 7, 13, 7, 7, 7, 7, 7, 7, 11, 11, 11, 7, 11, 11, 7, 11, 11, 7, 11, 11],
  [11, 7, 7, 11, 7, 7, 7, 11, 7, 13, 11, 14, 11, 11, 11, 7, 7, 7, 11, 7, 7, 11, 7, 7, 11, 7, 7],
  [11, 7, 7, 11, 7, 7, 7, 11, 7, 14, 11, 13, 11, 11, 11, 7, 7, 7, 11, 7, 7, 11, 7, 7, 11, 7, 7],
  [14, 7, 7, 13, 7, 7, 7, 19, 7, 11, 19, 11, 13, 13, 13, 7, 7, 7, 19, 7, 7, 13, 7, 7, 13, 7, 7],
  [13, 7, 7, 19, 7, 7, 7, 13, 7, 11, 13, 11, 14, 14, 14, 7, 7, 7, 13, 7, 7, 14, 7, 7, 14, 7, 7],
  [19, 7, 7, 13, 7, 7, 7, 14, 7, 11, 14, 11, 13, 13, 13, 7, 7, 7, 14, 7, 7, 13, 7, 7, 13, 7, 7],
  [11, 7, 7, 11, 7, 7, 7, 11, 7, 21, 11, 13, 11, 11, 11, 7, 7, 7, 11, 7, 7, 11, 7, 7, 11, 7, 7],
  [7, 11, 11, 7, 11, 11, 21, 7, 13, 7, 7, 7, 7, 7, 7, 11, 11, 11, 7, 11, 11, 7, 11, 11, 7, 11, 11]
]
set_option maxHeartbeats 0 in
theorem checked11 : (pairs.zip rows11).all (fun (pq,rs) => check (templates.getD 1 []) true pq rs) = true := by decide +kernel

def rows20 : List (List Nat) := [
  [28, 7, 13, 28, 7, 14, 7, 11, 11, 7, 7, 7, 7, 7, 7, 28, 7, 13, 13, 13, 7, 13, 13, 7, 13, 13, 13],
  [11, 7, 11, 11, 7, 11, 7, 13, 14, 7, 7, 7, 7, 7, 7, 11, 7, 11, 11, 11, 7, 11, 11, 7, 11, 11, 11],
  [11, 7, 11, 11, 7, 11, 7, 14, 13, 7, 7, 7, 7, 7, 7, 11, 7, 11, 11, 11, 7, 11, 11, 7, 11, 11, 11],
  [7, 11, 7, 7, 11, 7, 11, 7, 7, 11, 13, 14, 11, 11, 11, 7, 11, 7, 7, 7, 11, 7, 7, 11, 7, 7, 7],
  [7, 11, 7, 7, 11, 7, 11, 7, 7, 11, 14, 13, 11, 11, 11, 7, 11, 7, 7, 7, 11, 7, 7, 11, 7, 7, 7],
  [7, 14, 7, 7, 13, 7, 19, 7, 7, 19, 11, 11, 13, 13, 13, 7, 19, 7, 7, 7, 13, 7, 7, 13, 7, 7, 7],
  [7, 13, 7, 7, 19, 7, 13, 7, 7, 13, 11, 11, 14, 14, 14, 7, 13, 7, 7, 7, 14, 7, 7, 14, 7, 7, 7],
  [7, 19, 7, 7, 13, 7, 14, 7, 7, 14, 11, 11, 13, 13, 13, 7, 14, 7, 7, 7, 13, 7, 7, 13, 7, 7, 7],
  [7, 11, 7, 7, 11, 7, 11, 7, 7, 11, 21, 13, 11, 11, 11, 7, 11, 7, 7, 7, 11, 7, 7, 11, 7, 7, 7],
  [11, 7, 11, 11, 7, 11, 7, 21, 13, 7, 7, 7, 7, 7, 7, 11, 7, 11, 11, 11, 7, 11, 11, 7, 11, 11, 11]
]
set_option maxHeartbeats 0 in
theorem checked20 : (pairs.zip rows20).all (fun (pq,rs) => check (templates.getD 2 []) false pq rs) = true := by decide +kernel

def rows21 : List (List Nat) := [
  [7, 28, 13, 7, 28, 14, 11, 7, 11, 7, 7, 7, 7, 7, 7, 13, 13, 28, 7, 13, 13, 7, 13, 13, 7, 13, 13],
  [7, 11, 11, 7, 11, 11, 13, 7, 14, 7, 7, 7, 7, 7, 7, 11, 11, 11, 7, 11, 11, 7, 11, 11, 7, 11, 11],
  [7, 11, 11, 7, 11, 11, 14, 7, 13, 7, 7, 7, 7, 7, 7, 11, 11, 11, 7, 11, 11, 7, 11, 11, 7, 11, 11],
  [11, 7, 7, 11, 7, 7, 7, 11, 7, 13, 11, 14, 11, 11, 11, 7, 7, 7, 11, 7, 7, 11, 7, 7, 11, 7, 7],
  [11, 7, 7, 11, 7, 7, 7, 11, 7, 14, 11, 13, 11, 11, 11, 7, 7, 7, 11, 7, 7, 11, 7, 7, 11, 7, 7],
  [14, 7, 7, 13, 7, 7, 7, 19, 7, 11, 19, 11, 13, 13, 13, 7, 7, 7, 19, 7, 7, 13, 7, 7, 13, 7, 7],
  [13, 7, 7, 19, 7, 7, 7, 13, 7, 11, 13, 11, 14, 14, 14, 7, 7, 7, 13, 7, 7, 14, 7, 7, 14, 7, 7],
  [19, 7, 7, 13, 7, 7, 7, 14, 7, 11, 14, 11, 13, 13, 13, 7, 7, 7, 14, 7, 7, 13, 7, 7, 13, 7, 7],
  [11, 7, 7, 11, 7, 7, 7, 11, 7, 21, 11, 13, 11, 11, 11, 7, 7, 7, 11, 7, 7, 11, 7, 7, 11, 7, 7],
  [7, 11, 11, 7, 11, 11, 21, 7, 13, 7, 7, 7, 7, 7, 7, 11, 11, 11, 7, 11, 11, 7, 11, 11, 7, 11, 11]
]
set_option maxHeartbeats 0 in
theorem checked21 : (pairs.zip rows21).all (fun (pq,rs) => check (templates.getD 2 []) true pq rs) = true := by decide +kernel

def rows30 : List (List Nat) := [
  [28, 7, 13, 28, 7, 14, 7, 11, 11, 7, 7, 7, 7, 28, 7, 13, 13, 13, 7, 13, 13, 7, 13, 13, 7, 7, 13],
  [11, 7, 11, 11, 7, 11, 7, 13, 14, 7, 7, 7, 7, 11, 7, 11, 11, 11, 7, 11, 11, 7, 11, 11, 7, 7, 11],
  [11, 7, 11, 11, 7, 11, 7, 14, 13, 7, 7, 7, 7, 11, 7, 11, 11, 11, 7, 11, 11, 7, 11, 11, 7, 7, 11],
  [7, 11, 7, 7, 11, 7, 11, 7, 7, 11, 13, 14, 11, 7, 11, 7, 7, 7, 11, 7, 7, 11, 7, 7, 11, 11, 7],
  [7, 11, 7, 7, 11, 7, 11, 7, 7, 11, 14, 13, 11, 7, 11, 7, 7, 7, 11, 7, 7, 11, 7, 7, 11, 11, 7],
  [7, 14, 7, 7, 13, 7, 19, 7, 7, 19, 11, 11, 13, 7, 19, 7, 7, 7, 13, 7, 7, 13, 7, 7, 13, 13, 7],
  [7, 13, 7, 7, 19, 7, 13, 7, 7, 13, 11, 11, 14, 7, 13, 7, 7, 7, 14, 7, 7, 14, 7, 7, 14, 14, 7],
  [7, 19, 7, 7, 13, 7, 14, 7, 7, 14, 11, 11, 13, 7, 14, 7, 7, 7, 13, 7, 7, 13, 7, 7, 13, 13, 7],
  [7, 11, 7, 7, 11, 7, 11, 7, 7, 11, 21, 13, 11, 7, 11, 7, 7, 7, 11, 7, 7, 11, 7, 7, 11, 11, 7],
  [11, 7, 11, 11, 7, 11, 7, 21, 13, 7, 7, 7, 7, 11, 7, 11, 11, 11, 7, 11, 11, 7, 11, 11, 7, 7, 11]
]
set_option maxHeartbeats 0 in
theorem checked30 : (pairs.zip rows30).all (fun (pq,rs) => check (templates.getD 3 []) false pq rs) = true := by decide +kernel

def rows31 : List (List Nat) := [
  [7, 28, 13, 7, 28, 14, 11, 7, 11, 7, 7, 7, 7, 13, 13, 28, 7, 7, 13, 13, 7, 13, 13, 13, 13, 13, 13],
  [7, 11, 11, 7, 11, 11, 13, 7, 14, 7, 7, 7, 7, 11, 11, 11, 7, 7, 11, 11, 7, 11, 11, 11, 11, 11, 11],
  [7, 11, 11, 7, 11, 11, 14, 7, 13, 7, 7, 7, 7, 11, 11, 11, 7, 7, 11, 11, 7, 11, 11, 11, 11, 11, 11],
  [11, 7, 7, 11, 7, 7, 7, 11, 7, 13, 11, 14, 11, 7, 7, 7, 11, 11, 7, 7, 11, 7, 7, 7, 7, 7, 7],
  [11, 7, 7, 11, 7, 7, 7, 11, 7, 14, 11, 13, 11, 7, 7, 7, 11, 11, 7, 7, 11, 7, 7, 7, 7, 7, 7],
  [14, 7, 7, 13, 7, 7, 7, 19, 7, 11, 19, 11, 13, 7, 7, 7, 19, 13, 7, 7, 13, 7, 7, 7, 7, 7, 7],
  [13, 7, 7, 19, 7, 7, 7, 13, 7, 11, 13, 11, 14, 7, 7, 7, 13, 14, 7, 7, 14, 7, 7, 7, 7, 7, 7],
  [19, 7, 7, 13, 7, 7, 7, 14, 7, 11, 14, 11, 13, 7, 7, 7, 14, 13, 7, 7, 13, 7, 7, 7, 7, 7, 7],
  [11, 7, 7, 11, 7, 7, 7, 11, 7, 21, 11, 13, 11, 7, 7, 7, 11, 11, 7, 7, 11, 7, 7, 7, 7, 7, 7],
  [7, 11, 11, 7, 11, 11, 21, 7, 13, 7, 7, 7, 7, 11, 11, 11, 7, 7, 11, 11, 7, 11, 11, 11, 11, 11, 11]
]
set_option maxHeartbeats 0 in
theorem checked31 : (pairs.zip rows31).all (fun (pq,rs) => check (templates.getD 3 []) true pq rs) = true := by decide +kernel

def rows : List (List (List Nat)) := [rows00,rows01,rows10,rows11,rows20,rows21,rows30,rows31]

set_option maxHeartbeats 0 in
theorem checks (i : Fin 4) (d : Bool) :
    (pairs.zip (rows.getD (2*i.val + d.toNat) [])).all
      (fun (pq,rs) => check (templates.getD i.val []) d pq rs) = true := by
  fin_cases i <;> cases d
  · exact checked00
  · exact checked01
  · exact checked10
  · exact checked11
  · exact checked20
  · exact checked21
  · exact checked30
  · exact checked31

theorem single_insertion_fails (i : Fin 4) (d : Bool) (pq : Nat × Nat) (hp : pq ∈ pairs)
    (cut : List Nat) (hc : cut ∈ nonemptyCuts (templates.getD i.val [])) :
    ∃ r < 32, cutValue (templates.getD i.val []) d cut r ≠ pairLow pq.1 pq.2 r := by
  let hints := rows.getD (2*i.val + d.toNat) []
  have hlen : pairs.length = hints.length := by
    fin_cases i <;> cases d <;> decide
  obtain ⟨j,hj,ej⟩ := List.mem_iff_getElem.mp hp
  have jh : j < hints.length := hlen ▸ hj
  have hit : (pq,hints[j]) ∈ pairs.zip hints := by
    apply List.mem_iff_getElem.mpr
    refine ⟨j,by simpa [List.length_zip] using (lt_min hj jh),?_⟩
    simpa [ej]
  have ck := List.all_eq_true.mp (checks i d) _ hit
  have eq := (Bool.and_eq_true_iff.mp ck).1
  have all := (Bool.and_eq_true_iff.mp ck).2
  have lens : (nonemptyCuts (templates.getD i.val [])).length = hints[j].length := by
    simpa using eq
  obtain ⟨k,hk,ek⟩ := List.mem_iff_getElem.mp hc
  have kh : k < hints[j].length := lens ▸ hk
  have got : (cut,hints[j][k]) ∈ (nonemptyCuts (templates.getD i.val [])).zip hints[j] := by
    apply List.mem_iff_getElem.mpr
    refine ⟨k,by simpa [List.length_zip] using (lt_min hk kh),?_⟩
    simpa [ek]
  have out := Bool.and_eq_true_iff.mp (List.all_eq_true.mp all _ got)
  exact ⟨hints[j][k],of_decide_eq_true out.1,by simpa using out.2⟩
end Simlowker.Cofactors12119.Guard

namespace Simlowker.Cofactors12119
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_12118

-- Any six-input function that depends on the last input and restricts to majority
-- at true needs eleven gates, even allowing NOT at every gate position.
theorem majority_extension_lower (G : (Fin 6 → Bool) → Bool) (s : ℕ)
    (high : ∀ z : Fin 5 → Bool, G (Fin.snoc z true) = side true z)
    (dep : ∃ x : Fin 6 → Bool, G (Function.update x (Fin.last 5) (!x (Fin.last 5))) ≠ G x)
    (h : HasCircuitSize 6 G s) : 11 ≤ s := by
  obtain ⟨t,ht,cf⟩ := PEqualNP.Outside.L_meta_9526.gate_elim_one 5 G true s dep
    ⟨fun _ => false, fun _ => true, by rw [high,high]; decide +kernel⟩ h
  have eq : (fun z : Fin 5 → Bool => G (Fin.snoc z true)) = side true := funext high
  rw [eq] at cf
  have := lower_high t cf
  omega

def neighbor (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276676736 * 2^32 + 3907577984) (tableIndex x)

def nearWitness : Circuit := ⟨[
  ⟨.and,[3,4]⟩, ⟨.and,[0,1]⟩, ⟨.and,[6,5]⟩, ⟨.or,[7,8]⟩,
  ⟨.and,[2,9]⟩, ⟨.or,[3,4]⟩, ⟨.or,[0,1]⟩, ⟨.or,[2,9]⟩,
  ⟨.and,[12,13]⟩, ⟨.and,[11,14]⟩, ⟨.or,[10,15]⟩],16⟩

theorem unique_difference : ∀ x : Fin 6 → Bool,
    (neighbor x != f x) = decide (tableIndex x = 7) := by decide +kernel
theorem neighbor_basis : Monotone2 nearWitness ∧ FanInTwo nearWitness := by
  simp [Monotone2,FanInTwo,nearWitness]
theorem neighbor_eval : ∀ x : Fin 6 → Bool, nearWitness.eval (List.ofFn x) = neighbor x := by decide +kernel
theorem neighbor_exact (s : ℕ) : HasCircuitSize 6 neighbor s ↔ 11 ≤ s := by
  refine ⟨majority_extension_lower neighbor s (by decide +kernel) ?_,fun h =>
    ⟨nearWitness,neighbor_basis.2,h,neighbor_eval⟩⟩
  exact ⟨fun i => decide (i.val = 0 ∨ i.val = 3 ∨ i.val = 4),by decide +kernel⟩
end Simlowker.Cofactors12119

namespace Simlowker.Cofactors12119.Family
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def word (hi lo : ℕ) (x : Fin 6 → Bool) := Nat.testBit (hi*2^32+lo) (tableIndex x)
def majority (x : Fin 5 → Bool) := Nat.testBit 4276676736 (tableIndex x)
def restricted (v : Fin 6) (f : (Fin 6 → Bool) → Bool) : (Fin 6 → Bool) → Bool :=
  fun x => f (x ∘ Equiv.swap v (Fin.last 5))
theorem lower_majority (s : ℕ) (h : HasCircuitSize 5 majority s) : 10 ≤ s := by
  have eq : majority = side true := funext (by decide +kernel)
  rw [eq] at h
  exact lower_high s h
theorem extension (f : (Fin 6 → Bool) → Bool) (v : Fin 6) (b : Bool)
    (branch : ∀ x : Fin 5 → Bool, restricted v f (Fin.snoc x b) = majority x)
    (dep : ∃ x : Fin 6 → Bool, restricted v f (Function.update x (Fin.last 5) (!x (Fin.last 5))) ≠ restricted v f x)
    (s : ℕ) (h : HasCircuitSize 6 f s) : 11 ≤ s := by
  have remapped := PEqualNP.Outside.L_meta_9526.remap_size (⇑(Equiv.swap v (Fin.last 5))) f s h
  obtain ⟨t,ht,c⟩ := PEqualNP.Outside.L_meta_9526.gate_elim_one 5 (restricted v f) b s dep
    ⟨fun _ => false, fun _ => true, by rw [branch,branch]; decide +kernel⟩ remapped
  have eq : (fun x : Fin 5 → Bool => restricted v f (Fin.snoc x b)) = majority := funext branch
  rw [eq] at c
  have := lower_majority t c
  omega
end Simlowker.Cofactors12119.Family

namespace Simlowker.Cofactors12119.Family
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def circN0 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [4,3]⟩, ⟨.and, [2,7]⟩, ⟨.or, [0,1]⟩, ⟨.or, [2,7]⟩, ⟨.and, [9,10]⟩, ⟨.and, [5,11]⟩, ⟨.or, [5,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [8,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN0 := word 4276676840 3900735616
theorem basisN0 : Monotone2 circN0 ∧ FanInTwo circN0 := by simp [Monotone2,FanInTwo,circN0]
theorem evalN0 : ∀ x : Fin 6 → Bool, circN0.eval (List.ofFn x) = funcN0 x := by decide +kernel
theorem lowerN0 (s : ℕ) (h : HasCircuitSize 6 funcN0 s) : 11 ≤ s :=
  extension funcN0 3 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (19 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN0 (s : ℕ) : HasCircuitSize 6 funcN0 s ↔ 11 ≤ s :=
  ⟨lowerN0 s, fun h => ⟨circN0,(basisN0).2,h,evalN0⟩⟩
def circN1 : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [4,3]⟩, ⟨.or, [2,7]⟩, ⟨.and, [0,1]⟩, ⟨.and, [2,7]⟩, ⟨.or, [9,10]⟩, ⟨.or, [5,11]⟩, ⟨.and, [5,11]⟩, ⟨.and, [6,12]⟩, ⟨.and, [8,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN1 := word 4278124264 3907577984
theorem basisN1 : Monotone2 circN1 ∧ FanInTwo circN1 := by simp [Monotone2,FanInTwo,circN1]
theorem evalN1 : ∀ x : Fin 6 → Bool, circN1.eval (List.ofFn x) = funcN1 x := by decide +kernel
theorem lowerN1 (s : ℕ) (h : HasCircuitSize 6 funcN1 s) : 11 ≤ s :=
  extension funcN1 3 false (by decide +kernel)
    ⟨(fun j : Fin 6 => (3 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN1 (s : ℕ) : HasCircuitSize 6 funcN1 s ↔ 11 ≤ s :=
  ⟨lowerN1 s, fun h => ⟨circN1,(basisN1).2,h,evalN1⟩⟩
def circN2 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [3,5]⟩, ⟨.and, [2,7]⟩, ⟨.or, [0,1]⟩, ⟨.or, [2,7]⟩, ⟨.and, [9,10]⟩, ⟨.and, [4,11]⟩, ⟨.or, [4,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [8,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN2 := word 4276676736 3907551360
theorem basisN2 : Monotone2 circN2 ∧ FanInTwo circN2 := by simp [Monotone2,FanInTwo,circN2]
theorem evalN2 : ∀ x : Fin 6 → Bool, circN2.eval (List.ofFn x) = funcN2 x := by decide +kernel
theorem lowerN2 (s : ℕ) (h : HasCircuitSize 6 funcN2 s) : 11 ≤ s :=
  extension funcN2 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (11 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN2 (s : ℕ) : HasCircuitSize 6 funcN2 s ↔ 11 ≤ s :=
  ⟨lowerN2 s, fun h => ⟨circN2,(basisN2).2,h,evalN2⟩⟩
def circN3 : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [3,5]⟩, ⟨.or, [2,7]⟩, ⟨.and, [0,1]⟩, ⟨.and, [2,7]⟩, ⟨.or, [9,10]⟩, ⟨.or, [4,11]⟩, ⟨.and, [4,11]⟩, ⟨.and, [6,12]⟩, ⟨.and, [8,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN3 := word 4278118632 4276676736
theorem basisN3 : Monotone2 circN3 ∧ FanInTwo circN3 := by simp [Monotone2,FanInTwo,circN3]
theorem evalN3 : ∀ x : Fin 6 → Bool, circN3.eval (List.ofFn x) = funcN3 x := by decide +kernel
theorem lowerN3 (s : ℕ) (h : HasCircuitSize 6 funcN3 s) : 11 ≤ s :=
  extension funcN3 5 false (by decide +kernel)
    ⟨(fun j : Fin 6 => (3 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN3 (s : ℕ) : HasCircuitSize 6 funcN3 s ↔ 11 ≤ s :=
  ⟨lowerN3 s, fun h => ⟨circN3,(basisN3).2,h,evalN3⟩⟩
def circ12292 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [2,3]⟩, ⟨.or, [0,1]⟩, ⟨.or, [2,3]⟩, ⟨.and, [8,9]⟩, ⟨.and, [4,5]⟩, ⟨.and, [11,10]⟩, ⟨.or, [11,10]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def func12292 := word 4276676736 3900762240
theorem basis12292 : Monotone2 circ12292 ∧ FanInTwo circ12292 := by simp [Monotone2,FanInTwo,circ12292]
theorem eval12292 : ∀ x : Fin 6 → Bool, circ12292.eval (List.ofFn x) = func12292 x := by decide +kernel
theorem lower12292 (s : ℕ) (h : HasCircuitSize 6 func12292 s) : 11 ≤ s :=
  extension func12292 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (19 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exact12292 (s : ℕ) : HasCircuitSize 6 func12292 s ↔ 11 ≤ s :=
  ⟨lower12292 s, fun h => ⟨circ12292,(basis12292).2,h,eval12292⟩⟩
def circ12343 : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [2,3]⟩, ⟨.and, [0,1]⟩, ⟨.and, [2,3]⟩, ⟨.or, [8,9]⟩, ⟨.or, [5,4]⟩, ⟨.or, [11,10]⟩, ⟨.and, [11,10]⟩, ⟨.and, [6,12]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def func12343 := word 4276682472 4276676736
theorem basis12343 : Monotone2 circ12343 ∧ FanInTwo circ12343 := by simp [Monotone2,FanInTwo,circ12343]
theorem eval12343 : ∀ x : Fin 6 → Bool, circ12343.eval (List.ofFn x) = func12343 x := by decide +kernel
theorem lower12343 (s : ℕ) (h : HasCircuitSize 6 func12343 s) : 11 ≤ s :=
  extension func12343 4 false (by decide +kernel)
    ⟨(fun j : Fin 6 => (3 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exact12343 (s : ℕ) : HasCircuitSize 6 func12343 s ↔ 11 ≤ s :=
  ⟨lower12343 s, fun h => ⟨circ12343,(basis12343).2,h,eval12343⟩⟩
def circN6 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [2,4]⟩, ⟨.or, [0,1]⟩, ⟨.or, [2,4]⟩, ⟨.and, [8,9]⟩, ⟨.and, [5,10]⟩, ⟨.and, [10,3]⟩, ⟨.or, [5,12]⟩, ⟨.or, [6,11]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN6 := word 4278118632 3892346880
theorem basisN6 : Monotone2 circN6 ∧ FanInTwo circN6 := by simp [Monotone2,FanInTwo,circN6]
theorem evalN6 : ∀ x : Fin 6 → Bool, circN6.eval (List.ofFn x) = funcN6 x := by decide +kernel
theorem lowerN6 (s : ℕ) (h : HasCircuitSize 6 funcN6 s) : 11 ≤ s :=
  extension funcN6 3 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN6 (s : ℕ) : HasCircuitSize 6 funcN6 s ↔ 11 ≤ s :=
  ⟨lowerN6 s, fun h => ⟨circN6,(basisN6).2,h,evalN6⟩⟩
def circN7 : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [2,4]⟩, ⟨.and, [0,1]⟩, ⟨.and, [2,4]⟩, ⟨.or, [8,9]⟩, ⟨.or, [5,10]⟩, ⟨.or, [10,3]⟩, ⟨.and, [5,12]⟩, ⟨.and, [6,11]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN7 := word 4294901736 3907551360
theorem basisN7 : Monotone2 circN7 ∧ FanInTwo circN7 := by simp [Monotone2,FanInTwo,circN7]
theorem evalN7 : ∀ x : Fin 6 → Bool, circN7.eval (List.ofFn x) = funcN7 x := by decide +kernel
theorem lowerN7 (s : ℕ) (h : HasCircuitSize 6 funcN7 s) : 11 ≤ s :=
  extension funcN7 3 false (by decide +kernel)
    ⟨(fun j : Fin 6 => (8 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN7 (s : ℕ) : HasCircuitSize 6 funcN7 s ↔ 11 ≤ s :=
  ⟨lowerN7 s, fun h => ⟨circN7,(basisN7).2,h,evalN7⟩⟩
def circN8 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [2,3]⟩, ⟨.or, [0,1]⟩, ⟨.or, [2,3]⟩, ⟨.and, [8,9]⟩, ⟨.and, [5,10]⟩, ⟨.and, [10,4]⟩, ⟨.or, [5,12]⟩, ⟨.or, [6,11]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN8 := word 4276682472 3900702720
theorem basisN8 : Monotone2 circN8 ∧ FanInTwo circN8 := by simp [Monotone2,FanInTwo,circN8]
theorem evalN8 : ∀ x : Fin 6 → Bool, circN8.eval (List.ofFn x) = funcN8 x := by decide +kernel
theorem lowerN8 (s : ℕ) (h : HasCircuitSize 6 funcN8 s) : 11 ≤ s :=
  extension funcN8 4 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN8 (s : ℕ) : HasCircuitSize 6 funcN8 s ↔ 11 ≤ s :=
  ⟨lowerN8 s, fun h => ⟨circN8,(basisN8).2,h,evalN8⟩⟩
def circN9 : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [2,3]⟩, ⟨.and, [0,1]⟩, ⟨.and, [2,3]⟩, ⟨.or, [8,9]⟩, ⟨.or, [5,10]⟩, ⟨.or, [10,4]⟩, ⟨.and, [5,12]⟩, ⟨.and, [6,11]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN9 := word 4294967016 3900762240
theorem basisN9 : Monotone2 circN9 ∧ FanInTwo circN9 := by simp [Monotone2,FanInTwo,circN9]
theorem evalN9 : ∀ x : Fin 6 → Bool, circN9.eval (List.ofFn x) = funcN9 x := by decide +kernel
theorem lowerN9 (s : ℕ) (h : HasCircuitSize 6 funcN9 s) : 11 ≤ s :=
  extension funcN9 4 false (by decide +kernel)
    ⟨(fun j : Fin 6 => (16 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN9 (s : ℕ) : HasCircuitSize 6 funcN9 s ↔ 11 ≤ s :=
  ⟨lowerN9 s, fun h => ⟨circN9,(basisN9).2,h,evalN9⟩⟩
def circN10 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [2,3]⟩, ⟨.or, [0,1]⟩, ⟨.or, [2,3]⟩, ⟨.and, [8,9]⟩, ⟨.and, [4,10]⟩, ⟨.and, [10,5]⟩, ⟨.or, [4,12]⟩, ⟨.or, [6,11]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN10 := word 4276676736 4276617216
theorem basisN10 : Monotone2 circN10 ∧ FanInTwo circN10 := by simp [Monotone2,FanInTwo,circN10]
theorem evalN10 : ∀ x : Fin 6 → Bool, circN10.eval (List.ofFn x) = funcN10 x := by decide +kernel
theorem lowerN10 (s : ℕ) (h : HasCircuitSize 6 funcN10 s) : 11 ≤ s :=
  extension funcN10 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN10 (s : ℕ) : HasCircuitSize 6 funcN10 s ↔ 11 ≤ s :=
  ⟨lowerN10 s, fun h => ⟨circN10,(basisN10).2,h,evalN10⟩⟩
def circN11 : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [2,3]⟩, ⟨.and, [0,1]⟩, ⟨.and, [2,3]⟩, ⟨.or, [8,9]⟩, ⟨.or, [4,10]⟩, ⟨.or, [10,5]⟩, ⟨.and, [4,12]⟩, ⟨.and, [6,11]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN11 := word 4294961280 4276676736
theorem basisN11 : Monotone2 circN11 ∧ FanInTwo circN11 := by simp [Monotone2,FanInTwo,circN11]
theorem evalN11 : ∀ x : Fin 6 → Bool, circN11.eval (List.ofFn x) = funcN11 x := by decide +kernel
theorem lowerN11 (s : ℕ) (h : HasCircuitSize 6 funcN11 s) : 11 ≤ s :=
  extension funcN11 5 false (by decide +kernel)
    ⟨(fun j : Fin 6 => (16 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN11 (s : ℕ) : HasCircuitSize 6 funcN11 s ↔ 11 ≤ s :=
  ⟨lowerN11 s, fun h => ⟨circN11,(basisN11).2,h,evalN11⟩⟩
def circ12040 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [2,4]⟩, ⟨.or, [0,1]⟩, ⟨.or, [2,4]⟩, ⟨.and, [8,9]⟩, ⟨.and, [5,10]⟩, ⟨.or, [5,10]⟩, ⟨.or, [6,11]⟩, ⟨.or, [7,13]⟩, ⟨.and, [12,3]⟩, ⟨.and, [15,14]⟩], 16⟩
def func12040 := word 4261472256 3892346880
theorem basis12040 : Monotone2 circ12040 ∧ FanInTwo circ12040 := by simp [Monotone2,FanInTwo,circ12040]
theorem eval12040 : ∀ x : Fin 6 → Bool, circ12040.eval (List.ofFn x) = func12040 x := by decide +kernel
theorem lower12040 (s : ℕ) (h : HasCircuitSize 6 func12040 s) : 11 ≤ s :=
  extension func12040 3 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exact12040 (s : ℕ) : HasCircuitSize 6 func12040 s ↔ 11 ≤ s :=
  ⟨lower12040 s, fun h => ⟨circ12040,(basis12040).2,h,eval12040⟩⟩
def circN13 : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [2,4]⟩, ⟨.and, [0,1]⟩, ⟨.and, [2,4]⟩, ⟨.or, [8,9]⟩, ⟨.or, [5,10]⟩, ⟨.and, [5,10]⟩, ⟨.and, [6,11]⟩, ⟨.and, [7,13]⟩, ⟨.or, [12,3]⟩, ⟨.or, [15,14]⟩], 16⟩
def funcN13 := word 4294901736 4293459840
theorem basisN13 : Monotone2 circN13 ∧ FanInTwo circN13 := by simp [Monotone2,FanInTwo,circN13]
theorem evalN13 : ∀ x : Fin 6 → Bool, circN13.eval (List.ofFn x) = funcN13 x := by decide +kernel
theorem lowerN13 (s : ℕ) (h : HasCircuitSize 6 funcN13 s) : 11 ≤ s :=
  extension funcN13 3 false (by decide +kernel)
    ⟨(fun j : Fin 6 => (0 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN13 (s : ℕ) : HasCircuitSize 6 funcN13 s ↔ 11 ≤ s :=
  ⟨lowerN13 s, fun h => ⟨circN13,(basisN13).2,h,evalN13⟩⟩
def circN14 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [2,3]⟩, ⟨.or, [0,1]⟩, ⟨.or, [2,3]⟩, ⟨.and, [8,9]⟩, ⟨.and, [5,10]⟩, ⟨.or, [5,10]⟩, ⟨.or, [6,11]⟩, ⟨.or, [7,13]⟩, ⟨.and, [12,4]⟩, ⟨.and, [15,14]⟩], 16⟩
def funcN14 := word 4276617216 3900702720
theorem basisN14 : Monotone2 circN14 ∧ FanInTwo circN14 := by simp [Monotone2,FanInTwo,circN14]
theorem evalN14 : ∀ x : Fin 6 → Bool, circN14.eval (List.ofFn x) = funcN14 x := by decide +kernel
theorem lowerN14 (s : ℕ) (h : HasCircuitSize 6 funcN14 s) : 11 ≤ s :=
  extension funcN14 4 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN14 (s : ℕ) : HasCircuitSize 6 funcN14 s ↔ 11 ≤ s :=
  ⟨lowerN14 s, fun h => ⟨circN14,(basisN14).2,h,evalN14⟩⟩
def circN15 : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [2,3]⟩, ⟨.and, [0,1]⟩, ⟨.and, [2,3]⟩, ⟨.or, [8,9]⟩, ⟨.or, [5,10]⟩, ⟨.and, [5,10]⟩, ⟨.and, [6,11]⟩, ⟨.and, [7,13]⟩, ⟨.or, [12,4]⟩, ⟨.or, [15,14]⟩], 16⟩
def funcN15 := word 4294967016 4294961280
theorem basisN15 : Monotone2 circN15 ∧ FanInTwo circN15 := by simp [Monotone2,FanInTwo,circN15]
theorem evalN15 : ∀ x : Fin 6 → Bool, circN15.eval (List.ofFn x) = funcN15 x := by decide +kernel
theorem lowerN15 (s : ℕ) (h : HasCircuitSize 6 funcN15 s) : 11 ≤ s :=
  extension funcN15 4 false (by decide +kernel)
    ⟨(fun j : Fin 6 => (0 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN15 (s : ℕ) : HasCircuitSize 6 funcN15 s ↔ 11 ≤ s :=
  ⟨lowerN15 s, fun h => ⟨circN15,(basisN15).2,h,evalN15⟩⟩
def circN16 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [2,3]⟩, ⟨.or, [0,1]⟩, ⟨.or, [2,3]⟩, ⟨.and, [8,9]⟩, ⟨.and, [4,10]⟩, ⟨.or, [4,10]⟩, ⟨.or, [6,11]⟩, ⟨.or, [7,13]⟩, ⟨.and, [12,5]⟩, ⟨.and, [15,14]⟩], 16⟩
def funcN16 := word 4276676736 0
theorem basisN16 : Monotone2 circN16 ∧ FanInTwo circN16 := by simp [Monotone2,FanInTwo,circN16]
theorem evalN16 : ∀ x : Fin 6 → Bool, circN16.eval (List.ofFn x) = funcN16 x := by decide +kernel
theorem lowerN16 (s : ℕ) (h : HasCircuitSize 6 funcN16 s) : 11 ≤ s :=
  extension funcN16 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN16 (s : ℕ) : HasCircuitSize 6 funcN16 s ↔ 11 ≤ s :=
  ⟨lowerN16 s, fun h => ⟨circN16,(basisN16).2,h,evalN16⟩⟩
def circN17 : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [2,3]⟩, ⟨.and, [0,1]⟩, ⟨.and, [2,3]⟩, ⟨.or, [8,9]⟩, ⟨.or, [4,10]⟩, ⟨.and, [4,10]⟩, ⟨.and, [6,11]⟩, ⟨.and, [7,13]⟩, ⟨.or, [12,5]⟩, ⟨.or, [15,14]⟩], 16⟩
def funcN17 := word 4294967295 4276676736
theorem basisN17 : Monotone2 circN17 ∧ FanInTwo circN17 := by simp [Monotone2,FanInTwo,circN17]
theorem evalN17 : ∀ x : Fin 6 → Bool, circN17.eval (List.ofFn x) = funcN17 x := by decide +kernel
theorem lowerN17 (s : ℕ) (h : HasCircuitSize 6 funcN17 s) : 11 ≤ s :=
  extension funcN17 5 false (by decide +kernel)
    ⟨(fun j : Fin 6 => (0 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN17 (s : ℕ) : HasCircuitSize 6 funcN17 s ↔ 11 ≤ s :=
  ⟨lowerN17 s, fun h => ⟨circN17,(basisN17).2,h,evalN17⟩⟩
def circN18 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [2,5]⟩, ⟨.or, [0,1]⟩, ⟨.or, [2,5]⟩, ⟨.and, [8,9]⟩, ⟨.and, [4,10]⟩, ⟨.and, [10,3]⟩, ⟨.or, [4,12]⟩, ⟨.or, [6,11]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN18 := word 4278118400 3907551232
theorem basisN18 : Monotone2 circN18 ∧ FanInTwo circN18 := by simp [Monotone2,FanInTwo,circN18]
theorem evalN18 : ∀ x : Fin 6 → Bool, circN18.eval (List.ofFn x) = funcN18 x := by decide +kernel
theorem lowerN18 (s : ℕ) (h : HasCircuitSize 6 funcN18 s) : 11 ≤ s :=
  extension funcN18 3 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN18 (s : ℕ) : HasCircuitSize 6 funcN18 s ↔ 11 ≤ s :=
  ⟨lowerN18 s, fun h => ⟨circN18,(basisN18).2,h,evalN18⟩⟩
def circN19 : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [2,5]⟩, ⟨.and, [0,1]⟩, ⟨.and, [2,5]⟩, ⟨.or, [8,9]⟩, ⟨.or, [4,10]⟩, ⟨.or, [10,3]⟩, ⟨.and, [4,12]⟩, ⟨.and, [6,11]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN19 := word 4294895848 4293427328
theorem basisN19 : Monotone2 circN19 ∧ FanInTwo circN19 := by simp [Monotone2,FanInTwo,circN19]
theorem evalN19 : ∀ x : Fin 6 → Bool, circN19.eval (List.ofFn x) = funcN19 x := by decide +kernel
theorem lowerN19 (s : ℕ) (h : HasCircuitSize 6 funcN19 s) : 11 ≤ s :=
  extension funcN19 3 false (by decide +kernel)
    ⟨(fun j : Fin 6 => (16 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN19 (s : ℕ) : HasCircuitSize 6 funcN19 s ↔ 11 ≤ s :=
  ⟨lowerN19 s, fun h => ⟨circN19,(basisN19).2,h,evalN19⟩⟩
def circN20 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [2,5]⟩, ⟨.or, [0,1]⟩, ⟨.or, [2,5]⟩, ⟨.and, [8,9]⟩, ⟨.and, [3,10]⟩, ⟨.and, [10,4]⟩, ⟨.or, [3,12]⟩, ⟨.or, [6,11]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN20 := word 4276682240 3900762112
theorem basisN20 : Monotone2 circN20 ∧ FanInTwo circN20 := by simp [Monotone2,FanInTwo,circN20]
theorem evalN20 : ∀ x : Fin 6 → Bool, circN20.eval (List.ofFn x) = funcN20 x := by decide +kernel
theorem lowerN20 (s : ℕ) (h : HasCircuitSize 6 funcN20 s) : 11 ≤ s :=
  extension funcN20 4 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN20 (s : ℕ) : HasCircuitSize 6 funcN20 s ↔ 11 ≤ s :=
  ⟨lowerN20 s, fun h => ⟨circN20,(basisN20).2,h,evalN20⟩⟩
def circN21 : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [2,5]⟩, ⟨.and, [0,1]⟩, ⟨.and, [2,5]⟩, ⟨.or, [8,9]⟩, ⟨.or, [3,10]⟩, ⟨.or, [10,4]⟩, ⟨.and, [3,12]⟩, ⟨.and, [6,11]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN21 := word 4293459688 4286638208
theorem basisN21 : Monotone2 circN21 ∧ FanInTwo circN21 := by simp [Monotone2,FanInTwo,circN21]
theorem evalN21 : ∀ x : Fin 6 → Bool, circN21.eval (List.ofFn x) = funcN21 x := by decide +kernel
theorem lowerN21 (s : ℕ) (h : HasCircuitSize 6 funcN21 s) : 11 ≤ s :=
  extension funcN21 4 false (by decide +kernel)
    ⟨(fun j : Fin 6 => (8 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN21 (s : ℕ) : HasCircuitSize 6 funcN21 s ↔ 11 ≤ s :=
  ⟨lowerN21 s, fun h => ⟨circN21,(basisN21).2,h,evalN21⟩⟩
def circ12124 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [2,4]⟩, ⟨.or, [0,1]⟩, ⟨.or, [2,4]⟩, ⟨.and, [8,9]⟩, ⟨.and, [3,10]⟩, ⟨.and, [10,5]⟩, ⟨.or, [3,12]⟩, ⟨.or, [6,11]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def func12124 := word 4276676736 4261472256
theorem basis12124 : Monotone2 circ12124 ∧ FanInTwo circ12124 := by simp [Monotone2,FanInTwo,circ12124]
theorem eval12124 : ∀ x : Fin 6 → Bool, circ12124.eval (List.ofFn x) = func12124 x := by decide +kernel
theorem lower12124 (s : ℕ) (h : HasCircuitSize 6 func12124 s) : 11 ≤ s :=
  extension func12124 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exact12124 (s : ℕ) : HasCircuitSize 6 func12124 s ↔ 11 ≤ s :=
  ⟨lower12124 s, fun h => ⟨circ12124,(basis12124).2,h,eval12124⟩⟩
def circN23 : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [2,4]⟩, ⟨.and, [0,1]⟩, ⟨.and, [2,4]⟩, ⟨.or, [8,9]⟩, ⟨.or, [3,10]⟩, ⟨.or, [10,5]⟩, ⟨.and, [3,12]⟩, ⟨.and, [6,11]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN23 := word 4293459840 4276676736
theorem basisN23 : Monotone2 circN23 ∧ FanInTwo circN23 := by simp [Monotone2,FanInTwo,circN23]
theorem evalN23 : ∀ x : Fin 6 → Bool, circN23.eval (List.ofFn x) = funcN23 x := by decide +kernel
theorem lowerN23 (s : ℕ) (h : HasCircuitSize 6 funcN23 s) : 11 ≤ s :=
  extension funcN23 5 false (by decide +kernel)
    ⟨(fun j : Fin 6 => (8 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN23 (s : ℕ) : HasCircuitSize 6 funcN23 s ↔ 11 ≤ s :=
  ⟨lowerN23 s, fun h => ⟨circN23,(basisN23).2,h,evalN23⟩⟩
def circN24 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [4,3]⟩, ⟨.and, [7,5]⟩, ⟨.or, [0,1]⟩, ⟨.or, [4,5]⟩, ⟨.and, [9,10]⟩, ⟨.and, [2,11]⟩, ⟨.or, [2,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [8,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN24 := word 4276676840 3907551360
theorem basisN24 : Monotone2 circN24 ∧ FanInTwo circN24 := by simp [Monotone2,FanInTwo,circN24]
theorem evalN24 : ∀ x : Fin 6 → Bool, circN24.eval (List.ofFn x) = funcN24 x := by decide +kernel
theorem lowerN24 (s : ℕ) (h : HasCircuitSize 6 funcN24 s) : 11 ≤ s :=
  extension funcN24 3 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (25 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN24 (s : ℕ) : HasCircuitSize 6 funcN24 s ↔ 11 ≤ s :=
  ⟨lowerN24 s, fun h => ⟨circN24,(basisN24).2,h,evalN24⟩⟩
def circN25 : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [4,3]⟩, ⟨.or, [7,5]⟩, ⟨.and, [0,1]⟩, ⟨.and, [4,5]⟩, ⟨.or, [9,10]⟩, ⟨.or, [2,11]⟩, ⟨.and, [2,11]⟩, ⟨.and, [6,12]⟩, ⟨.and, [8,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN25 := word 4278118632 3907577984
theorem basisN25 : Monotone2 circN25 ∧ FanInTwo circN25 := by simp [Monotone2,FanInTwo,circN25]
theorem evalN25 : ∀ x : Fin 6 → Bool, circN25.eval (List.ofFn x) = funcN25 x := by decide +kernel
theorem lowerN25 (s : ℕ) (h : HasCircuitSize 6 funcN25 s) : 11 ≤ s :=
  extension funcN25 3 false (by decide +kernel)
    ⟨(fun j : Fin 6 => (3 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN25 (s : ℕ) : HasCircuitSize 6 funcN25 s ↔ 11 ≤ s :=
  ⟨lowerN25 s, fun h => ⟨circN25,(basisN25).2,h,evalN25⟩⟩
def circN26 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [3,4]⟩, ⟨.and, [7,5]⟩, ⟨.or, [0,1]⟩, ⟨.or, [3,5]⟩, ⟨.and, [9,10]⟩, ⟨.and, [2,11]⟩, ⟨.or, [2,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [8,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN26 := word 4276676840 3900762240
theorem basisN26 : Monotone2 circN26 ∧ FanInTwo circN26 := by simp [Monotone2,FanInTwo,circN26]
theorem evalN26 : ∀ x : Fin 6 → Bool, circN26.eval (List.ofFn x) = funcN26 x := by decide +kernel
theorem lowerN26 (s : ℕ) (h : HasCircuitSize 6 funcN26 s) : 11 ≤ s :=
  extension funcN26 4 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (25 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN26 (s : ℕ) : HasCircuitSize 6 funcN26 s ↔ 11 ≤ s :=
  ⟨lowerN26 s, fun h => ⟨circN26,(basisN26).2,h,evalN26⟩⟩
def circN27 : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [3,4]⟩, ⟨.or, [7,5]⟩, ⟨.and, [0,1]⟩, ⟨.and, [3,5]⟩, ⟨.or, [9,10]⟩, ⟨.or, [2,11]⟩, ⟨.and, [2,11]⟩, ⟨.and, [6,12]⟩, ⟨.and, [8,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN27 := word 4276682472 3907577984
theorem basisN27 : Monotone2 circN27 ∧ FanInTwo circN27 := by simp [Monotone2,FanInTwo,circN27]
theorem evalN27 : ∀ x : Fin 6 → Bool, circN27.eval (List.ofFn x) = funcN27 x := by decide +kernel
theorem lowerN27 (s : ℕ) (h : HasCircuitSize 6 funcN27 s) : 11 ≤ s :=
  extension funcN27 4 false (by decide +kernel)
    ⟨(fun j : Fin 6 => (3 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN27 (s : ℕ) : HasCircuitSize 6 funcN27 s ↔ 11 ≤ s :=
  ⟨lowerN27 s, fun h => ⟨circN27,(basisN27).2,h,evalN27⟩⟩
def circ12294 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [3,5]⟩, ⟨.and, [7,4]⟩, ⟨.or, [0,1]⟩, ⟨.or, [3,4]⟩, ⟨.and, [9,10]⟩, ⟨.and, [2,11]⟩, ⟨.or, [2,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [8,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def func12294 := word 4276676736 3907577984
theorem basis12294 : Monotone2 circ12294 ∧ FanInTwo circ12294 := by simp [Monotone2,FanInTwo,circ12294]
theorem eval12294 : ∀ x : Fin 6 → Bool, circ12294.eval (List.ofFn x) = func12294 x := by decide +kernel
theorem lower12294 (s : ℕ) (h : HasCircuitSize 6 func12294 s) : 11 ≤ s :=
  extension func12294 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (25 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exact12294 (s : ℕ) : HasCircuitSize 6 func12294 s ↔ 11 ≤ s :=
  ⟨lower12294 s, fun h => ⟨circ12294,(basis12294).2,h,eval12294⟩⟩
def circ12314 : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [3,5]⟩, ⟨.or, [7,4]⟩, ⟨.and, [0,1]⟩, ⟨.and, [3,4]⟩, ⟨.or, [9,10]⟩, ⟨.or, [2,11]⟩, ⟨.and, [2,11]⟩, ⟨.and, [6,12]⟩, ⟨.and, [8,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def func12314 := word 4276676840 4276676736
theorem basis12314 : Monotone2 circ12314 ∧ FanInTwo circ12314 := by simp [Monotone2,FanInTwo,circ12314]
theorem eval12314 : ∀ x : Fin 6 → Bool, circ12314.eval (List.ofFn x) = func12314 x := by decide +kernel
theorem lower12314 (s : ℕ) (h : HasCircuitSize 6 func12314 s) : 11 ≤ s :=
  extension func12314 5 false (by decide +kernel)
    ⟨(fun j : Fin 6 => (3 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exact12314 (s : ℕ) : HasCircuitSize 6 func12314 s ↔ 11 ≤ s :=
  ⟨lower12314 s, fun h => ⟨circ12314,(basis12314).2,h,eval12314⟩⟩
def circN30 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [4,5]⟩, ⟨.or, [0,1]⟩, ⟨.and, [4,3]⟩, ⟨.or, [9,5]⟩, ⟨.and, [8,10]⟩, ⟨.and, [2,11]⟩, ⟨.or, [2,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN30 := word 4278118632 3900735616
theorem basisN30 : Monotone2 circN30 ∧ FanInTwo circN30 := by simp [Monotone2,FanInTwo,circN30]
theorem evalN30 : ∀ x : Fin 6 → Bool, circN30.eval (List.ofFn x) = funcN30 x := by decide +kernel
theorem lowerN30 (s : ℕ) (h : HasCircuitSize 6 funcN30 s) : 11 ≤ s :=
  extension funcN30 3 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (19 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN30 (s : ℕ) : HasCircuitSize 6 funcN30 s ↔ 11 ≤ s :=
  ⟨lowerN30 s, fun h => ⟨circN30,(basisN30).2,h,evalN30⟩⟩
def circN31 : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [4,5]⟩, ⟨.and, [0,1]⟩, ⟨.or, [4,3]⟩, ⟨.and, [9,5]⟩, ⟨.or, [8,10]⟩, ⟨.or, [2,11]⟩, ⟨.and, [2,11]⟩, ⟨.and, [6,12]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN31 := word 4278124264 3907551360
theorem basisN31 : Monotone2 circN31 ∧ FanInTwo circN31 := by simp [Monotone2,FanInTwo,circN31]
theorem evalN31 : ∀ x : Fin 6 → Bool, circN31.eval (List.ofFn x) = funcN31 x := by decide +kernel
theorem lowerN31 (s : ℕ) (h : HasCircuitSize 6 funcN31 s) : 11 ≤ s :=
  extension funcN31 3 false (by decide +kernel)
    ⟨(fun j : Fin 6 => (9 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN31 (s : ℕ) : HasCircuitSize 6 funcN31 s ↔ 11 ≤ s :=
  ⟨lowerN31 s, fun h => ⟨circN31,(basisN31).2,h,evalN31⟩⟩
def circN32 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [3,5]⟩, ⟨.or, [0,1]⟩, ⟨.and, [3,4]⟩, ⟨.or, [9,5]⟩, ⟨.and, [8,10]⟩, ⟨.and, [2,11]⟩, ⟨.or, [2,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN32 := word 4276682472 3900735616
theorem basisN32 : Monotone2 circN32 ∧ FanInTwo circN32 := by simp [Monotone2,FanInTwo,circN32]
theorem evalN32 : ∀ x : Fin 6 → Bool, circN32.eval (List.ofFn x) = funcN32 x := by decide +kernel
theorem lowerN32 (s : ℕ) (h : HasCircuitSize 6 funcN32 s) : 11 ≤ s :=
  extension funcN32 4 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (11 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN32 (s : ℕ) : HasCircuitSize 6 funcN32 s ↔ 11 ≤ s :=
  ⟨lowerN32 s, fun h => ⟨circN32,(basisN32).2,h,evalN32⟩⟩
def circN33 : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [3,5]⟩, ⟨.and, [0,1]⟩, ⟨.or, [3,4]⟩, ⟨.and, [9,5]⟩, ⟨.or, [8,10]⟩, ⟨.or, [2,11]⟩, ⟨.and, [2,11]⟩, ⟨.and, [6,12]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN33 := word 4278124264 3900762240
theorem basisN33 : Monotone2 circN33 ∧ FanInTwo circN33 := by simp [Monotone2,FanInTwo,circN33]
theorem evalN33 : ∀ x : Fin 6 → Bool, circN33.eval (List.ofFn x) = funcN33 x := by decide +kernel
theorem lowerN33 (s : ℕ) (h : HasCircuitSize 6 funcN33 s) : 11 ≤ s :=
  extension funcN33 4 false (by decide +kernel)
    ⟨(fun j : Fin 6 => (17 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN33 (s : ℕ) : HasCircuitSize 6 funcN33 s ↔ 11 ≤ s :=
  ⟨lowerN33 s, fun h => ⟨circN33,(basisN33).2,h,evalN33⟩⟩
def circN34 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [3,4]⟩, ⟨.or, [0,1]⟩, ⟨.and, [3,5]⟩, ⟨.or, [9,4]⟩, ⟨.and, [8,10]⟩, ⟨.and, [2,11]⟩, ⟨.or, [2,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN34 := word 4276676736 4276650112
theorem basisN34 : Monotone2 circN34 ∧ FanInTwo circN34 := by simp [Monotone2,FanInTwo,circN34]
theorem evalN34 : ∀ x : Fin 6 → Bool, circN34.eval (List.ofFn x) = funcN34 x := by decide +kernel
theorem lowerN34 (s : ℕ) (h : HasCircuitSize 6 funcN34 s) : 11 ≤ s :=
  extension funcN34 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (11 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN34 (s : ℕ) : HasCircuitSize 6 funcN34 s ↔ 11 ≤ s :=
  ⟨lowerN34 s, fun h => ⟨circN34,(basisN34).2,h,evalN34⟩⟩
def circN35 : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [3,4]⟩, ⟨.and, [0,1]⟩, ⟨.or, [3,5]⟩, ⟨.and, [9,4]⟩, ⟨.or, [8,10]⟩, ⟨.or, [2,11]⟩, ⟨.and, [2,11]⟩, ⟨.and, [6,12]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN35 := word 4278118528 4276676736
theorem basisN35 : Monotone2 circN35 ∧ FanInTwo circN35 := by simp [Monotone2,FanInTwo,circN35]
theorem evalN35 : ∀ x : Fin 6 → Bool, circN35.eval (List.ofFn x) = funcN35 x := by decide +kernel
theorem lowerN35 (s : ℕ) (h : HasCircuitSize 6 funcN35 s) : 11 ≤ s :=
  extension funcN35 5 false (by decide +kernel)
    ⟨(fun j : Fin 6 => (17 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN35 (s : ℕ) : HasCircuitSize 6 funcN35 s ↔ 11 ≤ s :=
  ⟨lowerN35 s, fun h => ⟨circN35,(basisN35).2,h,evalN35⟩⟩
def circN36 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [4,5]⟩, ⟨.or, [0,1]⟩, ⟨.and, [5,3]⟩, ⟨.or, [4,9]⟩, ⟨.and, [8,10]⟩, ⟨.and, [2,11]⟩, ⟨.or, [2,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN36 := word 4278118528 3907551360
theorem basisN36 : Monotone2 circN36 ∧ FanInTwo circN36 := by simp [Monotone2,FanInTwo,circN36]
theorem evalN36 : ∀ x : Fin 6 → Bool, circN36.eval (List.ofFn x) = funcN36 x := by decide +kernel
theorem lowerN36 (s : ℕ) (h : HasCircuitSize 6 funcN36 s) : 11 ≤ s :=
  extension funcN36 3 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (11 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN36 (s : ℕ) : HasCircuitSize 6 funcN36 s ↔ 11 ≤ s :=
  ⟨lowerN36 s, fun h => ⟨circN36,(basisN36).2,h,evalN36⟩⟩
def circN37 : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [4,5]⟩, ⟨.and, [0,1]⟩, ⟨.or, [5,3]⟩, ⟨.and, [4,9]⟩, ⟨.or, [8,10]⟩, ⟨.or, [2,11]⟩, ⟨.and, [2,11]⟩, ⟨.and, [6,12]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN37 := word 4278118632 4276650112
theorem basisN37 : Monotone2 circN37 ∧ FanInTwo circN37 := by simp [Monotone2,FanInTwo,circN37]
theorem evalN37 : ∀ x : Fin 6 → Bool, circN37.eval (List.ofFn x) = funcN37 x := by decide +kernel
theorem lowerN37 (s : ℕ) (h : HasCircuitSize 6 funcN37 s) : 11 ≤ s :=
  extension funcN37 3 false (by decide +kernel)
    ⟨(fun j : Fin 6 => (17 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN37 (s : ℕ) : HasCircuitSize 6 funcN37 s ↔ 11 ≤ s :=
  ⟨lowerN37 s, fun h => ⟨circN37,(basisN37).2,h,evalN37⟩⟩
def circN38 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [3,5]⟩, ⟨.or, [0,1]⟩, ⟨.and, [5,4]⟩, ⟨.or, [3,9]⟩, ⟨.and, [8,10]⟩, ⟨.and, [2,11]⟩, ⟨.or, [2,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN38 := word 4276682368 3900762240
theorem basisN38 : Monotone2 circN38 ∧ FanInTwo circN38 := by simp [Monotone2,FanInTwo,circN38]
theorem evalN38 : ∀ x : Fin 6 → Bool, circN38.eval (List.ofFn x) = funcN38 x := by decide +kernel
theorem lowerN38 (s : ℕ) (h : HasCircuitSize 6 funcN38 s) : 11 ≤ s :=
  extension funcN38 4 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (19 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN38 (s : ℕ) : HasCircuitSize 6 funcN38 s ↔ 11 ≤ s :=
  ⟨lowerN38 s, fun h => ⟨circN38,(basisN38).2,h,evalN38⟩⟩
def circN39 : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [3,5]⟩, ⟨.and, [0,1]⟩, ⟨.or, [5,4]⟩, ⟨.and, [3,9]⟩, ⟨.or, [8,10]⟩, ⟨.or, [2,11]⟩, ⟨.and, [2,11]⟩, ⟨.and, [6,12]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN39 := word 4276682472 4269860992
theorem basisN39 : Monotone2 circN39 ∧ FanInTwo circN39 := by simp [Monotone2,FanInTwo,circN39]
theorem evalN39 : ∀ x : Fin 6 → Bool, circN39.eval (List.ofFn x) = funcN39 x := by decide +kernel
theorem lowerN39 (s : ℕ) (h : HasCircuitSize 6 funcN39 s) : 11 ≤ s :=
  extension funcN39 4 false (by decide +kernel)
    ⟨(fun j : Fin 6 => (9 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN39 (s : ℕ) : HasCircuitSize 6 funcN39 s ↔ 11 ≤ s :=
  ⟨lowerN39 s, fun h => ⟨circN39,(basisN39).2,h,evalN39⟩⟩
def circ12298 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [3,4]⟩, ⟨.or, [0,1]⟩, ⟨.and, [4,5]⟩, ⟨.or, [3,9]⟩, ⟨.and, [8,10]⟩, ⟨.and, [2,11]⟩, ⟨.or, [2,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def func12298 := word 4276676736 4269860992
theorem basis12298 : Monotone2 circ12298 ∧ FanInTwo circ12298 := by simp [Monotone2,FanInTwo,circ12298]
theorem eval12298 : ∀ x : Fin 6 → Bool, circ12298.eval (List.ofFn x) = func12298 x := by decide +kernel
theorem lower12298 (s : ℕ) (h : HasCircuitSize 6 func12298 s) : 11 ≤ s :=
  extension func12298 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (19 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exact12298 (s : ℕ) : HasCircuitSize 6 func12298 s ↔ 11 ≤ s :=
  ⟨lower12298 s, fun h => ⟨circ12298,(basis12298).2,h,eval12298⟩⟩
def circ12335 : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [3,4]⟩, ⟨.and, [0,1]⟩, ⟨.or, [4,5]⟩, ⟨.and, [3,9]⟩, ⟨.or, [8,10]⟩, ⟨.or, [2,11]⟩, ⟨.and, [2,11]⟩, ⟨.and, [6,12]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def func12335 := word 4276682368 4276676736
theorem basis12335 : Monotone2 circ12335 ∧ FanInTwo circ12335 := by simp [Monotone2,FanInTwo,circ12335]
theorem eval12335 : ∀ x : Fin 6 → Bool, circ12335.eval (List.ofFn x) = func12335 x := by decide +kernel
theorem lower12335 (s : ℕ) (h : HasCircuitSize 6 func12335 s) : 11 ≤ s :=
  extension func12335 5 false (by decide +kernel)
    ⟨(fun j : Fin 6 => (9 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exact12335 (s : ℕ) : HasCircuitSize 6 func12335 s ↔ 11 ≤ s :=
  ⟨lower12335 s, fun h => ⟨circ12335,(basis12335).2,h,eval12335⟩⟩
def circN42 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [4,5]⟩, ⟨.or, [0,1]⟩, ⟨.or, [4,5]⟩, ⟨.and, [8,9]⟩, ⟨.and, [2,10]⟩, ⟨.or, [2,10]⟩, ⟨.or, [6,11]⟩, ⟨.and, [13,3]⟩, ⟨.or, [7,14]⟩, ⟨.and, [12,15]⟩], 16⟩
def funcN42 := word 4278118400 3892346880
theorem basisN42 : Monotone2 circN42 ∧ FanInTwo circN42 := by simp [Monotone2,FanInTwo,circN42]
theorem evalN42 : ∀ x : Fin 6 → Bool, circN42.eval (List.ofFn x) = funcN42 x := by decide +kernel
theorem lowerN42 (s : ℕ) (h : HasCircuitSize 6 funcN42 s) : 11 ≤ s :=
  extension funcN42 3 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN42 (s : ℕ) : HasCircuitSize 6 funcN42 s ↔ 11 ≤ s :=
  ⟨lowerN42 s, fun h => ⟨circN42,(basisN42).2,h,evalN42⟩⟩
def circN43 : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [4,5]⟩, ⟨.and, [0,1]⟩, ⟨.and, [4,5]⟩, ⟨.or, [8,9]⟩, ⟨.or, [2,10]⟩, ⟨.and, [2,10]⟩, ⟨.and, [6,11]⟩, ⟨.or, [13,3]⟩, ⟨.and, [7,14]⟩, ⟨.or, [12,15]⟩], 16⟩
def funcN43 := word 4294901736 4293427328
theorem basisN43 : Monotone2 circN43 ∧ FanInTwo circN43 := by simp [Monotone2,FanInTwo,circN43]
theorem evalN43 : ∀ x : Fin 6 → Bool, circN43.eval (List.ofFn x) = funcN43 x := by decide +kernel
theorem lowerN43 (s : ℕ) (h : HasCircuitSize 6 funcN43 s) : 11 ≤ s :=
  extension funcN43 3 false (by decide +kernel)
    ⟨(fun j : Fin 6 => (8 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN43 (s : ℕ) : HasCircuitSize 6 funcN43 s ↔ 11 ≤ s :=
  ⟨lowerN43 s, fun h => ⟨circN43,(basisN43).2,h,evalN43⟩⟩
def circN44 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [3,5]⟩, ⟨.or, [0,1]⟩, ⟨.or, [3,5]⟩, ⟨.and, [8,9]⟩, ⟨.and, [2,10]⟩, ⟨.or, [2,10]⟩, ⟨.or, [6,11]⟩, ⟨.and, [13,4]⟩, ⟨.or, [7,14]⟩, ⟨.and, [12,15]⟩], 16⟩
def funcN44 := word 4276682240 3900702720
theorem basisN44 : Monotone2 circN44 ∧ FanInTwo circN44 := by simp [Monotone2,FanInTwo,circN44]
theorem evalN44 : ∀ x : Fin 6 → Bool, circN44.eval (List.ofFn x) = funcN44 x := by decide +kernel
theorem lowerN44 (s : ℕ) (h : HasCircuitSize 6 funcN44 s) : 11 ≤ s :=
  extension funcN44 4 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN44 (s : ℕ) : HasCircuitSize 6 funcN44 s ↔ 11 ≤ s :=
  ⟨lowerN44 s, fun h => ⟨circN44,(basisN44).2,h,evalN44⟩⟩
def circN45 : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [3,5]⟩, ⟨.and, [0,1]⟩, ⟨.and, [3,5]⟩, ⟨.or, [8,9]⟩, ⟨.or, [2,10]⟩, ⟨.and, [2,10]⟩, ⟨.and, [6,11]⟩, ⟨.or, [13,4]⟩, ⟨.and, [7,14]⟩, ⟨.or, [12,15]⟩], 16⟩
def funcN45 := word 4294967016 4286638208
theorem basisN45 : Monotone2 circN45 ∧ FanInTwo circN45 := by simp [Monotone2,FanInTwo,circN45]
theorem evalN45 : ∀ x : Fin 6 → Bool, circN45.eval (List.ofFn x) = funcN45 x := by decide +kernel
theorem lowerN45 (s : ℕ) (h : HasCircuitSize 6 funcN45 s) : 11 ≤ s :=
  extension funcN45 4 false (by decide +kernel)
    ⟨(fun j : Fin 6 => (8 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN45 (s : ℕ) : HasCircuitSize 6 funcN45 s ↔ 11 ≤ s :=
  ⟨lowerN45 s, fun h => ⟨circN45,(basisN45).2,h,evalN45⟩⟩
def circ12120 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [3,4]⟩, ⟨.or, [0,1]⟩, ⟨.or, [3,4]⟩, ⟨.and, [8,9]⟩, ⟨.and, [2,10]⟩, ⟨.or, [2,10]⟩, ⟨.or, [6,11]⟩, ⟨.and, [13,5]⟩, ⟨.or, [7,14]⟩, ⟨.and, [12,15]⟩], 16⟩
def func12120 := word 4276676736 4261412864
theorem basis12120 : Monotone2 circ12120 ∧ FanInTwo circ12120 := by simp [Monotone2,FanInTwo,circ12120]
theorem eval12120 : ∀ x : Fin 6 → Bool, circ12120.eval (List.ofFn x) = func12120 x := by decide +kernel
theorem lower12120 (s : ℕ) (h : HasCircuitSize 6 func12120 s) : 11 ≤ s :=
  extension func12120 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exact12120 (s : ℕ) : HasCircuitSize 6 func12120 s ↔ 11 ≤ s :=
  ⟨lower12120 s, fun h => ⟨circ12120,(basis12120).2,h,eval12120⟩⟩
def circN47 : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [3,4]⟩, ⟨.and, [0,1]⟩, ⟨.and, [3,4]⟩, ⟨.or, [8,9]⟩, ⟨.or, [2,10]⟩, ⟨.and, [2,10]⟩, ⟨.and, [6,11]⟩, ⟨.or, [13,5]⟩, ⟨.and, [7,14]⟩, ⟨.or, [12,15]⟩], 16⟩
def funcN47 := word 4294967168 4276676736
theorem basisN47 : Monotone2 circN47 ∧ FanInTwo circN47 := by simp [Monotone2,FanInTwo,circN47]
theorem evalN47 : ∀ x : Fin 6 → Bool, circN47.eval (List.ofFn x) = funcN47 x := by decide +kernel
theorem lowerN47 (s : ℕ) (h : HasCircuitSize 6 funcN47 s) : 11 ≤ s :=
  extension funcN47 5 false (by decide +kernel)
    ⟨(fun j : Fin 6 => (8 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN47 (s : ℕ) : HasCircuitSize 6 funcN47 s ↔ 11 ≤ s :=
  ⟨lowerN47 s, fun h => ⟨circN47,(basisN47).2,h,evalN47⟩⟩
def circN48 : Circuit := ⟨[⟨.and, [0,5]⟩, ⟨.and, [6,1]⟩, ⟨.and, [2,3]⟩, ⟨.or, [0,1]⟩, ⟨.or, [2,3]⟩, ⟨.and, [9,10]⟩, ⟨.and, [4,11]⟩, ⟨.or, [4,11]⟩, ⟨.or, [7,12]⟩, ⟨.or, [8,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN48 := word 4276676736 4276150272
theorem basisN48 : Monotone2 circN48 ∧ FanInTwo circN48 := by simp [Monotone2,FanInTwo,circN48]
theorem evalN48 : ∀ x : Fin 6 → Bool, circN48.eval (List.ofFn x) = funcN48 x := by decide +kernel
theorem lowerN48 (s : ℕ) (h : HasCircuitSize 6 funcN48 s) : 11 ≤ s :=
  extension funcN48 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN48 (s : ℕ) : HasCircuitSize 6 funcN48 s ↔ 11 ≤ s :=
  ⟨lowerN48 s, fun h => ⟨circN48,(basisN48).2,h,evalN48⟩⟩
def circN49 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [2,3]⟩, ⟨.and, [0,5]⟩, ⟨.or, [8,1]⟩, ⟨.or, [2,3]⟩, ⟨.and, [9,10]⟩, ⟨.and, [4,11]⟩, ⟨.or, [4,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN49 := word 4276676736 4241016960
theorem basisN49 : Monotone2 circN49 ∧ FanInTwo circN49 := by simp [Monotone2,FanInTwo,circN49]
theorem evalN49 : ∀ x : Fin 6 → Bool, circN49.eval (List.ofFn x) = funcN49 x := by decide +kernel
theorem lowerN49 (s : ℕ) (h : HasCircuitSize 6 funcN49 s) : 11 ≤ s :=
  extension funcN49 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (13 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN49 (s : ℕ) : HasCircuitSize 6 funcN49 s ↔ 11 ≤ s :=
  ⟨lowerN49 s, fun h => ⟨circN49,(basisN49).2,h,evalN49⟩⟩
def circN50 : Circuit := ⟨[⟨.and, [0,5]⟩, ⟨.and, [6,1]⟩, ⟨.and, [2,3]⟩, ⟨.or, [6,1]⟩, ⟨.or, [2,3]⟩, ⟨.and, [9,10]⟩, ⟨.and, [4,11]⟩, ⟨.or, [4,11]⟩, ⟨.or, [7,12]⟩, ⟨.or, [8,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN50 := word 4276676736 4240490496
theorem basisN50 : Monotone2 circN50 ∧ FanInTwo circN50 := by simp [Monotone2,FanInTwo,circN50]
theorem evalN50 : ∀ x : Fin 6 → Bool, circN50.eval (List.ofFn x) = funcN50 x := by decide +kernel
theorem lowerN50 (s : ℕ) (h : HasCircuitSize 6 funcN50 s) : 11 ≤ s :=
  extension funcN50 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN50 (s : ℕ) : HasCircuitSize 6 funcN50 s ↔ 11 ≤ s :=
  ⟨lowerN50 s, fun h => ⟨circN50,(basisN50).2,h,evalN50⟩⟩
def circN51 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [2,3]⟩, ⟨.and, [1,5]⟩, ⟨.or, [0,8]⟩, ⟨.or, [2,3]⟩, ⟨.and, [9,10]⟩, ⟨.and, [4,11]⟩, ⟨.or, [4,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN51 := word 4276676736 4205357184
theorem basisN51 : Monotone2 circN51 ∧ FanInTwo circN51 := by simp [Monotone2,FanInTwo,circN51]
theorem evalN51 : ∀ x : Fin 6 → Bool, circN51.eval (List.ofFn x) = funcN51 x := by decide +kernel
theorem lowerN51 (s : ℕ) (h : HasCircuitSize 6 funcN51 s) : 11 ≤ s :=
  extension funcN51 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (14 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN51 (s : ℕ) : HasCircuitSize 6 funcN51 s ↔ 11 ≤ s :=
  ⟨lowerN51 s, fun h => ⟨circN51,(basisN51).2,h,evalN51⟩⟩
def circN52 : Circuit := ⟨[⟨.and, [1,5]⟩, ⟨.and, [0,6]⟩, ⟨.and, [2,3]⟩, ⟨.or, [0,6]⟩, ⟨.or, [2,3]⟩, ⟨.and, [9,10]⟩, ⟨.and, [4,11]⟩, ⟨.or, [4,11]⟩, ⟨.or, [7,12]⟩, ⟨.or, [8,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN52 := word 4276676736 4204830720
theorem basisN52 : Monotone2 circN52 ∧ FanInTwo circN52 := by simp [Monotone2,FanInTwo,circN52]
theorem evalN52 : ∀ x : Fin 6 → Bool, circN52.eval (List.ofFn x) = funcN52 x := by decide +kernel
theorem lowerN52 (s : ℕ) (h : HasCircuitSize 6 funcN52 s) : 11 ≤ s :=
  extension funcN52 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN52 (s : ℕ) : HasCircuitSize 6 funcN52 s ↔ 11 ≤ s :=
  ⟨lowerN52 s, fun h => ⟨circN52,(basisN52).2,h,evalN52⟩⟩
def circN53 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [2,5]⟩, ⟨.and, [7,3]⟩, ⟨.or, [0,1]⟩, ⟨.or, [2,3]⟩, ⟨.and, [9,10]⟩, ⟨.and, [4,11]⟩, ⟨.or, [4,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [8,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN53 := word 4276676736 4008216704
theorem basisN53 : Monotone2 circN53 ∧ FanInTwo circN53 := by simp [Monotone2,FanInTwo,circN53]
theorem evalN53 : ∀ x : Fin 6 → Bool, circN53.eval (List.ofFn x) = funcN53 x := by decide +kernel
theorem lowerN53 (s : ℕ) (h : HasCircuitSize 6 funcN53 s) : 11 ≤ s :=
  extension funcN53 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (13 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN53 (s : ℕ) : HasCircuitSize 6 funcN53 s ↔ 11 ≤ s :=
  ⟨lowerN53 s, fun h => ⟨circN53,(basisN53).2,h,evalN53⟩⟩
def circN54 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [2,3]⟩, ⟨.or, [0,1]⟩, ⟨.and, [2,5]⟩, ⟨.or, [9,3]⟩, ⟨.and, [8,10]⟩, ⟨.and, [4,11]⟩, ⟨.or, [4,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN54 := word 4276676736 4270385152
theorem basisN54 : Monotone2 circN54 ∧ FanInTwo circN54 := by simp [Monotone2,FanInTwo,circN54]
theorem evalN54 : ∀ x : Fin 6 → Bool, circN54.eval (List.ofFn x) = funcN54 x := by decide +kernel
theorem lowerN54 (s : ℕ) (h : HasCircuitSize 6 funcN54 s) : 11 ≤ s :=
  extension funcN54 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN54 (s : ℕ) : HasCircuitSize 6 funcN54 s ↔ 11 ≤ s :=
  ⟨lowerN54 s, fun h => ⟨circN54,(basisN54).2,h,evalN54⟩⟩
def circN55 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [2,5]⟩, ⟨.and, [7,3]⟩, ⟨.or, [0,1]⟩, ⟨.or, [7,3]⟩, ⟨.and, [9,10]⟩, ⟨.and, [4,11]⟩, ⟨.or, [4,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [8,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN55 := word 4276676736 4001925120
theorem basisN55 : Monotone2 circN55 ∧ FanInTwo circN55 := by simp [Monotone2,FanInTwo,circN55]
theorem evalN55 : ∀ x : Fin 6 → Bool, circN55.eval (List.ofFn x) = funcN55 x := by decide +kernel
theorem lowerN55 (s : ℕ) (h : HasCircuitSize 6 funcN55 s) : 11 ≤ s :=
  extension funcN55 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN55 (s : ℕ) : HasCircuitSize 6 funcN55 s ↔ 11 ≤ s :=
  ⟨lowerN55 s, fun h => ⟨circN55,(basisN55).2,h,evalN55⟩⟩
def circN56 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [2,3]⟩, ⟨.or, [0,1]⟩, ⟨.and, [3,5]⟩, ⟨.or, [2,9]⟩, ⟨.and, [8,10]⟩, ⟨.and, [4,11]⟩, ⟨.or, [4,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN56 := word 4276676736 4176011392
theorem basisN56 : Monotone2 circN56 ∧ FanInTwo circN56 := by simp [Monotone2,FanInTwo,circN56]
theorem evalN56 : ∀ x : Fin 6 → Bool, circN56.eval (List.ofFn x) = funcN56 x := by decide +kernel
theorem lowerN56 (s : ℕ) (h : HasCircuitSize 6 funcN56 s) : 11 ≤ s :=
  extension funcN56 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (11 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN56 (s : ℕ) : HasCircuitSize 6 funcN56 s ↔ 11 ≤ s :=
  ⟨lowerN56 s, fun h => ⟨circN56,(basisN56).2,h,evalN56⟩⟩
def circN57 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [2,3]⟩, ⟨.or, [0,1]⟩, ⟨.or, [2,3]⟩, ⟨.and, [8,9]⟩, ⟨.and, [4,5]⟩, ⟨.and, [11,10]⟩, ⟨.or, [4,10]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN57 := word 4276676736 4169721984
theorem basisN57 : Monotone2 circN57 ∧ FanInTwo circN57 := by simp [Monotone2,FanInTwo,circN57]
theorem evalN57 : ∀ x : Fin 6 → Bool, circN57.eval (List.ofFn x) = funcN57 x := by decide +kernel
theorem lowerN57 (s : ℕ) (h : HasCircuitSize 6 funcN57 s) : 11 ≤ s :=
  extension funcN57 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (21 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN57 (s : ℕ) : HasCircuitSize 6 funcN57 s ↔ 11 ≤ s :=
  ⟨lowerN57 s, fun h => ⟨circN57,(basisN57).2,h,evalN57⟩⟩
def circN58 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [2,3]⟩, ⟨.or, [0,1]⟩, ⟨.or, [2,3]⟩, ⟨.and, [8,9]⟩, ⟨.and, [4,10]⟩, ⟨.and, [4,5]⟩, ⟨.or, [12,10]⟩, ⟨.or, [6,11]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN58 := word 4276676736 4007716992
theorem basisN58 : Monotone2 circN58 ∧ FanInTwo circN58 := by simp [Monotone2,FanInTwo,circN58]
theorem evalN58 : ∀ x : Fin 6 → Bool, circN58.eval (List.ofFn x) = funcN58 x := by decide +kernel
theorem lowerN58 (s : ℕ) (h : HasCircuitSize 6 funcN58 s) : 11 ≤ s :=
  extension funcN58 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (19 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN58 (s : ℕ) : HasCircuitSize 6 funcN58 s ↔ 11 ≤ s :=
  ⟨lowerN58 s, fun h => ⟨circN58,(basisN58).2,h,evalN58⟩⟩
def circN59 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [2,3]⟩, ⟨.or, [0,1]⟩, ⟨.or, [2,3]⟩, ⟨.and, [8,5]⟩, ⟨.and, [10,9]⟩, ⟨.and, [4,11]⟩, ⟨.or, [4,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN59 := word 4276676736 4169662464
theorem basisN59 : Monotone2 circN59 ∧ FanInTwo circN59 := by simp [Monotone2,FanInTwo,circN59]
theorem evalN59 : ∀ x : Fin 6 → Bool, circN59.eval (List.ofFn x) = funcN59 x := by decide +kernel
theorem lowerN59 (s : ℕ) (h : HasCircuitSize 6 funcN59 s) : 11 ≤ s :=
  extension funcN59 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN59 (s : ℕ) : HasCircuitSize 6 funcN59 s ↔ 11 ≤ s :=
  ⟨lowerN59 s, fun h => ⟨circN59,(basisN59).2,h,evalN59⟩⟩
def circN60 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [2,3]⟩, ⟨.or, [0,1]⟩, ⟨.or, [2,3]⟩, ⟨.and, [8,9]⟩, ⟨.and, [4,10]⟩, ⟨.or, [4,10]⟩, ⟨.or, [6,11]⟩, ⟨.and, [13,5]⟩, ⟨.or, [7,14]⟩, ⟨.and, [12,15]⟩], 16⟩
def funcN60 := word 4276676736 4026589184
theorem basisN60 : Monotone2 circN60 ∧ FanInTwo circN60 := by simp [Monotone2,FanInTwo,circN60]
theorem evalN60 : ∀ x : Fin 6 → Bool, circN60.eval (List.ofFn x) = funcN60 x := by decide +kernel
theorem lowerN60 (s : ℕ) (h : HasCircuitSize 6 funcN60 s) : 11 ≤ s :=
  extension funcN60 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN60 (s : ℕ) : HasCircuitSize 6 funcN60 s ↔ 11 ≤ s :=
  ⟨lowerN60 s, fun h => ⟨circN60,(basisN60).2,h,evalN60⟩⟩
def circN61 : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [2,3]⟩, ⟨.and, [0,1]⟩, ⟨.and, [2,3]⟩, ⟨.or, [8,9]⟩, ⟨.and, [10,5]⟩, ⟨.or, [4,11]⟩, ⟨.and, [4,11]⟩, ⟨.and, [6,12]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN61 := word 4276676736 4007657472
theorem basisN61 : Monotone2 circN61 ∧ FanInTwo circN61 := by simp [Monotone2,FanInTwo,circN61]
theorem evalN61 : ∀ x : Fin 6 → Bool, circN61.eval (List.ofFn x) = funcN61 x := by decide +kernel
theorem lowerN61 (s : ℕ) (h : HasCircuitSize 6 funcN61 s) : 11 ≤ s :=
  extension funcN61 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN61 (s : ℕ) : HasCircuitSize 6 funcN61 s ↔ 11 ≤ s :=
  ⟨lowerN61 s, fun h => ⟨circN61,(basisN61).2,h,evalN61⟩⟩
def circN62 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [2,5]⟩, ⟨.and, [7,4]⟩, ⟨.or, [0,1]⟩, ⟨.or, [2,4]⟩, ⟨.and, [9,10]⟩, ⟨.and, [3,11]⟩, ⟨.or, [3,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [8,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN62 := word 4276676736 4001949824
theorem basisN62 : Monotone2 circN62 ∧ FanInTwo circN62 := by simp [Monotone2,FanInTwo,circN62]
theorem evalN62 : ∀ x : Fin 6 → Bool, circN62.eval (List.ofFn x) = funcN62 x := by decide +kernel
theorem lowerN62 (s : ℕ) (h : HasCircuitSize 6 funcN62 s) : 11 ≤ s :=
  extension funcN62 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (21 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN62 (s : ℕ) : HasCircuitSize 6 funcN62 s ↔ 11 ≤ s :=
  ⟨lowerN62 s, fun h => ⟨circN62,(basisN62).2,h,evalN62⟩⟩
def circN63 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [2,4]⟩, ⟨.or, [0,1]⟩, ⟨.and, [2,5]⟩, ⟨.or, [9,4]⟩, ⟨.and, [8,10]⟩, ⟨.and, [3,11]⟩, ⟨.or, [3,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN63 := word 4276676736 4276652032
theorem basisN63 : Monotone2 circN63 ∧ FanInTwo circN63 := by simp [Monotone2,FanInTwo,circN63]
theorem evalN63 : ∀ x : Fin 6 → Bool, circN63.eval (List.ofFn x) = funcN63 x := by decide +kernel
theorem lowerN63 (s : ℕ) (h : HasCircuitSize 6 funcN63 s) : 11 ≤ s :=
  extension funcN63 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN63 (s : ℕ) : HasCircuitSize 6 funcN63 s ↔ 11 ≤ s :=
  ⟨lowerN63 s, fun h => ⟨circN63,(basisN63).2,h,evalN63⟩⟩
def circN64 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [2,4]⟩, ⟨.or, [0,1]⟩, ⟨.and, [4,5]⟩, ⟨.or, [2,9]⟩, ⟨.and, [8,10]⟩, ⟨.and, [3,11]⟩, ⟨.or, [3,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN64 := word 4276676736 4175489152
theorem basisN64 : Monotone2 circN64 ∧ FanInTwo circN64 := by simp [Monotone2,FanInTwo,circN64]
theorem evalN64 : ∀ x : Fin 6 → Bool, circN64.eval (List.ofFn x) = funcN64 x := by decide +kernel
theorem lowerN64 (s : ℕ) (h : HasCircuitSize 6 funcN64 s) : 11 ≤ s :=
  extension funcN64 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (19 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN64 (s : ℕ) : HasCircuitSize 6 funcN64 s ↔ 11 ≤ s :=
  ⟨lowerN64 s, fun h => ⟨circN64,(basisN64).2,h,evalN64⟩⟩
def circN65 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [2,4]⟩, ⟨.or, [0,1]⟩, ⟨.or, [2,4]⟩, ⟨.and, [8,9]⟩, ⟨.and, [3,5]⟩, ⟨.and, [11,10]⟩, ⟨.or, [3,10]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN65 := word 4276676736 4175988864
theorem basisN65 : Monotone2 circN65 ∧ FanInTwo circN65 := by simp [Monotone2,FanInTwo,circN65]
theorem evalN65 : ∀ x : Fin 6 → Bool, circN65.eval (List.ofFn x) = funcN65 x := by decide +kernel
theorem lowerN65 (s : ℕ) (h : HasCircuitSize 6 funcN65 s) : 11 ≤ s :=
  extension funcN65 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (13 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN65 (s : ℕ) : HasCircuitSize 6 funcN65 s ↔ 11 ≤ s :=
  ⟨lowerN65 s, fun h => ⟨circN65,(basisN65).2,h,evalN65⟩⟩
def circN66 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [2,4]⟩, ⟨.or, [0,1]⟩, ⟨.or, [2,4]⟩, ⟨.and, [8,9]⟩, ⟨.and, [3,10]⟩, ⟨.and, [3,5]⟩, ⟨.or, [12,10]⟩, ⟨.or, [6,11]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN66 := word 4276676736 4008239232
theorem basisN66 : Monotone2 circN66 ∧ FanInTwo circN66 := by simp [Monotone2,FanInTwo,circN66]
theorem evalN66 : ∀ x : Fin 6 → Bool, circN66.eval (List.ofFn x) = funcN66 x := by decide +kernel
theorem lowerN66 (s : ℕ) (h : HasCircuitSize 6 funcN66 s) : 11 ≤ s :=
  extension funcN66 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (11 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN66 (s : ℕ) : HasCircuitSize 6 funcN66 s ↔ 11 ≤ s :=
  ⟨lowerN66 s, fun h => ⟨circN66,(basisN66).2,h,evalN66⟩⟩
def circN67 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [2,4]⟩, ⟨.or, [0,1]⟩, ⟨.or, [2,4]⟩, ⟨.and, [8,5]⟩, ⟨.and, [10,9]⟩, ⟨.and, [3,11]⟩, ⟨.or, [3,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN67 := word 4276676736 4160784384
theorem basisN67 : Monotone2 circN67 ∧ FanInTwo circN67 := by simp [Monotone2,FanInTwo,circN67]
theorem evalN67 : ∀ x : Fin 6 → Bool, circN67.eval (List.ofFn x) = funcN67 x := by decide +kernel
theorem lowerN67 (s : ℕ) (h : HasCircuitSize 6 funcN67 s) : 11 ≤ s :=
  extension funcN67 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN67 (s : ℕ) : HasCircuitSize 6 funcN67 s ↔ 11 ≤ s :=
  ⟨lowerN67 s, fun h => ⟨circN67,(basisN67).2,h,evalN67⟩⟩
def circN68 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [2,4]⟩, ⟨.or, [0,1]⟩, ⟨.or, [2,4]⟩, ⟨.and, [8,9]⟩, ⟨.and, [3,10]⟩, ⟨.or, [3,10]⟩, ⟨.or, [6,11]⟩, ⟨.and, [13,5]⟩, ⟨.or, [7,14]⟩, ⟨.and, [12,15]⟩], 16⟩
def funcN68 := word 4276676736 4041211904
theorem basisN68 : Monotone2 circN68 ∧ FanInTwo circN68 := by simp [Monotone2,FanInTwo,circN68]
theorem evalN68 : ∀ x : Fin 6 → Bool, circN68.eval (List.ofFn x) = funcN68 x := by decide +kernel
theorem lowerN68 (s : ℕ) (h : HasCircuitSize 6 funcN68 s) : 11 ≤ s :=
  extension funcN68 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN68 (s : ℕ) : HasCircuitSize 6 funcN68 s ↔ 11 ≤ s :=
  ⟨lowerN68 s, fun h => ⟨circN68,(basisN68).2,h,evalN68⟩⟩
def circN69 : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [2,4]⟩, ⟨.and, [0,1]⟩, ⟨.and, [2,4]⟩, ⟨.or, [8,9]⟩, ⟨.and, [10,5]⟩, ⟨.or, [3,11]⟩, ⟨.and, [3,11]⟩, ⟨.and, [6,12]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN69 := word 4276676736 3993034752
theorem basisN69 : Monotone2 circN69 ∧ FanInTwo circN69 := by simp [Monotone2,FanInTwo,circN69]
theorem evalN69 : ∀ x : Fin 6 → Bool, circN69.eval (List.ofFn x) = funcN69 x := by decide +kernel
theorem lowerN69 (s : ℕ) (h : HasCircuitSize 6 funcN69 s) : 11 ≤ s :=
  extension funcN69 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN69 (s : ℕ) : HasCircuitSize 6 funcN69 s ↔ 11 ≤ s :=
  ⟨lowerN69 s, fun h => ⟨circN69,(basisN69).2,h,evalN69⟩⟩
def circN70 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [3,4]⟩, ⟨.or, [0,1]⟩, ⟨.or, [3,4]⟩, ⟨.and, [8,9]⟩, ⟨.and, [2,5]⟩, ⟨.and, [11,10]⟩, ⟨.or, [2,10]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN70 := word 4276676736 4270360704
theorem basisN70 : Monotone2 circN70 ∧ FanInTwo circN70 := by simp [Monotone2,FanInTwo,circN70]
theorem evalN70 : ∀ x : Fin 6 → Bool, circN70.eval (List.ofFn x) = funcN70 x := by decide +kernel
theorem lowerN70 (s : ℕ) (h : HasCircuitSize 6 funcN70 s) : 11 ≤ s :=
  extension funcN70 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (13 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN70 (s : ℕ) : HasCircuitSize 6 funcN70 s ↔ 11 ≤ s :=
  ⟨lowerN70 s, fun h => ⟨circN70,(basisN70).2,h,evalN70⟩⟩
def circN71 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [3,4]⟩, ⟨.or, [0,1]⟩, ⟨.or, [3,4]⟩, ⟨.and, [8,9]⟩, ⟨.and, [2,10]⟩, ⟨.and, [2,5]⟩, ⟨.or, [12,10]⟩, ⟨.or, [6,11]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN71 := word 4276676736 4008241152
theorem basisN71 : Monotone2 circN71 ∧ FanInTwo circN71 := by simp [Monotone2,FanInTwo,circN71]
theorem evalN71 : ∀ x : Fin 6 → Bool, circN71.eval (List.ofFn x) = funcN71 x := by decide +kernel
theorem lowerN71 (s : ℕ) (h : HasCircuitSize 6 funcN71 s) : 11 ≤ s :=
  extension funcN71 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN71 (s : ℕ) : HasCircuitSize 6 funcN71 s ↔ 11 ≤ s :=
  ⟨lowerN71 s, fun h => ⟨circN71,(basisN71).2,h,evalN71⟩⟩
def circN72 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [3,4]⟩, ⟨.or, [0,1]⟩, ⟨.or, [3,4]⟩, ⟨.and, [8,5]⟩, ⟨.and, [10,9]⟩, ⟨.and, [2,11]⟩, ⟨.or, [2,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN72 := word 4276676736 4034953344
theorem basisN72 : Monotone2 circN72 ∧ FanInTwo circN72 := by simp [Monotone2,FanInTwo,circN72]
theorem evalN72 : ∀ x : Fin 6 → Bool, circN72.eval (List.ofFn x) = funcN72 x := by decide +kernel
theorem lowerN72 (s : ℕ) (h : HasCircuitSize 6 funcN72 s) : 11 ≤ s :=
  extension funcN72 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (11 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN72 (s : ℕ) : HasCircuitSize 6 funcN72 s ↔ 11 ≤ s :=
  ⟨lowerN72 s, fun h => ⟨circN72,(basisN72).2,h,evalN72⟩⟩
def circN73 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [3,4]⟩, ⟨.or, [0,1]⟩, ⟨.or, [3,4]⟩, ⟨.and, [8,9]⟩, ⟨.and, [2,10]⟩, ⟨.and, [10,5]⟩, ⟨.or, [2,12]⟩, ⟨.or, [6,11]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN73 := word 4276676736 4041269376
theorem basisN73 : Monotone2 circN73 ∧ FanInTwo circN73 := by simp [Monotone2,FanInTwo,circN73]
theorem evalN73 : ∀ x : Fin 6 → Bool, circN73.eval (List.ofFn x) = funcN73 x := by decide +kernel
theorem lowerN73 (s : ℕ) (h : HasCircuitSize 6 funcN73 s) : 11 ≤ s :=
  extension funcN73 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (11 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN73 (s : ℕ) : HasCircuitSize 6 funcN73 s ↔ 11 ≤ s :=
  ⟨lowerN73 s, fun h => ⟨circN73,(basisN73).2,h,evalN73⟩⟩
def circN74 : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.or, [3,4]⟩, ⟨.and, [0,1]⟩, ⟨.and, [3,4]⟩, ⟨.or, [8,9]⟩, ⟨.and, [10,5]⟩, ⟨.or, [2,11]⟩, ⟨.and, [2,11]⟩, ⟨.and, [6,12]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN74 := word 4276676736 3772833792
theorem basisN74 : Monotone2 circN74 ∧ FanInTwo circN74 := by simp [Monotone2,FanInTwo,circN74]
theorem evalN74 : ∀ x : Fin 6 → Bool, circN74.eval (List.ofFn x) = funcN74 x := by decide +kernel
theorem lowerN74 (s : ℕ) (h : HasCircuitSize 6 funcN74 s) : 11 ≤ s :=
  extension funcN74 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN74 (s : ℕ) : HasCircuitSize 6 funcN74 s ↔ 11 ≤ s :=
  ⟨lowerN74 s, fun h => ⟨circN74,(basisN74).2,h,evalN74⟩⟩
def circN75 : Circuit := ⟨[⟨.and, [0,5]⟩, ⟨.and, [6,2]⟩, ⟨.and, [1,3]⟩, ⟨.or, [0,2]⟩, ⟨.or, [1,3]⟩, ⟨.and, [9,10]⟩, ⟨.and, [4,11]⟩, ⟨.or, [4,11]⟩, ⟨.or, [7,12]⟩, ⟨.or, [8,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN75 := word 4276676736 4274571264
theorem basisN75 : Monotone2 circN75 ∧ FanInTwo circN75 := by simp [Monotone2,FanInTwo,circN75]
theorem evalN75 : ∀ x : Fin 6 → Bool, circN75.eval (List.ofFn x) = funcN75 x := by decide +kernel
theorem lowerN75 (s : ℕ) (h : HasCircuitSize 6 funcN75 s) : 11 ≤ s :=
  extension funcN75 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN75 (s : ℕ) : HasCircuitSize 6 funcN75 s ↔ 11 ≤ s :=
  ⟨lowerN75 s, fun h => ⟨circN75,(basisN75).2,h,evalN75⟩⟩
def circN76 : Circuit := ⟨[⟨.and, [0,2]⟩, ⟨.and, [1,3]⟩, ⟨.and, [0,5]⟩, ⟨.or, [8,2]⟩, ⟨.or, [1,3]⟩, ⟨.and, [9,10]⟩, ⟨.and, [4,11]⟩, ⟨.or, [4,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN76 := word 4276676736 4242595968
theorem basisN76 : Monotone2 circN76 ∧ FanInTwo circN76 := by simp [Monotone2,FanInTwo,circN76]
theorem evalN76 : ∀ x : Fin 6 → Bool, circN76.eval (List.ofFn x) = funcN76 x := by decide +kernel
theorem lowerN76 (s : ℕ) (h : HasCircuitSize 6 funcN76 s) : 11 ≤ s :=
  extension funcN76 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (11 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN76 (s : ℕ) : HasCircuitSize 6 funcN76 s ↔ 11 ≤ s :=
  ⟨lowerN76 s, fun h => ⟨circN76,(basisN76).2,h,evalN76⟩⟩
def circN77 : Circuit := ⟨[⟨.and, [0,2]⟩, ⟨.and, [1,3]⟩, ⟨.and, [2,5]⟩, ⟨.or, [0,8]⟩, ⟨.or, [1,3]⟩, ⟨.and, [9,10]⟩, ⟨.and, [4,11]⟩, ⟨.or, [4,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN77 := word 4276676736 4004030592
theorem basisN77 : Monotone2 circN77 ∧ FanInTwo circN77 := by simp [Monotone2,FanInTwo,circN77]
theorem evalN77 : ∀ x : Fin 6 → Bool, circN77.eval (List.ofFn x) = funcN77 x := by decide +kernel
theorem lowerN77 (s : ℕ) (h : HasCircuitSize 6 funcN77 s) : 11 ≤ s :=
  extension funcN77 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (14 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN77 (s : ℕ) : HasCircuitSize 6 funcN77 s ↔ 11 ≤ s :=
  ⟨lowerN77 s, fun h => ⟨circN77,(basisN77).2,h,evalN77⟩⟩
def circN78 : Circuit := ⟨[⟨.and, [0,2]⟩, ⟨.and, [1,5]⟩, ⟨.and, [7,3]⟩, ⟨.or, [0,2]⟩, ⟨.or, [1,3]⟩, ⟨.and, [9,10]⟩, ⟨.and, [4,11]⟩, ⟨.or, [4,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [8,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN78 := word 4276676736 4209549440
theorem basisN78 : Monotone2 circN78 ∧ FanInTwo circN78 := by simp [Monotone2,FanInTwo,circN78]
theorem evalN78 : ∀ x : Fin 6 → Bool, circN78.eval (List.ofFn x) = funcN78 x := by decide +kernel
theorem lowerN78 (s : ℕ) (h : HasCircuitSize 6 funcN78 s) : 11 ≤ s :=
  extension funcN78 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (11 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN78 (s : ℕ) : HasCircuitSize 6 funcN78 s ↔ 11 ≤ s :=
  ⟨lowerN78 s, fun h => ⟨circN78,(basisN78).2,h,evalN78⟩⟩
def circN79 : Circuit := ⟨[⟨.and, [0,2]⟩, ⟨.and, [1,3]⟩, ⟨.or, [0,2]⟩, ⟨.and, [1,5]⟩, ⟨.or, [9,3]⟩, ⟨.and, [8,10]⟩, ⟨.and, [4,11]⟩, ⟨.or, [4,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN79 := word 4276676736 4271958016
theorem basisN79 : Monotone2 circN79 ∧ FanInTwo circN79 := by simp [Monotone2,FanInTwo,circN79]
theorem evalN79 : ∀ x : Fin 6 → Bool, circN79.eval (List.ofFn x) = funcN79 x := by decide +kernel
theorem lowerN79 (s : ℕ) (h : HasCircuitSize 6 funcN79 s) : 11 ≤ s :=
  extension funcN79 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN79 (s : ℕ) : HasCircuitSize 6 funcN79 s ↔ 11 ≤ s :=
  ⟨lowerN79 s, fun h => ⟨circN79,(basisN79).2,h,evalN79⟩⟩
def circN80 : Circuit := ⟨[⟨.and, [0,2]⟩, ⟨.and, [1,3]⟩, ⟨.or, [0,2]⟩, ⟨.and, [3,5]⟩, ⟨.or, [1,9]⟩, ⟨.and, [8,10]⟩, ⟨.and, [4,11]⟩, ⟨.or, [4,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN80 := word 4276676736 3974678656
theorem basisN80 : Monotone2 circN80 ∧ FanInTwo circN80 := by simp [Monotone2,FanInTwo,circN80]
theorem evalN80 : ∀ x : Fin 6 → Bool, circN80.eval (List.ofFn x) = funcN80 x := by decide +kernel
theorem lowerN80 (s : ℕ) (h : HasCircuitSize 6 funcN80 s) : 11 ≤ s :=
  extension funcN80 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (13 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN80 (s : ℕ) : HasCircuitSize 6 funcN80 s ↔ 11 ≤ s :=
  ⟨lowerN80 s, fun h => ⟨circN80,(basisN80).2,h,evalN80⟩⟩
def circN81 : Circuit := ⟨[⟨.and, [0,2]⟩, ⟨.and, [1,3]⟩, ⟨.or, [0,2]⟩, ⟨.or, [1,3]⟩, ⟨.and, [8,9]⟩, ⟨.and, [4,5]⟩, ⟨.and, [11,10]⟩, ⟨.or, [4,10]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN81 := word 4276676736 3969968256
theorem basisN81 : Monotone2 circN81 ∧ FanInTwo circN81 := by simp [Monotone2,FanInTwo,circN81]
theorem evalN81 : ∀ x : Fin 6 → Bool, circN81.eval (List.ofFn x) = funcN81 x := by decide +kernel
theorem lowerN81 (s : ℕ) (h : HasCircuitSize 6 funcN81 s) : 11 ≤ s :=
  extension funcN81 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (19 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN81 (s : ℕ) : HasCircuitSize 6 funcN81 s ↔ 11 ≤ s :=
  ⟨lowerN81 s, fun h => ⟨circN81,(basisN81).2,h,evalN81⟩⟩
def circN82 : Circuit := ⟨[⟨.and, [0,2]⟩, ⟨.and, [1,3]⟩, ⟨.or, [0,2]⟩, ⟨.or, [1,3]⟩, ⟨.and, [8,9]⟩, ⟨.and, [4,10]⟩, ⟨.and, [4,5]⟩, ⟨.or, [12,10]⟩, ⟨.or, [6,11]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN82 := word 4276676736 4207470720
theorem basisN82 : Monotone2 circN82 ∧ FanInTwo circN82 := by simp [Monotone2,FanInTwo,circN82]
theorem evalN82 : ∀ x : Fin 6 → Bool, circN82.eval (List.ofFn x) = funcN82 x := by decide +kernel
theorem lowerN82 (s : ℕ) (h : HasCircuitSize 6 funcN82 s) : 11 ≤ s :=
  extension funcN82 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (21 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN82 (s : ℕ) : HasCircuitSize 6 funcN82 s ↔ 11 ≤ s :=
  ⟨lowerN82 s, fun h => ⟨circN82,(basisN82).2,h,evalN82⟩⟩
def circN83 : Circuit := ⟨[⟨.and, [0,2]⟩, ⟨.and, [1,3]⟩, ⟨.or, [0,2]⟩, ⟨.or, [1,3]⟩, ⟨.and, [8,5]⟩, ⟨.and, [10,9]⟩, ⟨.and, [4,11]⟩, ⟨.or, [4,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN83 := word 4276676736 3969908736
theorem basisN83 : Monotone2 circN83 ∧ FanInTwo circN83 := by simp [Monotone2,FanInTwo,circN83]
theorem evalN83 : ∀ x : Fin 6 → Bool, circN83.eval (List.ofFn x) = funcN83 x := by decide +kernel
theorem lowerN83 (s : ℕ) (h : HasCircuitSize 6 funcN83 s) : 11 ≤ s :=
  extension funcN83 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN83 (s : ℕ) : HasCircuitSize 6 funcN83 s ↔ 11 ≤ s :=
  ⟨lowerN83 s, fun h => ⟨circN83,(basisN83).2,h,evalN83⟩⟩
def circN84 : Circuit := ⟨[⟨.and, [0,2]⟩, ⟨.and, [1,3]⟩, ⟨.or, [0,2]⟩, ⟨.or, [1,3]⟩, ⟨.and, [8,9]⟩, ⟨.and, [4,10]⟩, ⟨.or, [4,10]⟩, ⟨.or, [6,11]⟩, ⟨.and, [13,5]⟩, ⟨.or, [7,14]⟩, ⟨.and, [12,15]⟩], 16⟩
def funcN84 := word 4276676736 3422603264
theorem basisN84 : Monotone2 circN84 ∧ FanInTwo circN84 := by simp [Monotone2,FanInTwo,circN84]
theorem evalN84 : ∀ x : Fin 6 → Bool, circN84.eval (List.ofFn x) = funcN84 x := by decide +kernel
theorem lowerN84 (s : ℕ) (h : HasCircuitSize 6 funcN84 s) : 11 ≤ s :=
  extension funcN84 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN84 (s : ℕ) : HasCircuitSize 6 funcN84 s ↔ 11 ≤ s :=
  ⟨lowerN84 s, fun h => ⟨circN84,(basisN84).2,h,evalN84⟩⟩
def circN85 : Circuit := ⟨[⟨.or, [0,2]⟩, ⟨.or, [1,3]⟩, ⟨.and, [0,2]⟩, ⟨.and, [1,3]⟩, ⟨.or, [8,9]⟩, ⟨.and, [10,5]⟩, ⟨.or, [4,11]⟩, ⟨.and, [4,11]⟩, ⟨.and, [6,12]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN85 := word 4276676736 4207411200
theorem basisN85 : Monotone2 circN85 ∧ FanInTwo circN85 := by simp [Monotone2,FanInTwo,circN85]
theorem evalN85 : ∀ x : Fin 6 → Bool, circN85.eval (List.ofFn x) = funcN85 x := by decide +kernel
theorem lowerN85 (s : ℕ) (h : HasCircuitSize 6 funcN85 s) : 11 ≤ s :=
  extension funcN85 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN85 (s : ℕ) : HasCircuitSize 6 funcN85 s ↔ 11 ≤ s :=
  ⟨lowerN85 s, fun h => ⟨circN85,(basisN85).2,h,evalN85⟩⟩
def circN86 : Circuit := ⟨[⟨.and, [0,2]⟩, ⟨.and, [1,5]⟩, ⟨.and, [7,4]⟩, ⟨.or, [0,2]⟩, ⟨.or, [1,4]⟩, ⟨.and, [9,10]⟩, ⟨.and, [3,11]⟩, ⟨.or, [3,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [8,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN86 := word 4276676736 4204849280
theorem basisN86 : Monotone2 circN86 ∧ FanInTwo circN86 := by simp [Monotone2,FanInTwo,circN86]
theorem evalN86 : ∀ x : Fin 6 → Bool, circN86.eval (List.ofFn x) = funcN86 x := by decide +kernel
theorem lowerN86 (s : ℕ) (h : HasCircuitSize 6 funcN86 s) : 11 ≤ s :=
  extension funcN86 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (19 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN86 (s : ℕ) : HasCircuitSize 6 funcN86 s ↔ 11 ≤ s :=
  ⟨lowerN86 s, fun h => ⟨circN86,(basisN86).2,h,evalN86⟩⟩
def circN87 : Circuit := ⟨[⟨.and, [0,2]⟩, ⟨.and, [1,4]⟩, ⟨.or, [0,2]⟩, ⟨.and, [1,5]⟩, ⟨.or, [9,4]⟩, ⟨.and, [8,10]⟩, ⟨.and, [3,11]⟩, ⟨.or, [3,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN87 := word 4276676736 4276658176
theorem basisN87 : Monotone2 circN87 ∧ FanInTwo circN87 := by simp [Monotone2,FanInTwo,circN87]
theorem evalN87 : ∀ x : Fin 6 → Bool, circN87.eval (List.ofFn x) = funcN87 x := by decide +kernel
theorem lowerN87 (s : ℕ) (h : HasCircuitSize 6 funcN87 s) : 11 ≤ s :=
  extension funcN87 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN87 (s : ℕ) : HasCircuitSize 6 funcN87 s ↔ 11 ≤ s :=
  ⟨lowerN87 s, fun h => ⟨circN87,(basisN87).2,h,evalN87⟩⟩
def circN88 : Circuit := ⟨[⟨.and, [0,2]⟩, ⟨.and, [1,4]⟩, ⟨.or, [0,2]⟩, ⟨.and, [4,5]⟩, ⟨.or, [1,9]⟩, ⟨.and, [8,10]⟩, ⟨.and, [3,11]⟩, ⟨.or, [3,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN88 := word 4276676736 3972589696
theorem basisN88 : Monotone2 circN88 ∧ FanInTwo circN88 := by simp [Monotone2,FanInTwo,circN88]
theorem evalN88 : ∀ x : Fin 6 → Bool, circN88.eval (List.ofFn x) = funcN88 x := by decide +kernel
theorem lowerN88 (s : ℕ) (h : HasCircuitSize 6 funcN88 s) : 11 ≤ s :=
  extension funcN88 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (21 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN88 (s : ℕ) : HasCircuitSize 6 funcN88 s ↔ 11 ≤ s :=
  ⟨lowerN88 s, fun h => ⟨circN88,(basisN88).2,h,evalN88⟩⟩
def circN89 : Circuit := ⟨[⟨.and, [0,2]⟩, ⟨.and, [1,4]⟩, ⟨.or, [0,2]⟩, ⟨.or, [1,4]⟩, ⟨.and, [8,9]⟩, ⟨.and, [3,5]⟩, ⟨.and, [11,10]⟩, ⟨.or, [3,10]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN89 := word 4276676736 3974668416
theorem basisN89 : Monotone2 circN89 ∧ FanInTwo circN89 := by simp [Monotone2,FanInTwo,circN89]
theorem evalN89 : ∀ x : Fin 6 → Bool, circN89.eval (List.ofFn x) = funcN89 x := by decide +kernel
theorem lowerN89 (s : ℕ) (h : HasCircuitSize 6 funcN89 s) : 11 ≤ s :=
  extension funcN89 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (11 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN89 (s : ℕ) : HasCircuitSize 6 funcN89 s ↔ 11 ≤ s :=
  ⟨lowerN89 s, fun h => ⟨circN89,(basisN89).2,h,evalN89⟩⟩
def circN90 : Circuit := ⟨[⟨.and, [0,2]⟩, ⟨.and, [1,4]⟩, ⟨.or, [0,2]⟩, ⟨.or, [1,4]⟩, ⟨.and, [8,9]⟩, ⟨.and, [3,10]⟩, ⟨.and, [3,5]⟩, ⟨.or, [12,10]⟩, ⟨.or, [6,11]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN90 := word 4276676736 4209559680
theorem basisN90 : Monotone2 circN90 ∧ FanInTwo circN90 := by simp [Monotone2,FanInTwo,circN90]
theorem evalN90 : ∀ x : Fin 6 → Bool, circN90.eval (List.ofFn x) = funcN90 x := by decide +kernel
theorem lowerN90 (s : ℕ) (h : HasCircuitSize 6 funcN90 s) : 11 ≤ s :=
  extension funcN90 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (13 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN90 (s : ℕ) : HasCircuitSize 6 funcN90 s ↔ 11 ≤ s :=
  ⟨lowerN90 s, fun h => ⟨circN90,(basisN90).2,h,evalN90⟩⟩
def circN91 : Circuit := ⟨[⟨.and, [0,2]⟩, ⟨.and, [1,4]⟩, ⟨.or, [0,2]⟩, ⟨.or, [1,4]⟩, ⟨.and, [8,5]⟩, ⟨.and, [10,9]⟩, ⟨.and, [3,11]⟩, ⟨.or, [3,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN91 := word 4276676736 3959463936
theorem basisN91 : Monotone2 circN91 ∧ FanInTwo circN91 := by simp [Monotone2,FanInTwo,circN91]
theorem evalN91 : ∀ x : Fin 6 → Bool, circN91.eval (List.ofFn x) = funcN91 x := by decide +kernel
theorem lowerN91 (s : ℕ) (h : HasCircuitSize 6 funcN91 s) : 11 ≤ s :=
  extension funcN91 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN91 (s : ℕ) : HasCircuitSize 6 funcN91 s ↔ 11 ≤ s :=
  ⟨lowerN91 s, fun h => ⟨circN91,(basisN91).2,h,evalN91⟩⟩
def circN92 : Circuit := ⟨[⟨.and, [0,2]⟩, ⟨.and, [1,4]⟩, ⟨.or, [0,2]⟩, ⟨.or, [1,4]⟩, ⟨.and, [8,9]⟩, ⟨.and, [3,10]⟩, ⟨.or, [3,10]⟩, ⟨.or, [6,11]⟩, ⟨.and, [13,5]⟩, ⟨.or, [7,14]⟩, ⟨.and, [12,15]⟩], 16⟩
def funcN92 := word 4276676736 3435659264
theorem basisN92 : Monotone2 circN92 ∧ FanInTwo circN92 := by simp [Monotone2,FanInTwo,circN92]
theorem evalN92 : ∀ x : Fin 6 → Bool, circN92.eval (List.ofFn x) = funcN92 x := by decide +kernel
theorem lowerN92 (s : ℕ) (h : HasCircuitSize 6 funcN92 s) : 11 ≤ s :=
  extension funcN92 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN92 (s : ℕ) : HasCircuitSize 6 funcN92 s ↔ 11 ≤ s :=
  ⟨lowerN92 s, fun h => ⟨circN92,(basisN92).2,h,evalN92⟩⟩
def circN93 : Circuit := ⟨[⟨.or, [0,2]⟩, ⟨.or, [1,4]⟩, ⟨.and, [0,2]⟩, ⟨.and, [1,4]⟩, ⟨.or, [8,9]⟩, ⟨.and, [10,5]⟩, ⟨.or, [3,11]⟩, ⟨.and, [3,11]⟩, ⟨.and, [6,12]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN93 := word 4276676736 4194355200
theorem basisN93 : Monotone2 circN93 ∧ FanInTwo circN93 := by simp [Monotone2,FanInTwo,circN93]
theorem evalN93 : ∀ x : Fin 6 → Bool, circN93.eval (List.ofFn x) = funcN93 x := by decide +kernel
theorem lowerN93 (s : ℕ) (h : HasCircuitSize 6 funcN93 s) : 11 ≤ s :=
  extension funcN93 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN93 (s : ℕ) : HasCircuitSize 6 funcN93 s ↔ 11 ≤ s :=
  ⟨lowerN93 s, fun h => ⟨circN93,(basisN93).2,h,evalN93⟩⟩
def circN94 : Circuit := ⟨[⟨.and, [0,2]⟩, ⟨.and, [3,4]⟩, ⟨.or, [0,2]⟩, ⟨.or, [3,4]⟩, ⟨.and, [8,9]⟩, ⟨.and, [1,5]⟩, ⟨.and, [11,10]⟩, ⟨.or, [1,10]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN94 := word 4276676736 4271939712
theorem basisN94 : Monotone2 circN94 ∧ FanInTwo circN94 := by simp [Monotone2,FanInTwo,circN94]
theorem evalN94 : ∀ x : Fin 6 → Bool, circN94.eval (List.ofFn x) = funcN94 x := by decide +kernel
theorem lowerN94 (s : ℕ) (h : HasCircuitSize 6 funcN94 s) : 11 ≤ s :=
  extension funcN94 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (11 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN94 (s : ℕ) : HasCircuitSize 6 funcN94 s ↔ 11 ≤ s :=
  ⟨lowerN94 s, fun h => ⟨circN94,(basisN94).2,h,evalN94⟩⟩
def circN95 : Circuit := ⟨[⟨.and, [0,2]⟩, ⟨.and, [3,4]⟩, ⟨.or, [0,2]⟩, ⟨.or, [3,4]⟩, ⟨.and, [8,9]⟩, ⟨.and, [1,10]⟩, ⟨.and, [1,5]⟩, ⟨.or, [12,10]⟩, ⟨.or, [6,11]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN95 := word 4276676736 4209567744
theorem basisN95 : Monotone2 circN95 ∧ FanInTwo circN95 := by simp [Monotone2,FanInTwo,circN95]
theorem evalN95 : ∀ x : Fin 6 → Bool, circN95.eval (List.ofFn x) = funcN95 x := by decide +kernel
theorem lowerN95 (s : ℕ) (h : HasCircuitSize 6 funcN95 s) : 11 ≤ s :=
  extension funcN95 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN95 (s : ℕ) : HasCircuitSize 6 funcN95 s ↔ 11 ≤ s :=
  ⟨lowerN95 s, fun h => ⟨circN95,(basisN95).2,h,evalN95⟩⟩
def circN96 : Circuit := ⟨[⟨.and, [0,2]⟩, ⟨.and, [3,4]⟩, ⟨.or, [0,2]⟩, ⟨.or, [3,4]⟩, ⟨.and, [8,5]⟩, ⟨.and, [10,9]⟩, ⟨.and, [1,11]⟩, ⟨.or, [1,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN96 := word 4276676736 3430973568
theorem basisN96 : Monotone2 circN96 ∧ FanInTwo circN96 := by simp [Monotone2,FanInTwo,circN96]
theorem evalN96 : ∀ x : Fin 6 → Bool, circN96.eval (List.ofFn x) = funcN96 x := by decide +kernel
theorem lowerN96 (s : ℕ) (h : HasCircuitSize 6 funcN96 s) : 11 ≤ s :=
  extension funcN96 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (11 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN96 (s : ℕ) : HasCircuitSize 6 funcN96 s ↔ 11 ≤ s :=
  ⟨lowerN96 s, fun h => ⟨circN96,(basisN96).2,h,evalN96⟩⟩
def circN97 : Circuit := ⟨[⟨.and, [0,2]⟩, ⟨.and, [3,4]⟩, ⟨.or, [0,2]⟩, ⟨.or, [3,4]⟩, ⟨.and, [8,9]⟩, ⟨.and, [1,10]⟩, ⟨.and, [10,5]⟩, ⟨.or, [1,12]⟩, ⟨.or, [6,11]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN97 := word 4276676736 3435710592
theorem basisN97 : Monotone2 circN97 ∧ FanInTwo circN97 := by simp [Monotone2,FanInTwo,circN97]
theorem evalN97 : ∀ x : Fin 6 → Bool, circN97.eval (List.ofFn x) = funcN97 x := by decide +kernel
theorem lowerN97 (s : ℕ) (h : HasCircuitSize 6 funcN97 s) : 11 ≤ s :=
  extension funcN97 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (13 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN97 (s : ℕ) : HasCircuitSize 6 funcN97 s ↔ 11 ≤ s :=
  ⟨lowerN97 s, fun h => ⟨circN97,(basisN97).2,h,evalN97⟩⟩
def circN98 : Circuit := ⟨[⟨.or, [0,2]⟩, ⟨.or, [3,4]⟩, ⟨.and, [0,2]⟩, ⟨.and, [3,4]⟩, ⟨.or, [8,9]⟩, ⟨.and, [10,5]⟩, ⟨.or, [1,11]⟩, ⟨.and, [1,11]⟩, ⟨.and, [6,12]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN98 := word 4276676736 3368601600
theorem basisN98 : Monotone2 circN98 ∧ FanInTwo circN98 := by simp [Monotone2,FanInTwo,circN98]
theorem evalN98 : ∀ x : Fin 6 → Bool, circN98.eval (List.ofFn x) = funcN98 x := by decide +kernel
theorem lowerN98 (s : ℕ) (h : HasCircuitSize 6 funcN98 s) : 11 ≤ s :=
  extension funcN98 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN98 (s : ℕ) : HasCircuitSize 6 funcN98 s ↔ 11 ≤ s :=
  ⟨lowerN98 s, fun h => ⟨circN98,(basisN98).2,h,evalN98⟩⟩
def circN99 : Circuit := ⟨[⟨.and, [0,5]⟩, ⟨.and, [6,3]⟩, ⟨.and, [1,2]⟩, ⟨.or, [0,3]⟩, ⟨.or, [1,2]⟩, ⟨.and, [9,10]⟩, ⟨.and, [4,11]⟩, ⟨.or, [4,11]⟩, ⟨.or, [7,12]⟩, ⟨.or, [8,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN99 := word 4276676736 4243112064
theorem basisN99 : Monotone2 circN99 ∧ FanInTwo circN99 := by simp [Monotone2,FanInTwo,circN99]
theorem evalN99 : ∀ x : Fin 6 → Bool, circN99.eval (List.ofFn x) = funcN99 x := by decide +kernel
theorem lowerN99 (s : ℕ) (h : HasCircuitSize 6 funcN99 s) : 11 ≤ s :=
  extension funcN99 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (11 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN99 (s : ℕ) : HasCircuitSize 6 funcN99 s ↔ 11 ≤ s :=
  ⟨lowerN99 s, fun h => ⟨circN99,(basisN99).2,h,evalN99⟩⟩
def circN100 : Circuit := ⟨[⟨.and, [0,3]⟩, ⟨.and, [1,2]⟩, ⟨.and, [0,5]⟩, ⟨.or, [8,3]⟩, ⟨.or, [1,2]⟩, ⟨.and, [9,10]⟩, ⟨.and, [4,11]⟩, ⟨.or, [4,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN100 := word 4276676736 4274055168
theorem basisN100 : Monotone2 circN100 ∧ FanInTwo circN100 := by simp [Monotone2,FanInTwo,circN100]
theorem evalN100 : ∀ x : Fin 6 → Bool, circN100.eval (List.ofFn x) = funcN100 x := by decide +kernel
theorem lowerN100 (s : ℕ) (h : HasCircuitSize 6 funcN100 s) : 11 ≤ s :=
  extension funcN100 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN100 (s : ℕ) : HasCircuitSize 6 funcN100 s ↔ 11 ≤ s :=
  ⟨lowerN100 s, fun h => ⟨circN100,(basisN100).2,h,evalN100⟩⟩
def circN101 : Circuit := ⟨[⟨.and, [0,3]⟩, ⟨.and, [1,2]⟩, ⟨.and, [3,5]⟩, ⟨.or, [0,8]⟩, ⟨.or, [1,2]⟩, ⟨.and, [9,10]⟩, ⟨.and, [4,11]⟩, ⟨.or, [4,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN101 := word 4276676736 3941116032
theorem basisN101 : Monotone2 circN101 ∧ FanInTwo circN101 := by simp [Monotone2,FanInTwo,circN101]
theorem evalN101 : ∀ x : Fin 6 → Bool, circN101.eval (List.ofFn x) = funcN101 x := by decide +kernel
theorem lowerN101 (s : ℕ) (h : HasCircuitSize 6 funcN101 s) : 11 ≤ s :=
  extension funcN101 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (14 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN101 (s : ℕ) : HasCircuitSize 6 funcN101 s ↔ 11 ≤ s :=
  ⟨lowerN101 s, fun h => ⟨circN101,(basisN101).2,h,evalN101⟩⟩
def circN102 : Circuit := ⟨[⟨.and, [0,3]⟩, ⟨.and, [1,5]⟩, ⟨.and, [7,2]⟩, ⟨.or, [0,3]⟩, ⟨.or, [1,2]⟩, ⟨.and, [9,10]⟩, ⟨.and, [4,11]⟩, ⟨.or, [4,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [8,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN102 := word 4276676736 4272465920
theorem basisN102 : Monotone2 circN102 ∧ FanInTwo circN102 := by simp [Monotone2,FanInTwo,circN102]
theorem evalN102 : ∀ x : Fin 6 → Bool, circN102.eval (List.ofFn x) = funcN102 x := by decide +kernel
theorem lowerN102 (s : ℕ) (h : HasCircuitSize 6 funcN102 s) : 11 ≤ s :=
  extension funcN102 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN102 (s : ℕ) : HasCircuitSize 6 funcN102 s ↔ 11 ≤ s :=
  ⟨lowerN102 s, fun h => ⟨circN102,(basisN102).2,h,evalN102⟩⟩
def circN103 : Circuit := ⟨[⟨.and, [0,3]⟩, ⟨.and, [1,2]⟩, ⟨.or, [0,3]⟩, ⟨.and, [1,5]⟩, ⟨.or, [9,2]⟩, ⟨.and, [8,10]⟩, ⟨.and, [4,11]⟩, ⟨.or, [4,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN103 := word 4276676736 4209041536
theorem basisN103 : Monotone2 circN103 ∧ FanInTwo circN103 := by simp [Monotone2,FanInTwo,circN103]
theorem evalN103 : ∀ x : Fin 6 → Bool, circN103.eval (List.ofFn x) = funcN103 x := by decide +kernel
theorem lowerN103 (s : ℕ) (h : HasCircuitSize 6 funcN103 s) : 11 ≤ s :=
  extension funcN103 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (11 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN103 (s : ℕ) : HasCircuitSize 6 funcN103 s ↔ 11 ≤ s :=
  ⟨lowerN103 s, fun h => ⟨circN103,(basisN103).2,h,evalN103⟩⟩
def circN104 : Circuit := ⟨[⟨.and, [0,3]⟩, ⟨.and, [1,2]⟩, ⟨.or, [0,3]⟩, ⟨.and, [2,5]⟩, ⟨.or, [1,9]⟩, ⟨.and, [8,10]⟩, ⟨.and, [4,11]⟩, ⟨.or, [4,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN104 := word 4276676736 4006135936
theorem basisN104 : Monotone2 circN104 ∧ FanInTwo circN104 := by simp [Monotone2,FanInTwo,circN104]
theorem evalN104 : ∀ x : Fin 6 → Bool, circN104.eval (List.ofFn x) = funcN104 x := by decide +kernel
theorem lowerN104 (s : ℕ) (h : HasCircuitSize 6 funcN104 s) : 11 ≤ s :=
  extension funcN104 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (13 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN104 (s : ℕ) : HasCircuitSize 6 funcN104 s ↔ 11 ≤ s :=
  ⟨lowerN104 s, fun h => ⟨circN104,(basisN104).2,h,evalN104⟩⟩
def circN105 : Circuit := ⟨[⟨.and, [0,3]⟩, ⟨.and, [1,2]⟩, ⟨.or, [0,3]⟩, ⟨.or, [1,2]⟩, ⟨.and, [8,9]⟩, ⟨.and, [4,5]⟩, ⟨.and, [11,10]⟩, ⟨.or, [4,10]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN105 := word 4276676736 3938510976
theorem basisN105 : Monotone2 circN105 ∧ FanInTwo circN105 := by simp [Monotone2,FanInTwo,circN105]
theorem evalN105 : ∀ x : Fin 6 → Bool, circN105.eval (List.ofFn x) = funcN105 x := by decide +kernel
theorem lowerN105 (s : ℕ) (h : HasCircuitSize 6 funcN105 s) : 11 ≤ s :=
  extension funcN105 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (19 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN105 (s : ℕ) : HasCircuitSize 6 funcN105 s ↔ 11 ≤ s :=
  ⟨lowerN105 s, fun h => ⟨circN105,(basisN105).2,h,evalN105⟩⟩
def circN106 : Circuit := ⟨[⟨.and, [0,3]⟩, ⟨.and, [1,2]⟩, ⟨.or, [0,3]⟩, ⟨.or, [1,2]⟩, ⟨.and, [8,9]⟩, ⟨.and, [4,10]⟩, ⟨.and, [4,5]⟩, ⟨.or, [12,10]⟩, ⟨.or, [6,11]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN106 := word 4276676736 4238928000
theorem basisN106 : Monotone2 circN106 ∧ FanInTwo circN106 := by simp [Monotone2,FanInTwo,circN106]
theorem evalN106 : ∀ x : Fin 6 → Bool, circN106.eval (List.ofFn x) = funcN106 x := by decide +kernel
theorem lowerN106 (s : ℕ) (h : HasCircuitSize 6 funcN106 s) : 11 ≤ s :=
  extension funcN106 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (22 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN106 (s : ℕ) : HasCircuitSize 6 funcN106 s ↔ 11 ≤ s :=
  ⟨lowerN106 s, fun h => ⟨circN106,(basisN106).2,h,evalN106⟩⟩
def circN107 : Circuit := ⟨[⟨.and, [0,3]⟩, ⟨.and, [1,2]⟩, ⟨.or, [0,3]⟩, ⟨.or, [1,2]⟩, ⟨.and, [8,5]⟩, ⟨.and, [10,9]⟩, ⟨.and, [4,11]⟩, ⟨.or, [4,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN107 := word 4276676736 3938451456
theorem basisN107 : Monotone2 circN107 ∧ FanInTwo circN107 := by simp [Monotone2,FanInTwo,circN107]
theorem evalN107 : ∀ x : Fin 6 → Bool, circN107.eval (List.ofFn x) = funcN107 x := by decide +kernel
theorem lowerN107 (s : ℕ) (h : HasCircuitSize 6 funcN107 s) : 11 ≤ s :=
  extension funcN107 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN107 (s : ℕ) : HasCircuitSize 6 funcN107 s ↔ 11 ≤ s :=
  ⟨lowerN107 s, fun h => ⟨circN107,(basisN107).2,h,evalN107⟩⟩
def circN108 : Circuit := ⟨[⟨.and, [0,3]⟩, ⟨.and, [1,2]⟩, ⟨.or, [0,3]⟩, ⟨.or, [1,2]⟩, ⟨.and, [8,9]⟩, ⟨.and, [4,10]⟩, ⟨.or, [4,10]⟩, ⟨.or, [6,11]⟩, ⟨.and, [13,5]⟩, ⟨.or, [7,14]⟩, ⟨.and, [12,15]⟩], 16⟩
def funcN108 := word 4276676736 3233857664
theorem basisN108 : Monotone2 circN108 ∧ FanInTwo circN108 := by simp [Monotone2,FanInTwo,circN108]
theorem evalN108 : ∀ x : Fin 6 → Bool, circN108.eval (List.ofFn x) = funcN108 x := by decide +kernel
theorem lowerN108 (s : ℕ) (h : HasCircuitSize 6 funcN108 s) : 11 ≤ s :=
  extension funcN108 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (11 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN108 (s : ℕ) : HasCircuitSize 6 funcN108 s ↔ 11 ≤ s :=
  ⟨lowerN108 s, fun h => ⟨circN108,(basisN108).2,h,evalN108⟩⟩
def circN109 : Circuit := ⟨[⟨.or, [0,3]⟩, ⟨.or, [1,2]⟩, ⟨.and, [0,3]⟩, ⟨.and, [1,2]⟩, ⟨.or, [8,9]⟩, ⟨.and, [10,5]⟩, ⟨.or, [4,11]⟩, ⟨.and, [4,11]⟩, ⟨.and, [6,12]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN109 := word 4276676736 4238868480
theorem basisN109 : Monotone2 circN109 ∧ FanInTwo circN109 := by simp [Monotone2,FanInTwo,circN109]
theorem evalN109 : ∀ x : Fin 6 → Bool, circN109.eval (List.ofFn x) = funcN109 x := by decide +kernel
theorem lowerN109 (s : ℕ) (h : HasCircuitSize 6 funcN109 s) : 11 ≤ s :=
  extension funcN109 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN109 (s : ℕ) : HasCircuitSize 6 funcN109 s ↔ 11 ≤ s :=
  ⟨lowerN109 s, fun h => ⟨circN109,(basisN109).2,h,evalN109⟩⟩
def circN110 : Circuit := ⟨[⟨.and, [0,3]⟩, ⟨.and, [1,4]⟩, ⟨.or, [0,3]⟩, ⟨.or, [1,4]⟩, ⟨.and, [8,9]⟩, ⟨.and, [2,5]⟩, ⟨.and, [11,10]⟩, ⟨.or, [2,10]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN110 := word 4276676736 4006127616
theorem basisN110 : Monotone2 circN110 ∧ FanInTwo circN110 := by simp [Monotone2,FanInTwo,circN110]
theorem evalN110 : ∀ x : Fin 6 → Bool, circN110.eval (List.ofFn x) = funcN110 x := by decide +kernel
theorem lowerN110 (s : ℕ) (h : HasCircuitSize 6 funcN110 s) : 11 ≤ s :=
  extension funcN110 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN110 (s : ℕ) : HasCircuitSize 6 funcN110 s ↔ 11 ≤ s :=
  ⟨lowerN110 s, fun h => ⟨circN110,(basisN110).2,h,evalN110⟩⟩
def circN111 : Circuit := ⟨[⟨.and, [0,3]⟩, ⟨.and, [1,4]⟩, ⟨.or, [0,3]⟩, ⟨.or, [1,4]⟩, ⟨.and, [8,9]⟩, ⟨.and, [2,10]⟩, ⟨.and, [2,5]⟩, ⟨.or, [12,10]⟩, ⟨.or, [6,11]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN111 := word 4276676736 4272474240
theorem basisN111 : Monotone2 circN111 ∧ FanInTwo circN111 := by simp [Monotone2,FanInTwo,circN111]
theorem evalN111 : ∀ x : Fin 6 → Bool, circN111.eval (List.ofFn x) = funcN111 x := by decide +kernel
theorem lowerN111 (s : ℕ) (h : HasCircuitSize 6 funcN111 s) : 11 ≤ s :=
  extension funcN111 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (13 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN111 (s : ℕ) : HasCircuitSize 6 funcN111 s ↔ 11 ≤ s :=
  ⟨lowerN111 s, fun h => ⟨circN111,(basisN111).2,h,evalN111⟩⟩
def circN112 : Circuit := ⟨[⟨.and, [0,3]⟩, ⟨.and, [1,4]⟩, ⟨.or, [0,3]⟩, ⟨.or, [1,4]⟩, ⟨.and, [8,5]⟩, ⟨.and, [10,9]⟩, ⟨.and, [2,11]⟩, ⟨.or, [2,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN112 := word 4276676736 3770720256
theorem basisN112 : Monotone2 circN112 ∧ FanInTwo circN112 := by simp [Monotone2,FanInTwo,circN112]
theorem evalN112 : ∀ x : Fin 6 → Bool, circN112.eval (List.ofFn x) = funcN112 x := by decide +kernel
theorem lowerN112 (s : ℕ) (h : HasCircuitSize 6 funcN112 s) : 11 ≤ s :=
  extension funcN112 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN112 (s : ℕ) : HasCircuitSize 6 funcN112 s ↔ 11 ≤ s :=
  ⟨lowerN112 s, fun h => ⟨circN112,(basisN112).2,h,evalN112⟩⟩
def circN113 : Circuit := ⟨[⟨.or, [0,3]⟩, ⟨.or, [1,4]⟩, ⟨.and, [0,3]⟩, ⟨.and, [1,4]⟩, ⟨.or, [8,9]⟩, ⟨.and, [10,5]⟩, ⟨.or, [2,11]⟩, ⟨.and, [2,11]⟩, ⟨.and, [6,12]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN113 := word 4276676736 4037066880
theorem basisN113 : Monotone2 circN113 ∧ FanInTwo circN113 := by simp [Monotone2,FanInTwo,circN113]
theorem evalN113 : ∀ x : Fin 6 → Bool, circN113.eval (List.ofFn x) = funcN113 x := by decide +kernel
theorem lowerN113 (s : ℕ) (h : HasCircuitSize 6 funcN113 s) : 11 ≤ s :=
  extension funcN113 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (11 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN113 (s : ℕ) : HasCircuitSize 6 funcN113 s ↔ 11 ≤ s :=
  ⟨lowerN113 s, fun h => ⟨circN113,(basisN113).2,h,evalN113⟩⟩
def circN114 : Circuit := ⟨[⟨.and, [0,3]⟩, ⟨.and, [2,4]⟩, ⟨.or, [0,3]⟩, ⟨.or, [2,4]⟩, ⟨.and, [8,9]⟩, ⟨.and, [1,5]⟩, ⟨.and, [11,10]⟩, ⟨.or, [1,10]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN114 := word 4276676736 4209027072
theorem basisN114 : Monotone2 circN114 ∧ FanInTwo circN114 := by simp [Monotone2,FanInTwo,circN114]
theorem evalN114 : ∀ x : Fin 6 → Bool, circN114.eval (List.ofFn x) = funcN114 x := by decide +kernel
theorem lowerN114 (s : ℕ) (h : HasCircuitSize 6 funcN114 s) : 11 ≤ s :=
  extension funcN114 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN114 (s : ℕ) : HasCircuitSize 6 funcN114 s ↔ 11 ≤ s :=
  ⟨lowerN114 s, fun h => ⟨circN114,(basisN114).2,h,evalN114⟩⟩
def circN115 : Circuit := ⟨[⟨.and, [0,3]⟩, ⟨.and, [2,4]⟩, ⟨.or, [0,3]⟩, ⟨.or, [2,4]⟩, ⟨.and, [8,9]⟩, ⟨.and, [1,10]⟩, ⟨.and, [1,5]⟩, ⟨.or, [12,10]⟩, ⟨.or, [6,11]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN115 := word 4276676736 4272480384
theorem basisN115 : Monotone2 circN115 ∧ FanInTwo circN115 := by simp [Monotone2,FanInTwo,circN115]
theorem evalN115 : ∀ x : Fin 6 → Bool, circN115.eval (List.ofFn x) = funcN115 x := by decide +kernel
theorem lowerN115 (s : ℕ) (h : HasCircuitSize 6 funcN115 s) : 11 ≤ s :=
  extension funcN115 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (11 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN115 (s : ℕ) : HasCircuitSize 6 funcN115 s ↔ 11 ≤ s :=
  ⟨lowerN115 s, fun h => ⟨circN115,(basisN115).2,h,evalN115⟩⟩
def circN116 : Circuit := ⟨[⟨.and, [0,3]⟩, ⟨.and, [2,4]⟩, ⟨.or, [0,3]⟩, ⟨.or, [2,4]⟩, ⟨.and, [8,5]⟩, ⟨.and, [10,9]⟩, ⟨.and, [1,11]⟩, ⟨.or, [1,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN116 := word 4276676736 3368060928
theorem basisN116 : Monotone2 circN116 ∧ FanInTwo circN116 := by simp [Monotone2,FanInTwo,circN116]
theorem evalN116 : ∀ x : Fin 6 → Bool, circN116.eval (List.ofFn x) = funcN116 x := by decide +kernel
theorem lowerN116 (s : ℕ) (h : HasCircuitSize 6 funcN116 s) : 11 ≤ s :=
  extension funcN116 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN116 (s : ℕ) : HasCircuitSize 6 funcN116 s ↔ 11 ≤ s :=
  ⟨lowerN116 s, fun h => ⟨circN116,(basisN116).2,h,evalN116⟩⟩
def circN117 : Circuit := ⟨[⟨.or, [0,3]⟩, ⟨.or, [2,4]⟩, ⟨.and, [0,3]⟩, ⟨.and, [2,4]⟩, ⟨.or, [8,9]⟩, ⟨.and, [10,5]⟩, ⟨.or, [1,11]⟩, ⟨.and, [1,11]⟩, ⟨.and, [6,12]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN117 := word 4276676736 3431514240
theorem basisN117 : Monotone2 circN117 ∧ FanInTwo circN117 := by simp [Monotone2,FanInTwo,circN117]
theorem evalN117 : ∀ x : Fin 6 → Bool, circN117.eval (List.ofFn x) = funcN117 x := by decide +kernel
theorem lowerN117 (s : ℕ) (h : HasCircuitSize 6 funcN117 s) : 11 ≤ s :=
  extension funcN117 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (11 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN117 (s : ℕ) : HasCircuitSize 6 funcN117 s ↔ 11 ≤ s :=
  ⟨lowerN117 s, fun h => ⟨circN117,(basisN117).2,h,evalN117⟩⟩
def circN118 : Circuit := ⟨[⟨.and, [0,5]⟩, ⟨.and, [6,4]⟩, ⟨.and, [1,2]⟩, ⟨.or, [0,4]⟩, ⟨.or, [1,2]⟩, ⟨.and, [9,10]⟩, ⟨.and, [3,11]⟩, ⟨.or, [3,11]⟩, ⟨.or, [7,12]⟩, ⟨.or, [8,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN118 := word 4276676736 4240500864
theorem basisN118 : Monotone2 circN118 ∧ FanInTwo circN118 := by simp [Monotone2,FanInTwo,circN118]
theorem evalN118 : ∀ x : Fin 6 → Bool, circN118.eval (List.ofFn x) = funcN118 x := by decide +kernel
theorem lowerN118 (s : ℕ) (h : HasCircuitSize 6 funcN118 s) : 11 ≤ s :=
  extension funcN118 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (19 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN118 (s : ℕ) : HasCircuitSize 6 funcN118 s ↔ 11 ≤ s :=
  ⟨lowerN118 s, fun h => ⟨circN118,(basisN118).2,h,evalN118⟩⟩
def circN119 : Circuit := ⟨[⟨.and, [0,4]⟩, ⟨.and, [1,2]⟩, ⟨.and, [0,5]⟩, ⟨.or, [8,4]⟩, ⟨.or, [1,2]⟩, ⟨.and, [9,10]⟩, ⟨.and, [3,11]⟩, ⟨.or, [3,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN119 := word 4276676736 4276666368
theorem basisN119 : Monotone2 circN119 ∧ FanInTwo circN119 := by simp [Monotone2,FanInTwo,circN119]
theorem evalN119 : ∀ x : Fin 6 → Bool, circN119.eval (List.ofFn x) = funcN119 x := by decide +kernel
theorem lowerN119 (s : ℕ) (h : HasCircuitSize 6 funcN119 s) : 11 ≤ s :=
  extension funcN119 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN119 (s : ℕ) : HasCircuitSize 6 funcN119 s ↔ 11 ≤ s :=
  ⟨lowerN119 s, fun h => ⟨circN119,(basisN119).2,h,evalN119⟩⟩
def circN120 : Circuit := ⟨[⟨.and, [0,4]⟩, ⟨.and, [1,2]⟩, ⟨.and, [4,5]⟩, ⟨.or, [0,8]⟩, ⟨.or, [1,2]⟩, ⟨.and, [9,10]⟩, ⟨.and, [3,11]⟩, ⟨.or, [3,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN120 := word 4276676736 3936938112
theorem basisN120 : Monotone2 circN120 ∧ FanInTwo circN120 := by simp [Monotone2,FanInTwo,circN120]
theorem evalN120 : ∀ x : Fin 6 → Bool, circN120.eval (List.ofFn x) = funcN120 x := by decide +kernel
theorem lowerN120 (s : ℕ) (h : HasCircuitSize 6 funcN120 s) : 11 ≤ s :=
  extension funcN120 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (22 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN120 (s : ℕ) : HasCircuitSize 6 funcN120 s ↔ 11 ≤ s :=
  ⟨lowerN120 s, fun h => ⟨circN120,(basisN120).2,h,evalN120⟩⟩
def circN121 : Circuit := ⟨[⟨.and, [0,4]⟩, ⟨.and, [1,2]⟩, ⟨.or, [0,4]⟩, ⟨.or, [1,2]⟩, ⟨.and, [8,9]⟩, ⟨.and, [3,5]⟩, ⟨.and, [11,10]⟩, ⟨.or, [3,10]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN121 := word 4276676736 3941122176
theorem basisN121 : Monotone2 circN121 ∧ FanInTwo circN121 := by simp [Monotone2,FanInTwo,circN121]
theorem evalN121 : ∀ x : Fin 6 → Bool, circN121.eval (List.ofFn x) = funcN121 x := by decide +kernel
theorem lowerN121 (s : ℕ) (h : HasCircuitSize 6 funcN121 s) : 11 ≤ s :=
  extension funcN121 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (11 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN121 (s : ℕ) : HasCircuitSize 6 funcN121 s ↔ 11 ≤ s :=
  ⟨lowerN121 s, fun h => ⟨circN121,(basisN121).2,h,evalN121⟩⟩
def circN122 : Circuit := ⟨[⟨.and, [0,4]⟩, ⟨.and, [1,2]⟩, ⟨.or, [0,4]⟩, ⟨.or, [1,2]⟩, ⟨.and, [8,9]⟩, ⟨.and, [3,10]⟩, ⟨.and, [3,5]⟩, ⟨.or, [12,10]⟩, ⟨.or, [6,11]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN122 := word 4276676736 4243105920
theorem basisN122 : Monotone2 circN122 ∧ FanInTwo circN122 := by simp [Monotone2,FanInTwo,circN122]
theorem evalN122 : ∀ x : Fin 6 → Bool, circN122.eval (List.ofFn x) = funcN122 x := by decide +kernel
theorem lowerN122 (s : ℕ) (h : HasCircuitSize 6 funcN122 s) : 11 ≤ s :=
  extension funcN122 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (14 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN122 (s : ℕ) : HasCircuitSize 6 funcN122 s ↔ 11 ≤ s :=
  ⟨lowerN122 s, fun h => ⟨circN122,(basisN122).2,h,evalN122⟩⟩
def circN123 : Circuit := ⟨[⟨.and, [0,4]⟩, ⟨.and, [1,2]⟩, ⟨.or, [0,4]⟩, ⟨.or, [1,2]⟩, ⟨.and, [8,5]⟩, ⟨.and, [10,9]⟩, ⟨.and, [3,11]⟩, ⟨.or, [3,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN123 := word 4276676736 3925917696
theorem basisN123 : Monotone2 circN123 ∧ FanInTwo circN123 := by simp [Monotone2,FanInTwo,circN123]
theorem evalN123 : ∀ x : Fin 6 → Bool, circN123.eval (List.ofFn x) = funcN123 x := by decide +kernel
theorem lowerN123 (s : ℕ) (h : HasCircuitSize 6 funcN123 s) : 11 ≤ s :=
  extension funcN123 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN123 (s : ℕ) : HasCircuitSize 6 funcN123 s ↔ 11 ≤ s :=
  ⟨lowerN123 s, fun h => ⟨circN123,(basisN123).2,h,evalN123⟩⟩
def circN124 : Circuit := ⟨[⟨.or, [0,4]⟩, ⟨.or, [1,2]⟩, ⟨.and, [0,4]⟩, ⟨.and, [1,2]⟩, ⟨.or, [8,9]⟩, ⟨.and, [10,5]⟩, ⟨.or, [3,11]⟩, ⟨.and, [3,11]⟩, ⟨.and, [6,12]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN124 := word 4276676736 4227901440
theorem basisN124 : Monotone2 circN124 ∧ FanInTwo circN124 := by simp [Monotone2,FanInTwo,circN124]
theorem evalN124 : ∀ x : Fin 6 → Bool, circN124.eval (List.ofFn x) = funcN124 x := by decide +kernel
theorem lowerN124 (s : ℕ) (h : HasCircuitSize 6 funcN124 s) : 11 ≤ s :=
  extension funcN124 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN124 (s : ℕ) : HasCircuitSize 6 funcN124 s ↔ 11 ≤ s :=
  ⟨lowerN124 s, fun h => ⟨circN124,(basisN124).2,h,evalN124⟩⟩
def circN125 : Circuit := ⟨[⟨.and, [0,4]⟩, ⟨.and, [1,3]⟩, ⟨.or, [0,4]⟩, ⟨.or, [1,3]⟩, ⟨.and, [8,9]⟩, ⟨.and, [2,5]⟩, ⟨.and, [11,10]⟩, ⟨.or, [2,10]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN125 := word 4276676736 4004038656
theorem basisN125 : Monotone2 circN125 ∧ FanInTwo circN125 := by simp [Monotone2,FanInTwo,circN125]
theorem evalN125 : ∀ x : Fin 6 → Bool, circN125.eval (List.ofFn x) = funcN125 x := by decide +kernel
theorem lowerN125 (s : ℕ) (h : HasCircuitSize 6 funcN125 s) : 11 ≤ s :=
  extension funcN125 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN125 (s : ℕ) : HasCircuitSize 6 funcN125 s ↔ 11 ≤ s :=
  ⟨lowerN125 s, fun h => ⟨circN125,(basisN125).2,h,evalN125⟩⟩
def circN126 : Circuit := ⟨[⟨.and, [0,4]⟩, ⟨.and, [1,3]⟩, ⟨.or, [0,4]⟩, ⟨.or, [1,3]⟩, ⟨.and, [8,9]⟩, ⟨.and, [2,10]⟩, ⟨.and, [2,5]⟩, ⟨.or, [12,10]⟩, ⟨.or, [6,11]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN126 := word 4276676736 4274563200
theorem basisN126 : Monotone2 circN126 ∧ FanInTwo circN126 := by simp [Monotone2,FanInTwo,circN126]
theorem evalN126 : ∀ x : Fin 6 → Bool, circN126.eval (List.ofFn x) = funcN126 x := by decide +kernel
theorem lowerN126 (s : ℕ) (h : HasCircuitSize 6 funcN126 s) : 11 ≤ s :=
  extension funcN126 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (14 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN126 (s : ℕ) : HasCircuitSize 6 funcN126 s ↔ 11 ≤ s :=
  ⟨lowerN126 s, fun h => ⟨circN126,(basisN126).2,h,evalN126⟩⟩
def circN127 : Circuit := ⟨[⟨.and, [0,4]⟩, ⟨.and, [1,3]⟩, ⟨.or, [0,4]⟩, ⟨.or, [1,3]⟩, ⟨.and, [8,5]⟩, ⟨.and, [10,9]⟩, ⟨.and, [2,11]⟩, ⟨.or, [2,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN127 := word 4276676736 3768631296
theorem basisN127 : Monotone2 circN127 ∧ FanInTwo circN127 := by simp [Monotone2,FanInTwo,circN127]
theorem evalN127 : ∀ x : Fin 6 → Bool, circN127.eval (List.ofFn x) = funcN127 x := by decide +kernel
theorem lowerN127 (s : ℕ) (h : HasCircuitSize 6 funcN127 s) : 11 ≤ s :=
  extension funcN127 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN127 (s : ℕ) : HasCircuitSize 6 funcN127 s ↔ 11 ≤ s :=
  ⟨lowerN127 s, fun h => ⟨circN127,(basisN127).2,h,evalN127⟩⟩
def circN128 : Circuit := ⟨[⟨.or, [0,4]⟩, ⟨.or, [1,3]⟩, ⟨.and, [0,4]⟩, ⟨.and, [1,3]⟩, ⟨.or, [8,9]⟩, ⟨.and, [10,5]⟩, ⟨.or, [2,11]⟩, ⟨.and, [2,11]⟩, ⟨.and, [6,12]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN128 := word 4276676736 4039155840
theorem basisN128 : Monotone2 circN128 ∧ FanInTwo circN128 := by simp [Monotone2,FanInTwo,circN128]
theorem evalN128 : ∀ x : Fin 6 → Bool, circN128.eval (List.ofFn x) = funcN128 x := by decide +kernel
theorem lowerN128 (s : ℕ) (h : HasCircuitSize 6 funcN128 s) : 11 ≤ s :=
  extension funcN128 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (11 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN128 (s : ℕ) : HasCircuitSize 6 funcN128 s ↔ 11 ≤ s :=
  ⟨lowerN128 s, fun h => ⟨circN128,(basisN128).2,h,evalN128⟩⟩
def circN129 : Circuit := ⟨[⟨.and, [0,4]⟩, ⟨.and, [2,3]⟩, ⟨.or, [0,4]⟩, ⟨.or, [2,3]⟩, ⟨.and, [8,9]⟩, ⟨.and, [1,5]⟩, ⟨.and, [11,10]⟩, ⟨.or, [1,10]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN129 := word 4276676736 4205371392
theorem basisN129 : Monotone2 circN129 ∧ FanInTwo circN129 := by simp [Monotone2,FanInTwo,circN129]
theorem evalN129 : ∀ x : Fin 6 → Bool, circN129.eval (List.ofFn x) = funcN129 x := by decide +kernel
theorem lowerN129 (s : ℕ) (h : HasCircuitSize 6 funcN129 s) : 11 ≤ s :=
  extension funcN129 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN129 (s : ℕ) : HasCircuitSize 6 funcN129 s ↔ 11 ≤ s :=
  ⟨lowerN129 s, fun h => ⟨circN129,(basisN129).2,h,evalN129⟩⟩
def circN130 : Circuit := ⟨[⟨.and, [0,4]⟩, ⟨.and, [2,3]⟩, ⟨.or, [0,4]⟩, ⟨.or, [2,3]⟩, ⟨.and, [8,9]⟩, ⟨.and, [1,10]⟩, ⟨.and, [1,5]⟩, ⟨.or, [12,10]⟩, ⟨.or, [6,11]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN130 := word 4276676736 4276136064
theorem basisN130 : Monotone2 circN130 ∧ FanInTwo circN130 := by simp [Monotone2,FanInTwo,circN130]
theorem evalN130 : ∀ x : Fin 6 → Bool, circN130.eval (List.ofFn x) = funcN130 x := by decide +kernel
theorem lowerN130 (s : ℕ) (h : HasCircuitSize 6 funcN130 s) : 11 ≤ s :=
  extension funcN130 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (14 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN130 (s : ℕ) : HasCircuitSize 6 funcN130 s ↔ 11 ≤ s :=
  ⟨lowerN130 s, fun h => ⟨circN130,(basisN130).2,h,evalN130⟩⟩
def circN131 : Circuit := ⟨[⟨.and, [0,4]⟩, ⟨.and, [2,3]⟩, ⟨.or, [0,4]⟩, ⟨.or, [2,3]⟩, ⟨.and, [8,5]⟩, ⟨.and, [10,9]⟩, ⟨.and, [1,11]⟩, ⟨.or, [1,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN131 := word 4276676736 3364405248
theorem basisN131 : Monotone2 circN131 ∧ FanInTwo circN131 := by simp [Monotone2,FanInTwo,circN131]
theorem evalN131 : ∀ x : Fin 6 → Bool, circN131.eval (List.ofFn x) = funcN131 x := by decide +kernel
theorem lowerN131 (s : ℕ) (h : HasCircuitSize 6 funcN131 s) : 11 ≤ s :=
  extension funcN131 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN131 (s : ℕ) : HasCircuitSize 6 funcN131 s ↔ 11 ≤ s :=
  ⟨lowerN131 s, fun h => ⟨circN131,(basisN131).2,h,evalN131⟩⟩
def circN132 : Circuit := ⟨[⟨.or, [0,4]⟩, ⟨.or, [2,3]⟩, ⟨.and, [0,4]⟩, ⟨.and, [2,3]⟩, ⟨.or, [8,9]⟩, ⟨.and, [10,5]⟩, ⟨.or, [1,11]⟩, ⟨.and, [1,11]⟩, ⟨.and, [6,12]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN132 := word 4276676736 3435169920
theorem basisN132 : Monotone2 circN132 ∧ FanInTwo circN132 := by simp [Monotone2,FanInTwo,circN132]
theorem evalN132 : ∀ x : Fin 6 → Bool, circN132.eval (List.ofFn x) = funcN132 x := by decide +kernel
theorem lowerN132 (s : ℕ) (h : HasCircuitSize 6 funcN132 s) : 11 ≤ s :=
  extension funcN132 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (13 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN132 (s : ℕ) : HasCircuitSize 6 funcN132 s ↔ 11 ≤ s :=
  ⟨lowerN132 s, fun h => ⟨circN132,(basisN132).2,h,evalN132⟩⟩
def circN133 : Circuit := ⟨[⟨.and, [1,2]⟩, ⟨.and, [0,3]⟩, ⟨.or, [1,2]⟩, ⟨.or, [0,3]⟩, ⟨.and, [8,9]⟩, ⟨.and, [4,10]⟩, ⟨.or, [4,10]⟩, ⟨.or, [6,11]⟩, ⟨.and, [13,5]⟩, ⟨.or, [7,14]⟩, ⟨.and, [12,15]⟩], 16⟩
def funcN133 := word 4276676736 2852169728
theorem basisN133 : Monotone2 circN133 ∧ FanInTwo circN133 := by simp [Monotone2,FanInTwo,circN133]
theorem evalN133 : ∀ x : Fin 6 → Bool, circN133.eval (List.ofFn x) = funcN133 x := by decide +kernel
theorem lowerN133 (s : ℕ) (h : HasCircuitSize 6 funcN133 s) : 11 ≤ s :=
  extension funcN133 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN133 (s : ℕ) : HasCircuitSize 6 funcN133 s ↔ 11 ≤ s :=
  ⟨lowerN133 s, fun h => ⟨circN133,(basisN133).2,h,evalN133⟩⟩
def circN134 : Circuit := ⟨[⟨.and, [1,2]⟩, ⟨.and, [0,4]⟩, ⟨.or, [1,2]⟩, ⟨.or, [0,4]⟩, ⟨.and, [8,9]⟩, ⟨.and, [3,10]⟩, ⟨.or, [3,10]⟩, ⟨.or, [6,11]⟩, ⟨.and, [13,5]⟩, ⟨.or, [7,14]⟩, ⟨.and, [12,15]⟩], 16⟩
def funcN134 := word 4276676736 2863136768
theorem basisN134 : Monotone2 circN134 ∧ FanInTwo circN134 := by simp [Monotone2,FanInTwo,circN134]
theorem evalN134 : ∀ x : Fin 6 → Bool, circN134.eval (List.ofFn x) = funcN134 x := by decide +kernel
theorem lowerN134 (s : ℕ) (h : HasCircuitSize 6 funcN134 s) : 11 ≤ s :=
  extension funcN134 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN134 (s : ℕ) : HasCircuitSize 6 funcN134 s ↔ 11 ≤ s :=
  ⟨lowerN134 s, fun h => ⟨circN134,(basisN134).2,h,evalN134⟩⟩
def circN135 : Circuit := ⟨[⟨.and, [1,2]⟩, ⟨.and, [3,4]⟩, ⟨.or, [1,2]⟩, ⟨.or, [3,4]⟩, ⟨.and, [8,9]⟩, ⟨.and, [0,5]⟩, ⟨.and, [11,10]⟩, ⟨.or, [0,10]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN135 := word 4276676736 4274045056
theorem basisN135 : Monotone2 circN135 ∧ FanInTwo circN135 := by simp [Monotone2,FanInTwo,circN135]
theorem evalN135 : ∀ x : Fin 6 → Bool, circN135.eval (List.ofFn x) = funcN135 x := by decide +kernel
theorem lowerN135 (s : ℕ) (h : HasCircuitSize 6 funcN135 s) : 11 ≤ s :=
  extension funcN135 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (11 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN135 (s : ℕ) : HasCircuitSize 6 funcN135 s ↔ 11 ≤ s :=
  ⟨lowerN135 s, fun h => ⟨circN135,(basisN135).2,h,evalN135⟩⟩
def circN136 : Circuit := ⟨[⟨.and, [1,2]⟩, ⟨.and, [3,4]⟩, ⟨.or, [1,2]⟩, ⟨.or, [3,4]⟩, ⟨.and, [8,9]⟩, ⟨.and, [0,10]⟩, ⟨.and, [0,5]⟩, ⟨.or, [12,10]⟩, ⟨.or, [6,11]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN136 := word 4276676736 4243122176
theorem basisN136 : Monotone2 circN136 ∧ FanInTwo circN136 := by simp [Monotone2,FanInTwo,circN136]
theorem evalN136 : ∀ x : Fin 6 → Bool, circN136.eval (List.ofFn x) = funcN136 x := by decide +kernel
theorem lowerN136 (s : ℕ) (h : HasCircuitSize 6 funcN136 s) : 11 ≤ s :=
  extension funcN136 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN136 (s : ℕ) : HasCircuitSize 6 funcN136 s ↔ 11 ≤ s :=
  ⟨lowerN136 s, fun h => ⟨circN136,(basisN136).2,h,evalN136⟩⟩
def circN137 : Circuit := ⟨[⟨.and, [1,2]⟩, ⟨.and, [3,4]⟩, ⟨.or, [1,2]⟩, ⟨.or, [3,4]⟩, ⟨.and, [8,5]⟩, ⟨.and, [10,9]⟩, ⟨.and, [0,11]⟩, ⟨.or, [0,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN137 := word 4276676736 2860548224
theorem basisN137 : Monotone2 circN137 ∧ FanInTwo circN137 := by simp [Monotone2,FanInTwo,circN137]
theorem evalN137 : ∀ x : Fin 6 → Bool, circN137.eval (List.ofFn x) = funcN137 x := by decide +kernel
theorem lowerN137 (s : ℕ) (h : HasCircuitSize 6 funcN137 s) : 11 ≤ s :=
  extension funcN137 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (11 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN137 (s : ℕ) : HasCircuitSize 6 funcN137 s ↔ 11 ≤ s :=
  ⟨lowerN137 s, fun h => ⟨circN137,(basisN137).2,h,evalN137⟩⟩
def circN138 : Circuit := ⟨[⟨.and, [1,2]⟩, ⟨.and, [3,4]⟩, ⟨.or, [1,2]⟩, ⟨.or, [3,4]⟩, ⟨.and, [8,9]⟩, ⟨.and, [0,10]⟩, ⟨.and, [10,5]⟩, ⟨.or, [0,12]⟩, ⟨.or, [6,11]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN138 := word 4276676736 2863179904
theorem basisN138 : Monotone2 circN138 ∧ FanInTwo circN138 := by simp [Monotone2,FanInTwo,circN138]
theorem evalN138 : ∀ x : Fin 6 → Bool, circN138.eval (List.ofFn x) = funcN138 x := by decide +kernel
theorem lowerN138 (s : ℕ) (h : HasCircuitSize 6 funcN138 s) : 11 ≤ s :=
  extension funcN138 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (14 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN138 (s : ℕ) : HasCircuitSize 6 funcN138 s ↔ 11 ≤ s :=
  ⟨lowerN138 s, fun h => ⟨circN138,(basisN138).2,h,evalN138⟩⟩
def circN139 : Circuit := ⟨[⟨.or, [1,2]⟩, ⟨.or, [3,4]⟩, ⟨.and, [1,2]⟩, ⟨.and, [3,4]⟩, ⟨.or, [8,9]⟩, ⟨.and, [10,5]⟩, ⟨.or, [0,11]⟩, ⟨.and, [0,11]⟩, ⟨.and, [6,12]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN139 := word 4276676736 2829625344
theorem basisN139 : Monotone2 circN139 ∧ FanInTwo circN139 := by simp [Monotone2,FanInTwo,circN139]
theorem evalN139 : ∀ x : Fin 6 → Bool, circN139.eval (List.ofFn x) = funcN139 x := by decide +kernel
theorem lowerN139 (s : ℕ) (h : HasCircuitSize 6 funcN139 s) : 11 ≤ s :=
  extension funcN139 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN139 (s : ℕ) : HasCircuitSize 6 funcN139 s ↔ 11 ≤ s :=
  ⟨lowerN139 s, fun h => ⟨circN139,(basisN139).2,h,evalN139⟩⟩
def circN140 : Circuit := ⟨[⟨.and, [1,3]⟩, ⟨.and, [0,2]⟩, ⟨.or, [1,3]⟩, ⟨.or, [0,2]⟩, ⟨.and, [8,9]⟩, ⟨.and, [4,10]⟩, ⟨.or, [4,10]⟩, ⟨.or, [6,11]⟩, ⟨.and, [13,5]⟩, ⟨.or, [7,14]⟩, ⟨.and, [12,15]⟩], 16⟩
def funcN140 := word 4276676736 2694881408
theorem basisN140 : Monotone2 circN140 ∧ FanInTwo circN140 := by simp [Monotone2,FanInTwo,circN140]
theorem evalN140 : ∀ x : Fin 6 → Bool, circN140.eval (List.ofFn x) = funcN140 x := by decide +kernel
theorem lowerN140 (s : ℕ) (h : HasCircuitSize 6 funcN140 s) : 11 ≤ s :=
  extension funcN140 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (11 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN140 (s : ℕ) : HasCircuitSize 6 funcN140 s ↔ 11 ≤ s :=
  ⟨lowerN140 s, fun h => ⟨circN140,(basisN140).2,h,evalN140⟩⟩
def circN141 : Circuit := ⟨[⟨.and, [1,3]⟩, ⟨.and, [2,4]⟩, ⟨.or, [1,3]⟩, ⟨.or, [2,4]⟩, ⟨.and, [8,9]⟩, ⟨.and, [0,5]⟩, ⟨.and, [11,10]⟩, ⟨.or, [0,10]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN141 := word 4276676736 4242589696
theorem basisN141 : Monotone2 circN141 ∧ FanInTwo circN141 := by simp [Monotone2,FanInTwo,circN141]
theorem evalN141 : ∀ x : Fin 6 → Bool, circN141.eval (List.ofFn x) = funcN141 x := by decide +kernel
theorem lowerN141 (s : ℕ) (h : HasCircuitSize 6 funcN141 s) : 11 ≤ s :=
  extension funcN141 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN141 (s : ℕ) : HasCircuitSize 6 funcN141 s ↔ 11 ≤ s :=
  ⟨lowerN141 s, fun h => ⟨circN141,(basisN141).2,h,evalN141⟩⟩
def circN142 : Circuit := ⟨[⟨.and, [1,3]⟩, ⟨.and, [2,4]⟩, ⟨.or, [1,3]⟩, ⟨.or, [2,4]⟩, ⟨.and, [8,9]⟩, ⟨.and, [0,10]⟩, ⟨.and, [0,5]⟩, ⟨.or, [12,10]⟩, ⟨.or, [6,11]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN142 := word 4276676736 4274577536
theorem basisN142 : Monotone2 circN142 ∧ FanInTwo circN142 := by simp [Monotone2,FanInTwo,circN142]
theorem evalN142 : ∀ x : Fin 6 → Bool, circN142.eval (List.ofFn x) = funcN142 x := by decide +kernel
theorem lowerN142 (s : ℕ) (h : HasCircuitSize 6 funcN142 s) : 11 ≤ s :=
  extension funcN142 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (11 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN142 (s : ℕ) : HasCircuitSize 6 funcN142 s ↔ 11 ≤ s :=
  ⟨lowerN142 s, fun h => ⟨circN142,(basisN142).2,h,evalN142⟩⟩
def circN143 : Circuit := ⟨[⟨.and, [1,3]⟩, ⟨.and, [2,4]⟩, ⟨.or, [1,3]⟩, ⟨.or, [2,4]⟩, ⟨.and, [8,5]⟩, ⟨.and, [10,9]⟩, ⟨.and, [0,11]⟩, ⟨.or, [0,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN143 := word 4276676736 2829092864
theorem basisN143 : Monotone2 circN143 ∧ FanInTwo circN143 := by simp [Monotone2,FanInTwo,circN143]
theorem evalN143 : ∀ x : Fin 6 → Bool, circN143.eval (List.ofFn x) = funcN143 x := by decide +kernel
theorem lowerN143 (s : ℕ) (h : HasCircuitSize 6 funcN143 s) : 11 ≤ s :=
  extension funcN143 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN143 (s : ℕ) : HasCircuitSize 6 funcN143 s ↔ 11 ≤ s :=
  ⟨lowerN143 s, fun h => ⟨circN143,(basisN143).2,h,evalN143⟩⟩
def circN144 : Circuit := ⟨[⟨.or, [1,3]⟩, ⟨.or, [2,4]⟩, ⟨.and, [1,3]⟩, ⟨.and, [2,4]⟩, ⟨.or, [8,9]⟩, ⟨.and, [10,5]⟩, ⟨.or, [0,11]⟩, ⟨.and, [0,11]⟩, ⟨.and, [6,12]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN144 := word 4276676736 2861080704
theorem basisN144 : Monotone2 circN144 ∧ FanInTwo circN144 := by simp [Monotone2,FanInTwo,circN144]
theorem evalN144 : ∀ x : Fin 6 → Bool, circN144.eval (List.ofFn x) = funcN144 x := by decide +kernel
theorem lowerN144 (s : ℕ) (h : HasCircuitSize 6 funcN144 s) : 11 ≤ s :=
  extension funcN144 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (11 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN144 (s : ℕ) : HasCircuitSize 6 funcN144 s ↔ 11 ≤ s :=
  ⟨lowerN144 s, fun h => ⟨circN144,(basisN144).2,h,evalN144⟩⟩
def circN145 : Circuit := ⟨[⟨.and, [1,4]⟩, ⟨.and, [2,3]⟩, ⟨.or, [1,4]⟩, ⟨.or, [2,3]⟩, ⟨.and, [8,9]⟩, ⟨.and, [0,5]⟩, ⟨.and, [11,10]⟩, ⟨.or, [0,10]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN145 := word 4276676736 4241022976
theorem basisN145 : Monotone2 circN145 ∧ FanInTwo circN145 := by simp [Monotone2,FanInTwo,circN145]
theorem evalN145 : ∀ x : Fin 6 → Bool, circN145.eval (List.ofFn x) = funcN145 x := by decide +kernel
theorem lowerN145 (s : ℕ) (h : HasCircuitSize 6 funcN145 s) : 11 ≤ s :=
  extension funcN145 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN145 (s : ℕ) : HasCircuitSize 6 funcN145 s ↔ 11 ≤ s :=
  ⟨lowerN145 s, fun h => ⟨circN145,(basisN145).2,h,evalN145⟩⟩
def circN146 : Circuit := ⟨[⟨.and, [1,4]⟩, ⟨.and, [2,3]⟩, ⟨.or, [1,4]⟩, ⟨.or, [2,3]⟩, ⟨.and, [8,9]⟩, ⟨.and, [0,10]⟩, ⟨.and, [0,5]⟩, ⟨.or, [12,10]⟩, ⟨.or, [6,11]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN146 := word 4276676736 4276144256
theorem basisN146 : Monotone2 circN146 ∧ FanInTwo circN146 := by simp [Monotone2,FanInTwo,circN146]
theorem evalN146 : ∀ x : Fin 6 → Bool, circN146.eval (List.ofFn x) = funcN146 x := by decide +kernel
theorem lowerN146 (s : ℕ) (h : HasCircuitSize 6 funcN146 s) : 11 ≤ s :=
  extension funcN146 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (13 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN146 (s : ℕ) : HasCircuitSize 6 funcN146 s ↔ 11 ≤ s :=
  ⟨lowerN146 s, fun h => ⟨circN146,(basisN146).2,h,evalN146⟩⟩
def circN147 : Circuit := ⟨[⟨.and, [1,4]⟩, ⟨.and, [2,3]⟩, ⟨.or, [1,4]⟩, ⟨.or, [2,3]⟩, ⟨.and, [8,5]⟩, ⟨.and, [10,9]⟩, ⟨.and, [0,11]⟩, ⟨.or, [0,11]⟩, ⟨.or, [6,12]⟩, ⟨.or, [7,14]⟩, ⟨.and, [13,15]⟩], 16⟩
def funcN147 := word 4276676736 2827526144
theorem basisN147 : Monotone2 circN147 ∧ FanInTwo circN147 := by simp [Monotone2,FanInTwo,circN147]
theorem evalN147 : ∀ x : Fin 6 → Bool, circN147.eval (List.ofFn x) = funcN147 x := by decide +kernel
theorem lowerN147 (s : ℕ) (h : HasCircuitSize 6 funcN147 s) : 11 ≤ s :=
  extension funcN147 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (7 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN147 (s : ℕ) : HasCircuitSize 6 funcN147 s ↔ 11 ≤ s :=
  ⟨lowerN147 s, fun h => ⟨circN147,(basisN147).2,h,evalN147⟩⟩
def circN148 : Circuit := ⟨[⟨.or, [1,4]⟩, ⟨.or, [2,3]⟩, ⟨.and, [1,4]⟩, ⟨.and, [2,3]⟩, ⟨.or, [8,9]⟩, ⟨.and, [10,5]⟩, ⟨.or, [0,11]⟩, ⟨.and, [0,11]⟩, ⟨.and, [6,12]⟩, ⟨.and, [7,14]⟩, ⟨.or, [13,15]⟩], 16⟩
def funcN148 := word 4276676736 2862647424
theorem basisN148 : Monotone2 circN148 ∧ FanInTwo circN148 := by simp [Monotone2,FanInTwo,circN148]
theorem evalN148 : ∀ x : Fin 6 → Bool, circN148.eval (List.ofFn x) = funcN148 x := by decide +kernel
theorem lowerN148 (s : ℕ) (h : HasCircuitSize 6 funcN148 s) : 11 ≤ s :=
  extension funcN148 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (13 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN148 (s : ℕ) : HasCircuitSize 6 funcN148 s ↔ 11 ≤ s :=
  ⟨lowerN148 s, fun h => ⟨circN148,(basisN148).2,h,evalN148⟩⟩
def circN149 : Circuit := ⟨[⟨.and, [2,3]⟩, ⟨.and, [0,1]⟩, ⟨.or, [2,3]⟩, ⟨.or, [0,1]⟩, ⟨.and, [8,9]⟩, ⟨.and, [4,10]⟩, ⟨.or, [4,10]⟩, ⟨.or, [6,11]⟩, ⟨.and, [13,5]⟩, ⟨.or, [7,14]⟩, ⟨.and, [12,15]⟩], 16⟩
def funcN149 := word 4276676736 2290649216
theorem basisN149 : Monotone2 circN149 ∧ FanInTwo circN149 := by simp [Monotone2,FanInTwo,circN149]
theorem evalN149 : ∀ x : Fin 6 → Bool, circN149.eval (List.ofFn x) = funcN149 x := by decide +kernel
theorem lowerN149 (s : ℕ) (h : HasCircuitSize 6 funcN149 s) : 11 ≤ s :=
  extension funcN149 5 true (by decide +kernel)
    ⟨(fun j : Fin 6 => (13 : ℕ).testBit j.val),by decide +kernel⟩ s h
theorem exactN149 (s : ℕ) : HasCircuitSize 6 funcN149 s ↔ 11 ≤ s :=
  ⟨lowerN149 s, fun h => ⟨circN149,(basisN149).2,h,evalN149⟩⟩
end Simlowker.Cofactors12119.Family

namespace Simlowker.Cofactors12119.Family
open PEqualNP.MetaComplexity
def words0 : List Nat := [4276150272, 4241016960, 4240490496, 4205357184, 4204830720, 4008216704, 4270385152, 4001925120, 4176011392, 3907551360, 4169721984]
theorem lowerUpper0 (v s : Nat) (hv : v ∈ words0) : HasCircuitSize 6 (word 4276676736 v) s ↔ 11 ≤ s := by
  simp only [words0,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact exactN48 s
  · exact exactN49 s
  · exact exactN50 s
  · exact exactN51 s
  · exact exactN52 s
  · exact exactN53 s
  · exact exactN54 s
  · exact exactN55 s
  · exact exactN56 s
  · exact exactN2 s
  · exact exactN57 s
def words1 : List Nat := [4007716992, 3900762240, 4169662464, 4276617216, 0, 4026589184, 4007657472, 4001949824, 4276652032, 4175489152, 4175988864]
theorem lowerUpper1 (v s : Nat) (hv : v ∈ words1) : HasCircuitSize 6 (word 4276676736 v) s ↔ 11 ≤ s := by
  simp only [words1,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact exactN58 s
  · exact exact12292 s
  · exact exactN59 s
  · exact exactN10 s
  · exact exactN16 s
  · exact exactN60 s
  · exact exactN61 s
  · exact exactN62 s
  · exact exactN63 s
  · exact exactN64 s
  · exact exactN65 s
def words2 : List Nat := [4008239232, 4160784384, 4261472256, 4041211904, 3993034752, 3907577984, 4276650112, 4269860992, 4270360704, 4008241152, 4034953344]
theorem lowerUpper2 (v s : Nat) (hv : v ∈ words2) : HasCircuitSize 6 (word 4276676736 v) s ↔ 11 ≤ s := by
  simp only [words2,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact exactN66 s
  · exact exactN67 s
  · exact exact12124 s
  · exact exactN68 s
  · exact exactN69 s
  · exact exact12294 s
  · exact exactN34 s
  · exact exact12298 s
  · exact exactN70 s
  · exact exactN71 s
  · exact exactN72 s
def words3 : List Nat := [4041269376, 4261412864, 3772833792, 4274571264, 4242595968, 4004030592, 4209549440, 4271958016, 3974678656, 3969968256, 4207470720]
theorem lowerUpper3 (v s : Nat) (hv : v ∈ words3) : HasCircuitSize 6 (word 4276676736 v) s ↔ 11 ≤ s := by
  simp only [words3,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact exactN73 s
  · exact exact12120 s
  · exact exactN74 s
  · exact exactN75 s
  · exact exactN76 s
  · exact exactN77 s
  · exact exactN78 s
  · exact exactN79 s
  · exact exactN80 s
  · exact exactN81 s
  · exact exactN82 s
def words4 : List Nat := [3969908736, 3422603264, 4207411200, 4204849280, 4276658176, 3972589696, 3974668416, 4209559680, 3959463936, 3435659264, 4194355200]
theorem lowerUpper4 (v s : Nat) (hv : v ∈ words4) : HasCircuitSize 6 (word 4276676736 v) s ↔ 11 ≤ s := by
  simp only [words4,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact exactN83 s
  · exact exactN84 s
  · exact exactN85 s
  · exact exactN86 s
  · exact exactN87 s
  · exact exactN88 s
  · exact exactN89 s
  · exact exactN90 s
  · exact exactN91 s
  · exact exactN92 s
  · exact exactN93 s
def words5 : List Nat := [4271939712, 4209567744, 3430973568, 3435710592, 3368601600, 4243112064, 4274055168, 3941116032, 4272465920, 4209041536, 4006135936]
theorem lowerUpper5 (v s : Nat) (hv : v ∈ words5) : HasCircuitSize 6 (word 4276676736 v) s ↔ 11 ≤ s := by
  simp only [words5,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact exactN94 s
  · exact exactN95 s
  · exact exactN96 s
  · exact exactN97 s
  · exact exactN98 s
  · exact exactN99 s
  · exact exactN100 s
  · exact exactN101 s
  · exact exactN102 s
  · exact exactN103 s
  · exact exactN104 s
def words6 : List Nat := [3938510976, 4238928000, 3938451456, 3233857664, 4238868480, 4006127616, 4272474240, 3770720256, 4037066880, 4209027072, 4272480384]
theorem lowerUpper6 (v s : Nat) (hv : v ∈ words6) : HasCircuitSize 6 (word 4276676736 v) s ↔ 11 ≤ s := by
  simp only [words6,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact exactN105 s
  · exact exactN106 s
  · exact exactN107 s
  · exact exactN108 s
  · exact exactN109 s
  · exact exactN110 s
  · exact exactN111 s
  · exact exactN112 s
  · exact exactN113 s
  · exact exactN114 s
  · exact exactN115 s
def words7 : List Nat := [3368060928, 3431514240, 4240500864, 4276666368, 3936938112, 3941122176, 4243105920, 3925917696, 4227901440, 4004038656, 4274563200]
theorem lowerUpper7 (v s : Nat) (hv : v ∈ words7) : HasCircuitSize 6 (word 4276676736 v) s ↔ 11 ≤ s := by
  simp only [words7,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact exactN116 s
  · exact exactN117 s
  · exact exactN118 s
  · exact exactN119 s
  · exact exactN120 s
  · exact exactN121 s
  · exact exactN122 s
  · exact exactN123 s
  · exact exactN124 s
  · exact exactN125 s
  · exact exactN126 s
def words8 : List Nat := [3768631296, 4039155840, 4205371392, 4276136064, 3364405248, 3435169920, 2852169728, 2863136768, 4274045056, 4243122176, 2860548224]
theorem lowerUpper8 (v s : Nat) (hv : v ∈ words8) : HasCircuitSize 6 (word 4276676736 v) s ↔ 11 ≤ s := by
  simp only [words8,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact exactN127 s
  · exact exactN128 s
  · exact exactN129 s
  · exact exactN130 s
  · exact exactN131 s
  · exact exactN132 s
  · exact exactN133 s
  · exact exactN134 s
  · exact exactN135 s
  · exact exactN136 s
  · exact exactN137 s
def words9 : List Nat := [2863179904, 2829625344, 2694881408, 4242589696, 4274577536, 2829092864, 2861080704, 4241022976, 4276144256, 2827526144, 2862647424]
theorem lowerUpper9 (v s : Nat) (hv : v ∈ words9) : HasCircuitSize 6 (word 4276676736 v) s ↔ 11 ≤ s := by
  simp only [words9,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact exactN138 s
  · exact exactN139 s
  · exact exactN140 s
  · exact exactN141 s
  · exact exactN142 s
  · exact exactN143 s
  · exact exactN144 s
  · exact exactN145 s
  · exact exactN146 s
  · exact exactN147 s
  · exact exactN148 s
def words10 : List Nat := [2290649216]
theorem lowerUpper10 (v s : Nat) (hv : v ∈ words10) : HasCircuitSize 6 (word 4276676736 v) s ↔ 11 ≤ s := by
  have eq : v = 2290649216 := List.mem_singleton.mp hv
  rw [eq]
  exact exactN149 s
def lowWords := words0 ++ (words1 ++ (words2 ++ (words3 ++ (words4 ++ (words5 ++ (words6 ++ (words7 ++ (words8 ++ (words9 ++ (words10))))))))))
theorem distinct_tables : lowWords.length = 111 ∧ lowWords.Nodup := by decide +kernel
theorem all_exact (v s : Nat) (h : v ∈ lowWords) : HasCircuitSize 6 (word 4276676736 v) s ↔ 11 ≤ s := by
  simp only [lowWords,List.mem_append] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · exact lowerUpper0 v s h
  · exact lowerUpper1 v s h
  · exact lowerUpper2 v s h
  · exact lowerUpper3 v s h
  · exact lowerUpper4 v s h
  · exact lowerUpper5 v s h
  · exact lowerUpper6 v s h
  · exact lowerUpper7 v s h
  · exact lowerUpper8 v s h
  · exact lowerUpper9 v s h
  · exact lowerUpper10 v s h
end Simlowker.Cofactors12119.Family
