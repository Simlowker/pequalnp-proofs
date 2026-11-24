import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace L171Prefix


def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi


theorem foldl_step_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl step w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton, foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_step_length, Nat.min_eq_left ht.le]

theorem foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl step w).length) :
    (G.foldl step w).getD i false = ((G.take t).foldl step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact foldl_step_getD _ _ _ hi


theorem gate_value (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i =>
        if i < w.length + t then (G.foldl step w).getD i false else false) := by
  rw [foldl_step_getD_gate G w t ht]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : ((G.take t).foldl step w).length = w.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  split_ifs with h
  · exact (foldl_take_getD G w t i (by rw [hlen]; exact h)).symm
  · exact getD_of_length_le _ _ (by rw [hlen]; omega)

end L171Prefix
end PEqualNP.Outside
namespace PetersenDrops
abbrev Row := Finset Nat
abbrev Signal := Row → Bool
abbrev Pool := Signal → Prop
def bit (i : Nat) : Signal := fun x => decide (i∈x)
def con (b : Bool) : Signal := fun _ => b
def flip (a : Signal) : Signal := fun x => !a x
def both (a b : Signal) : Signal := fun x => a x && b x
def either (a b : Signal) : Signal := fun x => a x || b x
def start (S : Finset Nat) : Pool := fun y => y=con false ∨ y=con true ∨ ∃ i∈S,y=bit i
def add (p : Pool) (a : Signal) : Pool := fun y => y=a ∨ p y
def next (p : Pool) (y : Signal) : Prop :=
  (∃ a, p a ∧ y=flip a) ∨ ∃ a, p a ∧ ∃ b, p b ∧ (y=both a b ∨ y=either a b)
def run : Nat → Pool → Signal → Prop
  | 0,p,f => p f
  | k+1,p,f => ∃ y, next p y ∧ run k (add p y) f

def sub (ρ : Row → Row) (f : Signal) : Signal := fun r => f (ρ r)
theorem lift_step {p q y} {ρ : Row → Row} (h : ∀ g,p g → q (sub ρ g)) (st : next p y) : next q (sub ρ y) := by
  rcases st with ⟨a,ha,rfl⟩|⟨a,ha,b,hb,op|op⟩
  · exact Or.inl ⟨_,h a ha,rfl⟩
  · exact Or.inr ⟨_,h a ha,_,h b hb,Or.inl (op ▸ rfl)⟩
  · exact Or.inr ⟨_,h a ha,_,h b hb,Or.inr (op ▸ rfl)⟩

theorem lift_run {ρ : Row → Row} {p q f k} (h : ∀ g,p g → q (sub ρ g)) (rs : run k p f) :
    run k q (sub ρ f) := by
  induction k generalizing p q with
  | zero => exact h f rs
  | succ k ih =>
    obtain ⟨y,st,rest⟩ := rs
    refine ⟨_,lift_step h st,ih ?_ rest⟩
    intro z hz
    rcases hz with rfl|old
    · exact Or.inl rfl
    · exact Or.inr (h _ old)

def image (ρ : Row → Row) (p : Pool) : Pool := fun g => ∃ s,p s ∧ g=sub ρ s

theorem weaken {p q f k} (h : ∀ g,p g → q g) (rs : run k p f) : run k q f :=
  lift_run (ρ:=id) h rs

theorem eliminate {I : Type} (ρ : I → Row → Row) (P : Signal → Prop)
    (p : Pool) (f : Signal) (k : Nat)
    (good : ∀ x,p x → P x) (bad : ¬P f) (rs : run k p f)
    (const : ∀ b,p (con b))
    (collapse : ∀ q : Pool, (∀ x,q x → P x) → (∀ b,q (con b)) → ∀ y, next q y → ¬P y →
        ∃ i, image (ρ i) q (sub (ρ i) y)) :
    ∃ i m, m+1=k ∧ run m (image (ρ i) p) (sub (ρ i) f) := by
  classical
  induction k generalizing p with
  | zero => exact (bad (good f rs)).elim
  | succ k ih =>
    obtain ⟨y,st,rest⟩ := rs
    by_cases ok : P y
    · obtain ⟨i,m,len,rr⟩ := ih (add p y) (fun x hx => by rcases hx with rfl|old;exact ok;exact good x old)
        rest (fun b => Or.inr (const b))
      refine ⟨i,m+1,by omega,sub (ρ i) y,lift_step (fun x hx => ⟨x,hx,rfl⟩) st,?_⟩
      apply weaken _ rr
      rintro z ⟨a,ha,e⟩
      rcases ha with rfl|old
      · exact Or.inl e
      · exact Or.inr ⟨a,old,e⟩
    · obtain ⟨i,hit⟩ := collapse p good const y st ok
      refine ⟨i,k,rfl,lift_run (ρ:=ρ i) ?_ rest⟩
      intro z hz
      rcases hz with rfl|old
      · exact hit
      · exact ⟨z,old,rfl⟩
end PetersenDrops
namespace PetersenDrops

def kill (z : Nat) (r : Row) := r.erase z
def stable (z : Nat) (a : Signal) := ∀ r, a r=a (kill z r)

theorem zero_step (z : Nat) (p : Pool) (gs : ∀ x,p x → stable z x ∨ x=bit z) (cs : ∀ b,p (con b))
    {y} (st : next p y) (bad : ¬(stable z y ∨ y=bit z)) : image (kill z) p (sub (kill z) y) := by
  have here (r : Row) : bit z (kill z r)=false := by simp [bit,kill]
  rcases st with ⟨a,ha,rfl⟩|⟨a,ha,b,hb,op⟩
  · rcases gs a ha with stab|rfl
    · exact (bad (Or.inl (fun r => congrArg Bool.not (stab r)))).elim
    · exact ⟨con true,cs _,by funext r;simp [sub,flip,con,here]⟩
  · rcases gs a ha with sa|rfl <;> rcases gs b hb with sb|rfl
    · rcases op with rfl|rfl
      · exact (bad (Or.inl (fun r => congrArg₂ Bool.and (sa r) (sb r)))).elim
      · exact (bad (Or.inl (fun r => congrArg₂ Bool.or (sa r) (sb r)))).elim
    · rcases op with rfl|rfl
      · exact ⟨con false,cs _,by funext r;simp [sub,both,con,here]⟩
      · exact ⟨a,ha,by funext r;simp [sub,either,here]⟩
    · rcases op with rfl|rfl
      · exact ⟨con false,cs _,by funext r;simp [sub,both,con,here]⟩
      · exact ⟨b,hb,by funext r;simp [sub,either,here]⟩
    · rcases op with rfl|rfl
      · exact ⟨con false,cs _,by funext r;simp [sub,both,con,here]⟩
      · exact ⟨con false,cs _,by funext r;simp [sub,either,con,here]⟩

theorem at_start {S : Finset Nat} {z : Nat} {f} (h : start S f) : stable z f ∨ f=bit z := by
  rcases h with rfl|rfl|⟨i,_,rfl⟩
  · exact Or.inl (fun _ => rfl)
  · exact Or.inl (fun _ => rfl)
  · by_cases e : i=z
    · exact Or.inr (e ▸ rfl)
    · left;intro r;simp [bit,kill,e]

theorem after_zero {S : Finset Nat} {z : Nat} {g} (h : image (kill z) (start S) g) : start (S.erase z) g := by
  obtain ⟨a,ha,rfl⟩ := h
  rcases ha with rfl|rfl|⟨i,hi,rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · by_cases e : i=z
    · subst i;left;funext r;simp [sub,bit,con,kill]
    · right;right;refine ⟨i,Finset.mem_erase.mpr ⟨e,hi⟩,?_⟩
      funext r;simp [sub,bit,kill,e]

theorem drop_zero {S : Finset Nat} {z f k} (rs : run k (start S) f)
    (empty : f ∅=true) (negative : f {z}=false) :
    ∃ m, m+1=k ∧ run m (start (S.erase z)) (sub (kill z) f) := by
  have bad : ¬(stable z f ∨ f=bit z) := by
    rintro (h|rfl)
    · have e := h {z};simp [kill,empty,negative] at e
    · simp [bit] at empty
  obtain ⟨_,m,len,out⟩ := eliminate (I:=Unit) (fun _ => kill z) (fun g => stable z g ∨ g=bit z)
    (start S) f k (fun _ h => at_start h) bad rs
    (fun b => by cases b;exact Or.inl rfl;exact Or.inr (Or.inl rfl))
    (fun p g c _ s b => ⟨(),zero_step z p g c s b⟩)
  exact ⟨m,len,weaken (fun _ h => after_zero h) out⟩
end PetersenDrops
namespace PetersenDrops

def merge (i j : Nat) (r : Row) := if j∈r then insert i (r.erase i) else r.erase i
theorem bit_merge (i j v : Nat) (r : Row) : bit v (merge i j r)=(if v=i then bit j r else bit v r) := by
  by_cases jr : j∈r <;> by_cases e : v=i <;> simp [bit,merge,jr,e]

def unary (S : Row) (a : Signal) : Prop := ∃ i∈S, ∃ u : Bool → Bool, a=fun r => u (bit i r)
theorem unary_start {S : Row} (non : S.Nonempty) {a} (h : start S a) : unary S a := by
  obtain ⟨i,hi⟩ := non
  rcases h with rfl|rfl|⟨j,hj,rfl⟩
  · exact ⟨i,hi,fun _ => false,rfl⟩
  · exact ⟨i,hi,fun _ => true,rfl⟩
  · exact ⟨j,hj,id,rfl⟩

def gateOp (t : Bool) (x y : Bool) := if t then x && y else x || y
theorem unary_meet_join : ∀ (u v : Bool → Bool) (t : Bool),
    (∀ b,gateOp t (u b) (v b)=false) ∨ (∀ b,gateOp t (u b) (v b)=true) ∨
    (∀ b,gateOp t (u b) (v b)=u b) ∨ (∀ b,gateOp t (u b) (v b)=v b) := by decide +kernel

abbrev Pair (S : Row) := {p : Nat × Nat // p.1∈S ∧ p.2∈S ∧ p.1≠p.2}

theorem merge_step {S : Row} (p : Pool) (gs : ∀ x,p x → unary S x) (cs : ∀ b,p (con b))
    {y} (st : next p y) (bad : ¬unary S y) :
    ∃ d : Pair S, image (merge d.val.1 d.val.2) p (sub (merge d.val.1 d.val.2) y) := by
  rcases st with ⟨a,ha,rfl⟩|⟨a,ha,b,hb,op⟩
  · obtain ⟨i,hi,u,rfl⟩ := gs a ha
    exact (bad ⟨i,hi,fun x => !u x,rfl⟩).elim
  · obtain ⟨i,hi,u,rfl⟩ := gs a ha
    obtain ⟨j,hj,v,rfl⟩ := gs b hb
    obtain ⟨t,desc⟩ : ∃ t : Bool,y=fun r => gateOp t (u (bit i r)) (v (bit j r)) := by
      rcases op with e|e
      · exact ⟨true,e⟩
      · exact ⟨false,e⟩
    subst y
    by_cases e : i=j
    · subst j;exact (bad ⟨i,hi,fun x => gateOp t (u x) (v x),rfl⟩).elim
    · refine ⟨⟨(i,j),hi,hj,e⟩,?_⟩
      change image (merge i j) p _
      rcases unary_meet_join u v t with h|h|h|h
      · exact ⟨con false,cs _,by funext r;simp [sub,con,bit_merge,Ne.symm e,h]⟩
      · exact ⟨con true,cs _,by funext r;simp [sub,con,bit_merge,Ne.symm e,h]⟩
      · exact ⟨_,ha,by funext r;simp [sub,bit_merge,Ne.symm e,h]⟩
      · exact ⟨_,hb,by funext r;simp [sub,bit_merge,Ne.symm e,h]⟩

theorem after_merge {S : Row} {d : Pair S} {y}
    (h : image (merge d.val.1 d.val.2) (start S) y) : start (S.erase d.val.1) y := by
  obtain ⟨⟨i,j⟩,hi,hj,ne⟩ := d
  obtain ⟨a,ha,rfl⟩ := h
  rcases ha with rfl|rfl|⟨v,hv,rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · right;right
    by_cases e : v=i
    · subst v
      exact ⟨j,Finset.mem_erase.mpr ⟨ne.symm,hj⟩,by funext r;simp [sub,bit_merge]⟩
    · exact ⟨v,Finset.mem_erase.mpr ⟨e,hv⟩,by funext r;simp [sub,bit_merge,e]⟩

theorem drop_merge {S : Row} {f k} (rs : run k (start S) f) (non : S.Nonempty) (bad : ¬unary S f) :
    ∃ d : Pair S, ∃ m, m+1=k ∧ run m (start (S.erase d.val.1)) (sub (merge d.val.1 d.val.2) f) := by
  obtain ⟨d,m,len,out⟩ := eliminate (fun d : Pair S => merge d.val.1 d.val.2) (unary S) (start S) f k
    (fun _ h => unary_start non h) bad rs (fun b => by cases b;exact Or.inl rfl;exact Or.inr (Or.inl rfl))
    (fun p g c _ s b => merge_step p g c s b)
  exact ⟨d,m,len,weaken (fun _ h => after_merge h) out⟩
end PetersenDrops
namespace PetersenEquality
-- Four rows are ordered 00, 01, 10, 11, with the first row in the low bit.
def initial : List Nat := [0,15,10,12]
def gen (vs : List Nat) := vs ++ vs.map (fun x => 15 ^^^ x) ++
  vs.flatMap (fun a => vs.flatMap fun b => [a &&& b,a ||| b])
def possible : Nat → List Nat → Bool
  | 0,vs => vs.contains 9
  | k+1,vs => (gen vs).eraseDups.any fun a => possible k (a::vs)
theorem equality_two : possible 3 initial=false := by decide +kernel
end PetersenEquality
namespace PetersenDrops

def Mixed (S : Row) (f : Signal) :=
  f ∅=true ∧ (∀ i∈S,f {i}=false) ∧ ∃ r, r⊆S ∧ r.Nonempty ∧ f r=true

def code (i j : Nat) (f : Signal) := Nat.bit (f ∅) (Nat.bit (f {i}) (Nat.bit (f {j}) (Nat.bit (f {i,j}) 0)))
theorem code_flip (i j f) : code i j (flip f)=15 ^^^ code i j f := by
  change _=(Nat.bit true (Nat.bit true (Nat.bit true (Nat.bit true 0)))) ^^^ _
  simp only [code,flip,Nat.xor_bit];simp
theorem code_both (i j f g) : code i j (both f g)=code i j f &&& code i j g := by
  simp only [code,both,Nat.land_bit];simp
theorem code_either (i j f g) : code i j (either f g)=code i j f ||| code i j g := by
  simp only [code,either,Nat.lor_bit];simp

theorem coded_step (i j : Nat) {p y vs} (old : ∀ g,p g → code i j g∈vs) (st : next p y) :
    code i j y∈PetersenEquality.gen vs := by
  rcases st with ⟨a,ha,rfl⟩|⟨a,ha,b,hb,op|op⟩
  · rw [code_flip]
    apply List.mem_append_left
    exact List.mem_append_right _ (List.mem_map.mpr ⟨_,old _ ha,rfl⟩)
  · subst y;rw [code_both]
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨_,old _ ha,List.mem_flatMap.mpr ⟨_,old _ hb,by simp⟩⟩
  · subst y;rw [code_either]
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨_,old _ ha,List.mem_flatMap.mpr ⟨_,old _ hb,by simp⟩⟩

theorem coded_run (i j : Nat) {p f k vs} (old : ∀ g,p g → code i j g∈vs)
    (out : code i j f=9) (rs : run k p f) : PetersenEquality.possible k vs=true := by
  induction k generalizing vs p with
  | zero => simpa [PetersenEquality.possible,←out] using old f rs
  | succ k ih =>
    obtain ⟨y,st,rest⟩ := rs
    apply List.any_eq_true.mpr
    refine ⟨_,List.mem_eraseDups.mpr (coded_step i j old st),ih ?_ rest⟩
    rintro a (rfl|ha)
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (old _ ha)

theorem two_bound {S : Row} {f k} (card : S.card=2) (m : Mixed S f) (rs : run k (start S) f) : 4≤k := by
  classical
  obtain ⟨i,j,ne,rfl⟩ := Finset.card_eq_two.mp card
  obtain ⟨empty,one,r,sub',non,high⟩ := m
  have singleI := one i (by simp)
  have singleJ := one j (by simp)
  have ri : i∈r := by
    by_contra hi
    have e : r={j} := by
      apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
      exact ⟨non,fun a ha => by have h := sub' ha;simp only [Finset.mem_insert,Finset.mem_singleton] at h;rcases h with rfl|rfl;contradiction;rfl⟩
    rw [e,singleJ] at high;contradiction
  have rj : j∈r := by
    by_contra hj
    have e : r={i} := by
      apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
      exact ⟨non,fun a ha => by have h := sub' ha;simp only [Finset.mem_insert,Finset.mem_singleton] at h;rcases h with rfl|rfl;rfl;contradiction⟩
    rw [e,singleI] at high;contradiction
  have rfull : r={i,j} := Finset.Subset.antisymm sub' (by simp [Finset.insert_subset_iff,ri,rj])
  have word : code i j f=9 := by simp only [code,empty,singleI,singleJ,←rfull,high];rfl
  have old (g) (hg : start {i,j} g) : code i j g∈PetersenEquality.initial := by
    rcases hg with rfl|rfl|⟨v,hv,rfl⟩
    · change (0 : Nat)∈PetersenEquality.initial;decide
    · change (15 : Nat)∈PetersenEquality.initial;decide
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with rfl|rfl <;> simp [code,bit,ne,Ne.symm ne,PetersenEquality.initial,Nat.bit]
  have yes := coded_run i j old word rs
  by_contra! h
  have small : ∀ i : Fin 4,PetersenEquality.possible i.val PetersenEquality.initial≠true := by decide +kernel
  exact small ⟨k,h⟩ yes
end PetersenDrops
namespace PetersenDrops

theorem not_unary {S : Row} {f : Signal} (large : 2 ≤ S.card) (m : Mixed S f) : ¬unary S f := by
  rintro ⟨i,hi,u,rfl⟩
  have card := Finset.card_erase_of_mem hi
  have pos : 0 < (S.erase i).card := by omega
  obtain ⟨j,mem⟩ := Finset.card_pos.mp pos
  obtain ⟨ne,hj⟩ := Finset.mem_erase.mp mem
  have e := m.1
  have o := m.2.1 j hj
  simp [bit,Ne.symm ne] at e o
  simp_all

theorem mixed_lower (k : Nat) {S : Row} {f : Signal} (large : 2 ≤ S.card)
    (m : Mixed S f) (rs : run k (start S) f) : S.card+2 ≤ k := by
  classical
  induction k using Nat.strong_induction_on generalizing S f with
  | ind k ih =>
    by_cases base : S.card=2
    · have b := two_bound base m rs;omega
    have three : 3 ≤ S.card := by omega
    by_cases proper : ∃ r : Row,r ⊂ S ∧ r.Nonempty ∧ f r=true
    · obtain ⟨r,small,nz,hi⟩ := proper
      obtain ⟨z,hz,absent⟩ := Finset.exists_of_ssubset small
      obtain ⟨l,n,program⟩ := drop_zero rs m.1 (m.2.1 z hz)
      have card := Finset.card_erase_of_mem hz
      have mixed : Mixed (S.erase z) (sub (kill z) f) := by
        refine ⟨by simpa [sub,kill] using m.1,?_,r,?_,nz,?_⟩
        · intro i mem
          obtain ⟨ne,ins⟩ := Finset.mem_erase.mp mem
          simpa [sub,kill,Ne.symm ne] using m.2.1 i ins
        · intro x hx
          exact Finset.mem_erase.mpr ⟨fun e => absent (e ▸ hx),small.1 hx⟩
        · simpa [sub,kill,Finset.erase_eq_of_notMem absent] using hi
      have b := ih l (by omega) (by omega : 2 ≤ (S.erase z).card) mixed program
      omega
    · have highS : f S=true := by
        obtain ⟨r,sub',non,pos⟩ := m.2.2
        by_cases eq : r=S
        · exact eq ▸ pos
        · exact (proper ⟨r,Finset.ssubset_iff_subset_ne.mpr ⟨sub',eq⟩,non,pos⟩).elim
      obtain ⟨⟨⟨i,j⟩,ins,jns,ne⟩,l,n,program⟩ := drop_merge rs (Finset.card_pos.mp (by omega)) (not_unary large m)
      have card : (S.erase i).card=S.card-1 := Finset.card_erase_of_mem (show i∈S from ins)
      have member : j∈S.erase i := Finset.mem_erase.mpr ⟨Ne.symm ne,jns⟩
      have rlow : f {i,j}=false := by
        cases e : f {i,j} with
        | false => rfl
        | true =>
          have sm : ({i,j} : Row) ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨by simp [Finset.insert_subset_iff,ins,jns],by
            intro eq
            have c := congrArg Finset.card eq
            simp [ne] at c
            omega⟩
          exact (proper ⟨_,sm,by simp,e⟩).elim
      have mixed : Mixed (S.erase i) (sub (merge i j) f) := by
        refine ⟨by simpa [sub,merge] using m.1,?_,S.erase i,Finset.Subset.refl _,⟨j,member⟩,?_⟩
        · intro v mem
          obtain ⟨vi,vs⟩ := Finset.mem_erase.mp mem
          by_cases e : v=j
          · subst v;simpa [sub,merge,ne] using rlow
          · simpa [sub,merge,Ne.symm e,Ne.symm vi] using m.2.1 v vs
        · simpa [sub,merge,member,Finset.insert_erase ins] using highS
      have b := ih l (by omega) (by omega : 2 ≤ (S.erase i).card) mixed program
      omega
end PetersenDrops
namespace PetersenDrops
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L171Prefix
def ordinary : Row := {0,1,2,3,5,8}
def inputs (r : Row) (i : Fin 9) : Bool := if i.val∈ordinary then bit i.val r else false
def signal (C : Circuit) (i : Nat) : Signal := fun r => (C.wires (List.ofFn (inputs r))).getD i false

theorem raw_signal (C : Circuit) (i : Nat) (hi : i < 9) : start ordinary (signal C i) := by
  have e : signal C i=fun r => inputs r ⟨i,hi⟩ := by
    funext r
    unfold signal
    rw [wires_eq,foldl_step_getD _ _ _ (by simpa using hi)]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi,↓reduceDIte,Option.getD_some]
  by_cases ins : i∈ordinary
  · exact Or.inr (Or.inr ⟨i,ins,by simpa only [inputs,ins,ite_true] using e⟩)
  · left;change signal C i=(fun _ => false);simpa only [inputs,ins,ite_false] using e

theorem absent_signal (C : Circuit) (i : Nat) (late : 9+C.size ≤ i) : signal C i=con false := by
  funext r;apply getD_of_length_le
  rw [wires_eq,foldl_step_length,List.length_ofFn];exact late

theorem repeat_step {p y} (h : p y) : next p y := by
  right;exact ⟨y,h,y,h,Or.inl (by funext r;simp [both])⟩

theorem circuit_step (C : Circuit) (fan : FanInTwo C) (j : Fin C.size) {p : Pool}
    (zero : p (con false)) (one : p (con true)) (old : ∀ i < 9+j.val,p (signal C i)) :
    next p (signal C (9+j.val)) := by
  let g := C.gates.get j
  let read (i : Nat) : Signal := if i < 9+j.val then signal C i else con false
  have avail (i) : p (read i) := by unfold read;split <;> first | apply old;assumption | exact zero
  have gate (r) : signal C (9+j.val) r=g.op.eval (g.inputs.map (fun i => read i r)) := by
    have e := gate_value C.gates (List.ofFn (inputs r)) j.val j.isLt
    have gt : g=C.gates[j.val]'j.isLt := rfl
    rw [gt]
    simp only [List.length_ofFn] at e
    refine e.trans ?_
    congr 1;apply List.map_congr_left
    intro i _
    by_cases h : i < 9+j.val <;> simp [read,h,signal,wires_eq,con]
  obtain ⟨op,arity⟩ := fan g (List.get_mem _ j)
  have ops : g.op=.and ∨ g.op=.or ∨ g.op=.not := by simpa using op
  cases ls : g.inputs with
  | nil =>
    apply repeat_step
    rcases ops with h|h|h
    · have e : signal C (9+j.val)=con true := by funext r;rw [gate,ls,h];rfl
      exact e ▸ one
    · have e : signal C (9+j.val)=con false := by funext r;rw [gate,ls,h];rfl
      exact e ▸ zero
    · have e : signal C (9+j.val)=con true := by funext r;rw [gate,ls,h];rfl
      exact e ▸ one
  | cons a tail =>
    have inv (h : g.op=.not) : next p (signal C (9+j.val)) :=
      Or.inl ⟨read a,avail a,by funext r;rw [gate,ls,h];rfl⟩
    cases tail with
    | nil =>
      rcases ops with h|h|h
      · have e : signal C (9+j.val)=read a := by funext r;rw [gate,ls,h];simp [GateOp.eval]
        exact repeat_step (e ▸ avail a)
      · have e : signal C (9+j.val)=read a := by funext r;rw [gate,ls,h];simp [GateOp.eval]
        exact repeat_step (e ▸ avail a)
      · exact inv h
    | cons b tail =>
      have nil : tail=[] := by rw [ls] at arity;apply List.length_eq_zero_iff.mp;change tail.length+1+1 ≤ 2 at arity;omega
      subst tail
      rcases ops with h|h|h
      · right;exact ⟨read a,avail a,read b,avail b,Or.inl (by funext r;rw [gate,ls,h];simp [GateOp.eval,both])⟩
      · right;exact ⟨read a,avail a,read b,avail b,Or.inr (by funext r;rw [gate,ls,h];simp [GateOp.eval,either])⟩
      · exact inv h

theorem run_prefix (C : Circuit) (fan : FanInTwo C) (w j k) (hw : w < 9+(j+k))
    (p : Pool) (zero : p (con false)) (one : p (con true)) (old : ∀ i < 9+j,p (signal C i)) :
    run k p (signal C w) := by
  induction k generalizing p j with
  | zero => exact old _ hw
  | succ k ih =>
    have st : next p (signal C (9+j)) := by
      by_cases live : j < C.size
      · exact circuit_step C fan ⟨j,live⟩ zero one old
      · rw [absent_signal C _ (by omega)];exact repeat_step zero
    refine ⟨_,st,ih (j+1) (by omega) _ (Or.inr zero) (Or.inr one) ?_⟩
    intro i hi
    by_cases pre : i < 9+j
    · exact Or.inr (old i pre)
    · left;have e : i=9+j := by omega
      rw [e]

def rowOf (r : Nat) := ordinary.filter (fun i => r.testBit i)
theorem selected_rows : ∀ r : Fin 512,r.val &&& 303=r.val → r.val≠0 →
    (rowOf r.val).Nonempty ∧ ∀ i : Fin 9,inputs (rowOf r.val) i=r.val.testBit i.val := by decide +kernel
theorem singleton_rows : ∀ i∈ordinary,i∈([0,1,2,3,5,8] : List Nat) ∧
    ∀ j : Fin 9, inputs {i} j=(2^i : Nat).testBit j.val := by decide +kernel

end PetersenDrops
open PetersenDrops
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 12000 in
theorem PetersenCertificate.early_wire_bound : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     ∀ x3 < (16 : ℕ),       have x5 : ℕ → Bool := fun (x5 : ℕ) => (x1.wires (List.ofFn fun (x6 : Fin (9 : ℕ)) => x5.testBit ↑x6)).getD x3 Bool.false;       ¬(x5 (0 : ℕ) = Bool.true ∧ (∀ x6 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (5 : ℕ), (8 : ℕ)], x5 ((2 : ℕ) ^ x6) = Bool.false) ∧ ∃ (x6 : Fin (512 : ℕ)), ↑x6 &&& (303 : ℕ) = ↑x6 ∧ ↑x6 ≠ (0 : ℕ) ∧ x5 ↑x6 = Bool.true) := by
  intro C fan w early
  dsimp only
  intro h
  obtain ⟨empty,single,r,proj,nonempty,high⟩ := h
  let eval (m : Nat) := (C.wires (List.ofFn (fun i : Fin 9 => m.testBit i.val))).getD w false
  have transfer (x : Row) (m : Nat) (hm : ∀ j : Fin 9,inputs x j=m.testBit j.val) : signal C w x=eval m := by
    change (C.wires (List.ofFn (inputs x))).getD w false=_
    rw [show inputs x=(fun i : Fin 9 => m.testBit i.val) from funext hm]
  have zeroEq : ∀ i : Fin 9, inputs ∅ i=(0 : Nat).testBit i.val := by decide +kernel
  have mixed : Mixed ordinary (signal C w) := by
    refine ⟨(transfer ∅ 0 zeroEq).trans empty,?_,rowOf r,Finset.filter_subset _ _,(selected_rows r proj nonempty).1,?_⟩
    · intro v hv
      obtain ⟨mem,eq⟩ := singleton_rows v hv
      exact (transfer {v} (2^v) eq).trans (single v mem)
    · exact (transfer (rowOf r) r (selected_rows r proj nonempty).2).trans high
  have run7 := run_prefix C fan w 0 7 early (start ordinary) (Or.inl rfl)
    (Or.inr (Or.inl rfl)) (fun i h => raw_signal C i h)
  have impossible := mixed_lower 7 (by decide : 2 ≤ ordinary.card) mixed run7
  have six : ordinary.card=6 := by decide
  omega
