import LocalCones

/-! ## Certificates using at most four input wires -/

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1506 Simlowker.Types1735
namespace Simlowker.Transversal1735
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

def hitsWire (q : Nat) (x : Fin n → Bool) := ∃ w ∈ orIn n C q, x w = true
def hitsAll (R : Finset Nat) (x : Fin n → Bool) := ∀ q ∈ R, hitsWire C q x

theorem feeds_cone (ao : IsAO2 n C) {k j : Nat} (hj : j < C.gates.length) (h : feeds G C k j) :
    InCone n C k j := by
  obtain ⟨_,_,b,re⟩ := h
  let p := opnd C j b
  have A := ao_of n C ao
  obtain ⟨a,d,ins,la,ld⟩ := (A j hj).2
  have mem : p ∈ (gateAt C j).inputs := by fin_cases b <;> simp [p,opnd,ins,List.getD]
  have pre : p < n+j := by fin_cases b <;> simp [p,opnd,ins,List.getD,la,ld]
  change OrR n C p (n+k) at re
  have le := orR_le n C A _ _ re
  have pe : p = n+(p-n) := by omega
  rcases orR_cone n C A k p re (p-n) pe (by omega) with eq|hc
  · apply inCone_c1 n C A k j hj
    rwa [eq,←pe]
  · apply inCone_c2 n C A k (p-n) j hj hc
    rwa [←pe]

def dirtyPort (q : Nat) := ∃ k ∈ junk G C, ∃ b : Fin 2, q = opnd C k b

theorem flat_trace_strong (ao : IsAO2 n C) (top : TopForm G C)
    (flat : ∀ i ∈ junk G C, ∀ k ∈ junk G C, ¬ InCone n C i k)
    {j : Nat} (hj : j ∈ tops G C) (x : Fin n → Bool) (on : gateVal n C j x = true) :
    ∃ R ⊆ ports G C j, R.card ≤ 4 ∧ (4 ≤ R.card → ∀ q ∈ R, dirtyPort G C q) ∧ hitsAll C R x ∧ ∀ y, hitsAll C R y → graphFun G ∅ y = true := by
  classical
  have info := hj
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at info
  obtain ⟨lt,op,clean⟩ := info
  have half (b : Fin 2) (orig : W n C x (opnd C j b) = true) :
      ∃ R ⊆ ports G C j, R.card ≤ 2 ∧ (2 ≤ R.card → ∀ q ∈ R, dirtyPort G C q) ∧ hitsAll C R x ∧
        ∀ y, hitsAll C R y → W n C y (opnd C j b) = true := by
    rcases (through_operand G C ao top lt op b x).mp orig with lit|⟨k,sm,hk,reach,active⟩
    · refine ⟨{opnd C j b},Finset.singleton_subset_iff.mpr (port_mem G C (Or.inl rfl) b),by simp,by simp,?_,?_⟩
      · intro q hq
        obtain rfl := Finset.mem_singleton.mp hq
        exact lit
      · intro y all
        exact (through_operand G C ao top lt op b y).mpr (Or.inl (all _ (Finset.mem_singleton_self _)))
    · have feed : feeds G C k j := ⟨sm,hk,b,reach⟩
      have mem := Finset.mem_filter.mp hk
      have klt := Finset.mem_range.mp mem.1
      have kop := mem.2.1
      have both := (and_on C ao klt kop x).mp active
      have lit (z : Fin 2) (wz : W n C x (opnd C k z) = true) : hitsWire C (opnd C k z) x := by
        rcases (through_operand G C ao top klt kop z x).mp wz with yes|⟨i,sm',hi,re,_⟩
        · exact yes
        · exact False.elim (flat i hi k hk (feeds_cone G C ao klt ⟨sm',hi,z,re⟩))
      let R : Finset Nat := {opnd C k 0,opnd C k 1}
      refine ⟨R,?_,Finset.card_le_two,?_,?_,?_⟩
      · intro q hq
        rcases Finset.mem_insert.mp hq with eq|singleton
        · exact eq ▸ port_mem G C (Or.inr (.single feed)) 0
        · exact Finset.mem_singleton.mp singleton ▸ port_mem G C (Or.inr (.single feed)) 1
      · intro _ q hq
        rcases Finset.mem_insert.mp hq with eq|singleton
        · exact ⟨k,hk,0,eq⟩
        · exact ⟨k,hk,1,Finset.mem_singleton.mp singleton⟩
      · intro q hq
        rcases Finset.mem_insert.mp hq with eq|singleton
        · exact eq ▸ lit 0 both.1
        · exact Finset.mem_singleton.mp singleton ▸ lit 1 both.2
      · intro y all
        have yes (z : Fin 2) (hz : opnd C k z ∈ R) : W n C y (opnd C k z) = true :=
          (through_operand G C ao top klt kop z y).mpr (Or.inl (all _ hz))
        have kOn := (and_on C ao klt kop y).mpr ⟨yes 0 (by simp [R]),yes 1 (by simp [R])⟩
        exact (through_operand G C ao top lt op b y).mpr (Or.inr ⟨k,sm,hk,reach,kOn⟩)
  obtain ⟨h0,h1⟩ := (and_on C ao lt op x).mp on
  obtain ⟨A,sa,ca,da,ax,ay⟩ := half 0 h0
  obtain ⟨B,sb,cb,db,bx,by'⟩ := half 1 h1
  have total := Finset.card_union_le A B
  refine ⟨A ∪ B,Finset.union_subset sa sb,total.trans (by omega),?_,?_,?_⟩
  · intro big q hq
    exact (Finset.mem_union.mp hq).elim (da (by omega) q) (db (by omega) q)
  · intro q hq
    exact (Finset.mem_union.mp hq).elim (ax q) (bx q)
  · intro y enabled
    exact clean _ ((and_on C ao lt op y).mpr
      ⟨ay y (fun q h => enabled q (Finset.mem_union_left _ h)),
       by' y (fun q h => enabled q (Finset.mem_union_right _ h))⟩)

#print axioms flat_trace_strong
end Simlowker.Transversal1735

/-! ## Residual edges of nonnested dirty gates -/

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover
open Simlowker.Types1735
namespace Simlowker.Transversal1735
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

def thinVertex (v : Fin n) := ∃ k ∈ junk G C, ∃ b : Fin 2,
  v ∈ side C k b ∧ (side (n:=n) C k b).card ≤ 3

theorem trace_near (four : NoFourCycle G) (R : Finset Nat) {u v : Fin n}
    (active : hitsAll C R (pairInput u v)) (safe : ∀ y, hitsAll C R y → graphFun G ∅ y = true) :
    ∃ q ∈ missing C R u v, ((orIn n C q).filter fun y => ¬G.Adj u y).card < 2^((missing C R u v).card-1) := by
  apply missing_near G C four
  intro y hy
  apply safe
  intro q hq
  obtain ⟨w,hw,src⟩ := active q hq
  rcases of_decide_eq_true src with e|e
  · exact hy q hq (Or.inl (e ▸ hw))
  · exact hy q hq (Or.inr (e ▸ hw))

theorem flat_residual (four : NoFourCycle G) (least : IsLeastAO G C) (top : TopForm G C)
    (flat : ∀ i ∈ junk G C, ∀ j ∈ junk G C, ¬InCone n C i j)
    (u v : Fin n) (edge : s(u,v) ∈ Ustar G C) :
    s(u,v) ∈ frontEdges G C 2 ∨ thinVertex G C u ∨ thinVertex G C v := by
  classical
  obtain ⟨eG,out⟩ := Finset.mem_sdiff.mp edge
  obtain ⟨j,hj,on⟩ := edge_top G C least (G.mem_edgeFinset.mp eG)
  obtain ⟨R,sub,small,dirty,active,safe⟩ := flat_trace_strong G C least.1 top flat hj _ on
  have swap : pairInput v u = pairInput u v := by funext w; simp [pairInput,or_comm]
  have flipped : hitsAll C R (pairInput v u) := by rwa [swap]
  obtain ⟨a,ma,nearA⟩ := trace_near G C four R active safe
  obtain ⟨b,mb,nearB⟩ := trace_near G C four R flipped safe
  let A := missing C R u v
  let B := missing C R v u
  have sep : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro q ha hb
    exact (Finset.mem_filter.mp ha).2.2 (Finset.mem_filter.mp hb).2.1
  have subAB : A ∪ B ⊆ R := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have total := Finset.card_le_card subAB
  rw [Finset.card_union_of_disjoint sep] at total
  have ap : 0 < A.card := Finset.card_pos.mpr ⟨a,ma⟩
  have bp : 0 < B.card := Finset.card_pos.mpr ⟨b,mb⟩
  have aa := Finset.mem_filter.mp ma
  have bb := Finset.mem_filter.mp mb
  by_cases charged : s(u,v) ∈ frontEdges G C 2
  · exact Or.inl charged
  right
  have charge' : s(v,u) ∉ frontEdges G C 2 := fun h => charged (Sym2.eq_swap ▸ h)
  have narrow {x z : Fin n} {q : Nat} (occ : z ∈ orIn n C q) (no : s(x,z) ∉ frontEdges G C 2)
      (d : Nat) (count : d≤2) (h : ((orIn n C q).filter fun y => ¬G.Adj x y).card < 2^(d-1)) :
      (orIn n C q).card ≤ 3 := by
    by_contra! wide
    have near : ((orIn n C q).filter fun y => ¬G.Adj x y).card < 2 := h.trans_le
      (show 2^(d-1) ≤ 2^1 from Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
    exact no (front_in G C (wire_frontier G C least.1 (by decide : 0<2) x z q (by omega) near occ))
  have smallA (h : A.card ≤ 2) := narrow aa.2.1 charged A.card h nearA
  have smallB (h : B.card ≤ 2) := narrow bb.2.1 charge' B.card h nearB
  have thin {q : Nat} {x : Fin n} (port : dirtyPort G C q) (occ : x ∈ orIn n C q)
      (sz : (orIn n C q).card ≤ 3) : thinVertex G C x := by
    obtain ⟨k,hk,z,rfl⟩ := port
    exact ⟨k,hk,z,occ,sz⟩
  by_cases fourBits : 4 ≤ R.card
  · by_cases h : A.card ≤ 2
    · exact Or.inr (thin (dirty fourBits a aa.1) aa.2.1 (smallA h))
    · exact Or.inl (thin (dirty fourBits b bb.1) bb.2.1 (smallB (by omega)))
  have ha := smallA (by omega)
  have hb := smallB (by omega)
  by_cases da : dirtyPort G C a
  · exact Or.inr (thin da aa.2.1 ha)
  by_cases db : dirtyPort G C b
  · exact Or.inl (thin db bb.2.1 hb)
  have root {q : Nat} (hq : q ∈ R) (notD : ¬dirtyPort G C q) : ∃ z : Fin 2, q=opnd C j z := by
    obtain ⟨⟨k,z⟩,p,eq⟩ := Finset.mem_image.mp (sub hq)
    change opnd C k z = q at eq
    have rel : k ∈ relevant G C j := (Finset.mem_product.mp p).1
    rcases Finset.mem_insert.mp rel with kj|dirtyK
    · exact ⟨z,kj ▸ eq.symm⟩
    · exact False.elim (notD ⟨k,(Finset.mem_filter.mp dirtyK).1,z,eq.symm⟩)
  obtain ⟨i,ri⟩ := root aa.1 da
  obtain ⟨l,rl⟩ := root bb.1 db
  have vi : v ∈ side C j i := by simpa only [side,←ri] using aa.2.1
  have ul : u ∈ side C j l := by simpa only [side,←rl] using bb.2.1
  have ne : i ≠ l := by
    intro eq
    have same : a=b := ri.trans ((congrArg (opnd C j) eq).trans rl.symm)
    exact aa.2.2 (same ▸ bb.2.1)
  have cross (x y : Fin n) (hx : x ∈ side C j 0) (hy : y ∈ side C j 1) : s(x,y) ∈ starEdges G C :=
    Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,rfl⟩⟩
  exfalso
  apply out
  fin_cases i <;> fin_cases l
  · exact False.elim (ne rfl)
  · exact Sym2.eq_swap ▸ cross v u vi ul
  · exact cross u v ul vi
  · exact False.elim (ne rfl)

theorem no_thin_linear (four : NoFourCycle G) (least : IsLeastAO G C) (top : TopForm G C)
    (flat : ∀ i ∈ junk G C, ∀ j ∈ junk G C, ¬InCone n C i j)
    (wide : ∀ k ∈ junk G C, ∀ b : Fin 2, (side (n:=n) C k b).Nonempty → 4 ≤ (side (n:=n) C k b).card) :
    (Ustar G C).card ≤ 8*C.size := by
  have none (x) : ¬thinVertex G C x := by
    rintro ⟨k,hk,b,hx,small⟩
    exact (Nat.not_le_of_gt (wide k hk b ⟨x,hx⟩)) small
  apply (Finset.card_le_card ?_).trans (front_count G C four 2)
  intro e
  induction e using Sym2.inductionOn with
  | _ u v =>
    intro edge
    exact (flat_residual G C four least top flat u v edge).resolve_right
      (fun h => h.elim (none u) (none v))

noncomputable def thinSet : Finset (Fin n) := by classical exact Finset.univ.filter (thinVertex G C)

theorem thin_remainder (four : NoFourCycle G) (least : IsLeastAO G C) (top : TopForm G C)
    (flat : ∀ i ∈ junk G C, ∀ j ∈ junk G C, ¬InCone n C i j) :
    (Ustar G C).card ≤ 9*C.size + 1 + (thinSet G C).card^2 := by
  classical
  let Z := thinSet G C
  let S := G.support.toFinset
  let B := fun x => (Z.filter (G.Adj x)).image (fun y => s(x,y))
  have sub : Ustar G C ⊆ frontEdges G C 2 ∪ S.biUnion B := by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
      intro edge
      rcases flat_residual G C four least top flat u v edge with h|h
      · exact Finset.mem_union_left _ h
      have adj : G.Adj u v := G.mem_edgeFinset.mp (Finset.mem_sdiff.mp edge).1
      have cover (x y : Fin n) (xy : G.Adj x y) (small : thinVertex G C y) : s(x,y) ∈ S.biUnion B :=
        Finset.mem_biUnion.mpr ⟨x,Set.mem_toFinset.mpr ⟨y,xy⟩,Finset.mem_image.mpr
          ⟨y,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,small⟩,xy⟩,rfl⟩⟩
      apply Finset.mem_union_right
      rcases h with a|b
      · exact Sym2.eq_swap ▸ cover v u adj.symm a
      · exact cover u v adj b
  have count : (S.biUnion B).card ≤ S.card + Z.card^2 := by
    calc
      _ ≤ ∑ x ∈ S, (B x).card := Finset.card_biUnion_le
      _ ≤ ∑ x ∈ S, (Z.filter (G.Adj x)).card := Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
      _ ≤ _ := incidence_bound G four S Z
  have upper := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  have f := front_count G C four 2
  have s : S.card = G.support.ncard := by simp [S,Set.ncard_eq_toFinset_card']
  have h := PEqualNP.Outside.L_meta_2074 n G C least
  change _ ≤ _ + Z.card^2
  omega

#print axioms thin_remainder
#print axioms flat_residual
#print axioms no_thin_linear
end Simlowker.Transversal1735
