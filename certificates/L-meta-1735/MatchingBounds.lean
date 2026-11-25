import LocalWitnesses

/-! ## Maximal induced matchings and their neighborhoods -/

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
namespace Simlowker.Types1735

def apart {α : Type*} (R : α → α → Prop) (I : Finset α) :=
  ∀ a ∈ I, ∀ b ∈ I, a ≠ b → ¬R a b

theorem maximal_apart {α : Type*} (R : α → α → Prop) (sym : ∀ a b, R a b → R b a) (E : Finset α) :
    ∃ I ⊆ E, apart R I ∧ ∀ b ∈ E, ∃ a ∈ I, b = a ∨ R b a := by
  classical
  let P := E.powerset.filter (apart R)
  have nonempty : P.Nonempty := ⟨∅,by simp [P,apart]⟩
  obtain ⟨I,mem,maxi⟩ := P.exists_max_image Finset.card nonempty
  obtain ⟨subset,ok⟩ := Finset.mem_filter.mp mem
  have sub := Finset.mem_powerset.mp subset
  refine ⟨I,sub,ok,?_⟩
  intro b hb
  by_contra! lonely
  have outside : b ∉ I := fun h => (lonely b h).1 rfl
  have safe : apart R (insert b I) := by
    intro x hx y hy neq
    rcases Finset.mem_insert.mp hx with xb|xi
    · subst x
      rcases Finset.mem_insert.mp hy with yb|yi
      · exact False.elim (neq yb.symm)
      · exact (lonely y yi).2
    · rcases Finset.mem_insert.mp hy with yb|yi
      · subst y
        exact fun rel => (lonely x xi).2 (sym _ _ rel)
      · exact ok x xi y yi neq
  have larger := maxi (insert b I) (Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.insert_subset hb sub),safe⟩)
  rw [Finset.card_insert_of_notMem outside] at larger
  omega

variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
abbrev VertexPair (n : Nat) := Fin n × Fin n
def endpoint (p : VertexPair n) (x : Fin n) := x=p.1 ∨ x=p.2
def conflict (p q : VertexPair n) := ∃ x y, endpoint p x ∧ endpoint q y ∧ G.Adj x y

omit [DecidableRel G.Adj] in
theorem conflict_sym (p q : VertexPair n) (h : conflict G p q) : conflict G q p := by
  obtain ⟨x,y,hx,hy,adj⟩ := h
  exact ⟨y,x,hy,hx,adj.symm⟩

theorem packing_bound (least : IsLeastAO G C) (top : TopForm G C) (M : Finset (VertexPair n))
    (active : ∀ p ∈ M, s(p.1,p.2) ∈ Ustar G C) (sep : apart (conflict G) M) :
    M.card ≤ 2 * (junk G C).card := by
  classical
  let e : Fin M.card ≃ {p // p ∈ M} := (Fintype.equivFinOfCardEq (Fintype.card_coe M)).symm
  apply matching_junk G C least top (fun i => (e i).val.1) (fun i => (e i).val.2)
    (fun i => active _ (e i).property)
  intro i j diff x y hx hy adj
  apply sep _ (e i).property _ (e j).property _ ⟨x,y,hx,hy,adj⟩
  intro eq
  exact diff (e.injective (Subtype.ext eq))

/-- Edges with an endpoint adjacent to a fixed vertex. -/
def watched (a : Fin n) : Finset (Sym2 (Fin n)) :=
  (G.neighborFinset a).biUnion fun b => (G.neighborFinset b).image fun c => s(b,c)

theorem watched_count (hg : ∀ a : Fin n, ∀ p : G.Walk a a, p.IsCycle → 5 ≤ p.length)
    (a : Fin n) (ha : a ∈ G.support) : (watched G a).card ≤ G.support.ncard - 1 := by
  classical
  obtain ⟨tri,sq⟩ := Simlowker.Residual1735.girth_local G hg
  have loc := Simlowker.Residual1735.local_degree G tri sq a G.support.toFinset
    (fun _ h => Set.mem_toFinset.mpr h) (Set.mem_toFinset.mpr ha)
  calc
    _ ≤ ∑ b ∈ G.neighborFinset a, ((G.neighborFinset b).image fun c => s(b,c)).card := Finset.card_biUnion_le
    _ ≤ ∑ b ∈ G.neighborFinset a, G.degree b := Finset.sum_le_sum fun b _ =>
      Finset.card_image_le.trans_eq (G.card_neighborFinset_eq_degree b)
    _ ≤ _ := by simpa only [Set.ncard_eq_toFinset_card'] using loc

theorem maximal_packing (least : IsLeastAO G C) (top : TopForm G C) :
    ∃ M : Finset (VertexPair n), M.card ≤ 2*(junk G C).card ∧
      (∀ p ∈ M, s(p.1,p.2) ∈ Ustar G C) ∧
      ∀ u v, s(u,v) ∈ Ustar G C → ∃ p ∈ M, conflict G (u,v) p := by
  classical
  let E := Finset.univ.filter (fun p : VertexPair n => s(p.1,p.2) ∈ Ustar G C)
  obtain ⟨M,sub,sep,cover⟩ := maximal_apart (conflict G) (conflict_sym G) E
  have active (p) (hp : p ∈ M) := (Finset.mem_filter.mp (sub hp)).2
  refine ⟨M,packing_bound G C least top M active sep,active,?_⟩
  intro u v edge
  obtain ⟨p,mp,eq|near⟩ := cover (u,v) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,edge⟩)
  · subst p
    exact ⟨(u,v),mp,u,v,Or.inl rfl,Or.inr rfl,G.mem_edgeFinset.mp (Finset.mem_sdiff.mp edge).1⟩
  · exact ⟨p,mp,near⟩

theorem linear_in_junk (hg : ∀ a : Fin n, ∀ p : G.Walk a a, p.IsCycle → 5 ≤ p.length)
    (least : IsLeastAO G C) (top : TopForm G C) :
    (Ustar G C).card ≤ (4*(junk G C).card) * C.size := by
  classical
  obtain ⟨M,hM,active,cover⟩ := maximal_packing G C least top
  let B := fun p : VertexPair n => watched G p.1 ∪ watched G p.2
  have found (a u v : Fin n) (au : G.Adj a u) (uv : G.Adj u v) : s(u,v) ∈ watched G a :=
    Finset.mem_biUnion.mpr ⟨u,(G.mem_neighborFinset _ _).mpr au,
      Finset.mem_image.mpr ⟨v,(G.mem_neighborFinset _ _).mpr uv,rfl⟩⟩
  have sub : Ustar G C ⊆ M.biUnion B := by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
      intro edge
      obtain ⟨p,mp,x,y,hx,hy,adj⟩ := cover u v edge
      have uv : G.Adj u v := G.mem_edgeFinset.mp (Finset.mem_sdiff.mp edge).1
      apply Finset.mem_biUnion.mpr
      refine ⟨p,mp,Finset.mem_union.mpr ?_⟩
      change x=u ∨ x=v at hx
      rcases hx with rfl|rfl <;> rcases hy with rfl|rfl
      · exact Or.inl (found _ _ _ adj.symm uv)
      · exact Or.inr (found _ _ _ adj.symm uv)
      · exact Or.inl (Sym2.eq_swap ▸ found _ _ _ adj.symm uv.symm)
      · exact Or.inr (Sym2.eq_swap ▸ found _ _ _ adj.symm uv.symm)
  have cost (p) (hp : p ∈ M) : (B p).card ≤ 2*C.size := by
    have adj : G.Adj p.1 p.2 := G.mem_edgeFinset.mp (Finset.mem_sdiff.mp (active p hp)).1
    have a := watched_count G hg p.1 ⟨p.2,adj⟩
    have b := watched_count G hg p.2 ⟨p.1,adj.symm⟩
    have t := PEqualNP.Outside.L_meta_2074 n G C least
    exact (Finset.card_union_le _ _).trans (by omega)
  calc
    _ ≤ _ := Finset.card_le_card sub
    _ ≤ ∑ p ∈ M, (B p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ M, 2*C.size := Finset.sum_le_sum cost
    _ = M.card*(2*C.size) := by simp
    _ ≤ _ := (Nat.mul_le_mul_right _ hM).trans_eq (by ring)

#print axioms linear_in_junk
end Simlowker.Types1735

/-! ## Independent sets in a sparse conflict graph -/

namespace Simlowker.Types1735
open SimpleGraph

theorem independent_density {m r : Nat} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj]
    (hr : 0 < r) (cap : ∀ I : Finset (Fin m), H.IsIndepSet (I : Set (Fin m)) → I.card ≤ r) :
    m^2 ≤ r*(m+2*H.edgeFinset.card) := by
  classical
  have free : Hᶜ.CliqueFree (r+1) := by
    intro I h
    have b := cap I ((H.isClique_compl).mp h.1)
    have q := h.2
    omega
  have t := (Nat.mul_le_mul_left (2*r) free.card_edgeFinset_le).trans SimpleGraph.mul_turanNumber_le
  simp only [Fintype.card_fin] at t
  have dis : Disjoint H.edgeFinset Hᶜ.edgeFinset := by
    apply Finset.disjoint_left.mpr
    intro e
    induction e using Sym2.inductionOn with
    | _ x y =>
      intro h hc
      have hx : H.Adj x y := H.mem_edgeFinset.mp h
      have hc' : Hᶜ.Adj x y := Hᶜ.mem_edgeFinset.mp hc
      exact hc'.2 hx
  have all : H.edgeFinset ∪ Hᶜ.edgeFinset = (⊤ : SimpleGraph (Fin m)).edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | _ x y =>
      simp only [Finset.mem_union,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,SimpleGraph.compl_adj,SimpleGraph.top_adj]
      by_cases h : H.Adj x y
      · simp [h,h.ne]
      · simp [h]
  have nd := Finset.card_union_of_disjoint dis
  rw [all] at nd
  have total := (⊤ : SimpleGraph (Fin m)).sum_degrees_eq_twice_card_edges
  have deg (v : Fin m) : (⊤ : SimpleGraph (Fin m)).degree v = m-1 := by
    have nei : (⊤ : SimpleGraph (Fin m)).neighborFinset v = Finset.univ.erase v := by
      ext w
      simp [ne_comm]
    rw [← SimpleGraph.card_neighborFinset_eq_degree,nei,Finset.card_erase_of_mem (Finset.mem_univ v)]
    simp
  simp only [deg,Fintype.card_fin,Finset.sum_const,Finset.card_univ,Nat.nsmul_eq_mul] at total
  rw [nd] at total
  rcases m with _|m
  · simp
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
    simp at total t ⊢
    nlinarith [congrArg (fun z => (k+1)*z) total]

theorem matching_arithmetic {m r e : Nat} (hr : 0 < r) (density : m^2 ≤ r*(m+2*e))
    (girth : (2*e)^2 ≤ (2*m)^3) : m ≤ 32*r^2 := by
  by_cases sm : m ≤ 2*r
  · have one : 1 ≤ r := hr
    nlinarith [Nat.mul_le_mul_left r one]
  have st : 2*r ≤ m := by omega
  have half : m^2 ≤ 2*r*(2*e) := by nlinarith [Nat.mul_le_mul_right m st]
  have square := Nat.pow_le_pow_left half 2
  have tot : m^4 ≤ (32*r^2)*m^3 := by
    nlinarith [Nat.mul_le_mul_left (4*r^2) girth]
  have pos : 0 < m^3 := pow_pos (by omega) _
  exact Nat.le_of_mul_le_mul_right (show m*m^3 ≤ (32*r^2)*m^3 by nlinarith only [tot]) pos

#print axioms independent_density
#print axioms matching_arithmetic
end Simlowker.Types1735

/-! ## The size of an ordinary residual matching -/

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
namespace Simlowker.Types1735
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

def touches (p q : VertexPair n) := ∃ x, endpoint p x ∧ endpoint q x

theorem ordinary_bound {m : Nat} (hg : ∀ a : Fin n, ∀ p : G.Walk a a, p.IsCycle → 5 ≤ p.length)
    (least : IsLeastAO G C) (top : TopForm G C) (f : Fin m → VertexPair n)
    (edge : ∀ i, s((f i).1,(f i).2) ∈ Ustar G C)
    (dis : ∀ i j, i ≠ j → ¬touches (f i) (f j)) :
    m ≤ 32*(2*(junk G C).card)^2 := by
  classical
  by_cases zero : m=0
  · simp [zero]
  have hm : 0 < m := by omega
  let H : SimpleGraph (Fin m) := {
    Adj := fun i j => i≠j ∧ conflict G (f i) (f j)
    symm := ⟨fun _ _ h => ⟨h.1.symm,conflict_sym G _ _ h.2⟩⟩
    loopless := ⟨fun _ h => h.1 rfl⟩ }
  let r := 2*(junk G C).card
  have cap (I : Finset (Fin m)) (ind : H.IsIndepSet (I : Set (Fin m))) : I.card ≤ r := by
    let e : Fin I.card ≃ {i // i ∈ I} := (Fintype.equivFinOfCardEq (Fintype.card_coe I)).symm
    apply matching_junk G C least top (fun k => (f (e k).val).1) (fun k => (f (e k).val).2)
      (fun _ => edge _)
    intro k l diff x y hx hy adj
    have kl : (e k).val ≠ (e l).val := fun eq => diff (e.injective (Subtype.ext eq))
    exact ind (e k).property (e l).property kl ⟨kl,x,y,hx,hy,adj⟩
  have hr : 0 < r := by
    let i : Fin m := ⟨0,hm⟩
    have one := cap {i} (by intro x hx y hy ne; simp_all)
    rw [Finset.card_singleton] at one
    omega
  let W := Finset.univ.image (fun i => (f i).1) ∪ Finset.univ.image (fun i => (f i).2)
  have incl {i : Fin m} {x : Fin n} (h : endpoint (f i) x) : x ∈ W := by
    rcases h with eq|eq
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,eq.symm⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,eq.symm⟩))
  let owner (x : Fin n) := if h : ∃ i, endpoint (f i) x then Classical.choose h else (⟨0,hm⟩ : Fin m)
  have own {i : Fin m} {x : Fin n} (h : endpoint (f i) x) : owner x = i := by
    have h' : ∃ i, endpoint (f i) x := ⟨i,h⟩
    simp only [owner,dite_eq_left h']
    by_contra no
    exact dis _ _ no ⟨x,Classical.choose_spec h',h⟩
  let D : SimpleGraph (Fin n) := {
    Adj := fun x y => G.Adj x y ∧ x ∈ W ∧ y ∈ W
    symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
    loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩ }
  have image : H.edgeFinset ⊆ D.edgeFinset.image (Sym2.map owner) := by
    intro z
    induction z using Sym2.inductionOn with
    | _ i j =>
      intro mem
      have link : H.Adj i j := H.mem_edgeFinset.mp mem
      obtain ⟨x,y,hx,hy,xy⟩ := link.2
      refine Finset.mem_image.mpr ⟨s(x,y),D.mem_edgeFinset.mpr ⟨xy,incl hx,incl hy⟩,?_⟩
      change s(owner x,owner y) = _
      rw [own hx,own hy]
  have count := (Finset.card_le_card image).trans Finset.card_image_le
  have support : D.support.ncard ≤ 2*m := by
    have small : D.support ⊆ (W : Set (Fin n)) := fun x ⟨y,xy⟩ => xy.2.1
    have c := Set.ncard_le_ncard small
    have d := Finset.card_union_le (Finset.univ.image (fun i => (f i).1)) (Finset.univ.image (fun i => (f i).2))
    have ca : (Finset.univ.image (fun i => (f i).1)).card ≤ m := by simpa using
      (Finset.card_image_le (s := Finset.univ) (f := fun i => (f i).1))
    have cb : (Finset.univ.image (fun i => (f i).2)).card ≤ m := by simpa using
      (Finset.card_image_le (s := Finset.univ) (f := fun i => (f i).2))
    simp only [Set.ncard_coe_finset] at c
    dsimp only [W] at c
    omega
  obtain ⟨tri,sq⟩ := Simlowker.Residual1735.girth_local G hg
  have bound := Simlowker.Residual1735.global_degree D (fun a b c ab ac bc => tri a b c ab.1 ac.1 bc.1)
    (fun u v x y ne ux vx uy vy => sq u v x y ne ux.1 vx.1 uy.1 vy.1)
  have power : (2*H.edgeFinset.card)^2 ≤ (2*m)^3 := by
    calc
      _ ≤ (2*D.edgeFinset.card)^2 := Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 count) 2
      _ ≤ _ := bound
      _ ≤ (2*m)^2*(2*m) := Nat.mul_le_mul (Nat.pow_le_pow_left support 2) (by omega)
      _ = _ := by ring
  exact matching_arithmetic hr (independent_density H hr cap) power

#print axioms ordinary_bound
end Simlowker.Types1735

/-! ## Counting incidences with a vertex cover -/

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
namespace Simlowker.Types1735
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

theorem from_cover (four : NoFourCycle G) (Z : Finset (Fin n))
    (touch : ∀ u v, s(u,v) ∈ Ustar G C → u ∈ Z ∨ v ∈ Z) :
    (Ustar G C).card ≤ G.support.ncard + Z.card^2 := by
  classical
  let S := G.support.toFinset
  let B := fun x => (Z.filter (G.Adj x)).image (fun y => s(x,y))
  have sub : Ustar G C ⊆ S.biUnion B := by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
      intro edge
      have adj : G.Adj u v := G.mem_edgeFinset.mp (Finset.mem_sdiff.mp edge).1
      have mk (x y : Fin n) (xy : G.Adj x y) (hy : y ∈ Z) : s(x,y) ∈ S.biUnion B :=
        Finset.mem_biUnion.mpr ⟨x,Set.mem_toFinset.mpr ⟨y,xy⟩,Finset.mem_image.mpr
          ⟨y,Finset.mem_filter.mpr ⟨hy,xy⟩,rfl⟩⟩
      rcases touch u v edge with h|h
      · exact Sym2.eq_swap ▸ mk v u adj.symm h
      · exact mk u v adj h
  calc
    _ ≤ _ := Finset.card_le_card sub
    _ ≤ ∑ x ∈ S, (B x).card := Finset.card_biUnion_le
    _ ≤ ∑ x ∈ S, (Z.filter (G.Adj x)).card := Finset.sum_le_sum fun _ _ => Finset.card_image_le
    _ ≤ _ := by simpa only [S,Set.ncard_eq_toFinset_card'] using incidence_bound G four S Z

end Simlowker.Types1735

/-! ## A vertex cover and a fourth-power additive bound -/

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
namespace Simlowker.Types1735
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

theorem quadratic_cover (hg : ∀ a : Fin n, ∀ p : G.Walk a a, p.IsCycle → 5 ≤ p.length)
    (least : IsLeastAO G C) (top : TopForm G C) :
    ∃ Z : Finset (Fin n), Z.card ≤ 256*(junk G C).card^2 ∧
      ∀ u v, s(u,v) ∈ Ustar G C → u ∈ Z ∨ v ∈ Z := by
  classical
  let E := Finset.univ.filter fun p : VertexPair n => s(p.1,p.2) ∈ Ustar G C
  have sym {p q : VertexPair n} (h : touches p q) : touches q p := by
    obtain ⟨x,hx,hy⟩ := h
    exact ⟨x,hy,hx⟩
  obtain ⟨M,sub,sep,cover⟩ := maximal_apart touches (fun _ _ => sym) E
  let e : Fin M.card ≃ {p // p ∈ M} := (Fintype.equivFinOfCardEq (Fintype.card_coe M)).symm
  have size := ordinary_bound G C hg least top (fun i => (e i).val)
    (fun i => (Finset.mem_filter.mp (sub (e i).property)).2)
    (fun i j diff => sep _ (e i).property _ (e j).property (fun eq => diff (e.injective (Subtype.ext eq))))
  let Z := M.image Prod.fst ∪ M.image Prod.snd
  have count : Z.card ≤ 256*(junk G C).card^2 := by
    have a := Finset.card_image_le (s := M) (f := Prod.fst)
    have b := Finset.card_image_le (s := M) (f := Prod.snd)
    have c := Finset.card_union_le (M.image Prod.fst) (M.image Prod.snd)
    dsimp only [Z]
    nlinarith only [a,b,c,size]
  refine ⟨Z,count,?_⟩
  intro u v edge
  have found {p : VertexPair n} (hp : p ∈ M) {x : Fin n} (hx : endpoint p x) : x ∈ Z := by
    rcases hx with eq|eq
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨p,hp,eq.symm⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨p,hp,eq.symm⟩))
  obtain ⟨p,mp,eq|touch⟩ := cover (u,v) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,edge⟩)
  · subst p
    exact Or.inl (found mp (Or.inl rfl))
  · obtain ⟨x,hx,hy⟩ := touch
    change x=u ∨ x=v at hx
    rcases hx with h|h
    · exact Or.inl (h ▸ found mp hy)
    · exact Or.inr (h ▸ found mp hy)

theorem quartic_remainder (hg : ∀ a : Fin n, ∀ p : G.Walk a a, p.IsCycle → 5 ≤ p.length)
    (least : IsLeastAO G C) (top : TopForm G C) :
    (Ustar G C).card ≤ C.size+1 + 65536*(junk G C).card^4 := by
  obtain ⟨Z,count,touch⟩ := quadratic_cover G C hg least top
  apply (from_cover G C (girth_four G hg) Z touch).trans
  apply Nat.add_le_add (PEqualNP.Outside.L_meta_2074 n G C least)
  exact (Nat.pow_le_pow_left count 2).trans_eq (by ring)

#print axioms quartic_remainder
end Simlowker.Types1735
