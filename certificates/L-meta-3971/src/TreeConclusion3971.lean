import Catalog3971
namespace PetersenNegated3971

def validRecord (i : Nat) :=
  let c := costOf i
  let b := boxOf i
  let p := smallPos i
  0<c ∧ c≤5 ∧ b<604 ∧ 0<bk b ∧ bk b≤c ∧ bm b<31 ∧ inside (wOf i) (br b) ∧
    (c≤4 → startAt c≤p ∧ p<startAt c+numberAt c ∧ smallId p=i)

theorem recordSound {i : Nat} (h : recordOK i=true) : validRecord i := by
  unfold validRecord inside
  exact of_decide_eq_true h

def AllJoins := ∀ k j : Nat, 0<k → k≤j → k+j≤5 → universalJoin k j

theorem classify_joins (a : universalJoin 1 1) (b : universalJoin 1 2) (c : universalJoin 1 3)
    (d : universalJoin 1 4) (e : universalJoin 2 2) (f : universalJoin 2 3) : AllJoins := by
  intro k j hk ord sz
  have cases' : (k=1 ∧ j=1) ∨ (k=1 ∧ j=2) ∨ (k=1 ∧ j=3) ∨ (k=1 ∧ j=4) ∨
      (k=2 ∧ j=2) ∨ (k=2 ∧ j=3) := by omega
  rcases cases' with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> assumption

theorem growAvail {n k v : Nat} (le' : n≤k) (h : available n v) : available k v := by
  obtain ⟨i,hi,eq,lo⟩ := h
  exact ⟨i,hi,eq,lo.trans le'⟩

theorem merged (records : ∀ i, i<19466 → validRecord i) (joins : AllJoins)
    (n m v u : Nat) (sz : n+m≤5) (hv : available n v) (hu : available m u) :
    available (n+m) (v &&& u) ∧ available (n+m) (v ||| u) := by
  obtain ⟨i,hi,rfl,vi⟩ := hv
  obtain ⟨j,hj,rfl,vj⟩ := hu
  have ordered (x y : Nat) (hx : x<19466) (hy : y<19466)
      (ord : costOf x≤costOf y) (sz' : costOf x+costOf y≤5) :
      available (costOf x+costOf y) (wOf x &&& wOf y) ∧ available (costOf x+costOf y) (wOf x ||| wOf y) := by
    obtain ⟨xp,_,_,_,_,_,_,locx⟩ := records x hx
    obtain ⟨yp,_,_,_,_,_,_,locy⟩ := records y hy
    obtain ⟨xl,xh,eqx⟩ := locx (by omega)
    obtain ⟨yl,yh,eqy⟩ := locy (by omega)
    have b := joins _ _ xp ord sz' (smallPos x-startAt (costOf x)) (smallPos y-startAt (costOf y))
      (by omega) (by omega)
    simpa only [Nat.add_sub_of_le xl,Nat.add_sub_of_le yl,eqx,eqy] using b
  rcases le_total (costOf i) (costOf j) with ij|ji
  · have h := ordered i j hi hj ij (by omega)
    exact ⟨growAvail (by omega) h.1,growAvail (by omega) h.2⟩
  · have h := ordered j i hj hi ji (by omega)
    rw [Nat.and_comm,Nat.or_comm]
    exact ⟨growAvail (by omega) h.1,growAvail (by omega) h.2⟩

theorem word_present (records : ∀ i, i<19466 → validRecord i) (joins : AllJoins) (t : Formula)
    (sz : t.leaves≤5) : available t.leaves (word t) := by
  induction t with
  | var v =>
    exact ⟨_,of_decide_eq_true (atoms_ok v)⟩
  | disj a b ha hb =>
    exact (merged records joins _ _ _ _ sz (ha (by change a.leaves+b.leaves≤5 at sz; omega))
      (hb (by change a.leaves+b.leaves≤5 at sz; omega))).2
  | conj a b ha hb =>
    exact (merged records joins _ _ _ _ sz (ha (by change a.leaves+b.leaves≤5 at sz; omega))
      (hb (by change a.leaves+b.leaves≤5 at sz; omega))).1

theorem matrixData (j : Fin 31) :
    (∀ v : Fin 13, v.val≠12 → valid 0 (wm j.val) (denom j.val) v=true) ∧
      0≤denom j.val ∧ total j.val=rect (wm j.val) ri ci := by
  fin_cases j
  · exact normal0
  · exact normal1
  · exact normal2
  · exact normal3
  · exact normal4
  · exact normal5
  · exact normal6
  · exact normal7
  · exact normal8
  · exact normal9
  · exact normal10
  · exact normal11
  · exact normal12
  · exact normal13
  · exact normal14
  · exact normal15
  · exact normal16
  · exact normal17
  · exact normal18
  · exact normal19
  · exact normal20
  · exact normal21
  · exact normal22
  · exact normal23
  · exact normal24
  · exact normal25
  · exact normal26
  · exact normal27
  · exact normal28
  · exact normal29
  · exact normal30

theorem tree_from_checks (records : ∀ i, i<19466 → recordOK i=true) (joins : AllJoins)
    (boxes : ∀ idx, idx<604 → checkBox (bk idx,bm idx,br idx)=true)
    (o t : Formula) (once : marked o=1)
    (fit : ∀ r : Fin 512, o.eval (outerValue t r.val)=edge r.val) :
    14<o.leaves-1+t.leaves := by
  by_contra! short
  have inner := small_inner o t once fit short
  obtain ⟨i,hi,eq,le'⟩ := word_present (fun i hi => recordSound (records i hi)) joins t inner
  obtain ⟨_,_,len,_,bound,jok,inc,_⟩ := recordSound (records i hi)
  let b := boxOf i
  let j := bm b
  obtain ⟨ordinary,pos,mass⟩ := matrixData ⟨j,jok⟩
  have room' := box_sound (boxes b len)
  rw [eq] at inc
  let k := total j - (14-(bk b : Int))*denom j - 1
  have caps (v : Fin 13) : capacity (wm j) t v (price (denom j) k v) := by
    by_cases special : v.val=12
    · have e : v=12 := Fin.ext special
      subst v
      exact room_cap t _ inc _ k room'
    · have h := ordinary v special
      dsimp only [valid] at h
      have eqy (r : Nat) : rowOut t r v=yes 0 r v := by simp [rowOut,yes,outerValue,outside,special]
      have eqn (r : Nat) : colOut t r v=no 0 r v := by simp [colOut,no,outerValue,outside,special]
      intro u sub
      simp only [eqy] at sub
      simp only [price,special,ite_false,eqn]
      split at h
      · rename_i he
        simp [List.isEmpty_iff.mp he,upper,pos]
      · exact of_decide_eq_true ((List.all_eq_true.mp h) u (List.mem_sublists.mpr sub))
  have ineq : (14-(t.leaves : Int))*denom j+k < rect (wm j) ri ci := by
    have base : bk b≤t.leaves := bound.trans le'
    have av : (14-(t.leaves : Int))≤14-(bk b : Int) := by omega
    have s := mul_le_mul_of_nonneg_right av pos
    change total j=rect (wm j) ri ci at mass
    change (14-(t.leaves : Int))*denom j ≤ (14-(bk b : Int))*denom j at s
    rw [←mass]
    change (14-(t.leaves : Int))*denom j+(total j-(14-(bk b : Int))*denom j-1) < total j
    omega
  exact (Nat.not_lt_of_ge short) (exclude o t _ _ _ pos fit once caps ineq)

end PetersenNegated3971
