import OneNot3971
namespace PetersenNegated3971

def rawWords : List Nat := [219161609, 9135472659, 5436899366, 27592772, 1613103752, 3241672976, 10900996256, 13119783744, 16911436800, 16920103955, 0, 17179869183, 0]
def word : Formula → Nat
  | .var j => rawWords.getD j.val 0
  | .disj a b => word a ||| word b
  | .conj a b => word a &&& word b

theorem positive_bits (t : Formula) (i : Nat) (hi : i∈ri) :
    (word t).testBit i=t.eval (leafValue (positive.getD i 0)) := by
  induction t with
  | var j =>
    exact (show ∀ i∈ri, ∀ v : Fin 13, (rawWords.getD v.val 0).testBit i = leafValue (positive.getD i 0) v by decide +kernel) i hi j
  | disj a b ha hb => simp only [word,Formula.eval,Nat.testBit_or,ha,hb]
  | conj a b ha hb => simp only [word,Formula.eval,Nat.testBit_and,ha,hb]

theorem negative_bits (t : Formula) (i : Nat) (hi : i∈ci) :
    (word t).testBit (12+i)=t.eval (leafValue (negative.getD i 0)) := by
  induction t with
  | var j =>
    exact (show ∀ i∈ci, ∀ v : Fin 13, (rawWords.getD v.val 0).testBit (12+i) = leafValue (negative.getD i 0) v by decide +kernel) i hi j
  | disj a b ha hb => simp only [word,Formula.eval,Nat.testBit_or,ha,hb]
  | conj a b ha hb => simp only [word,Formula.eval,Nat.testBit_and,ha,hb]

def inside (a box : Nat) := (a ^^^ 4095) &&& box = (a ^^^ 4095)
def boxRows (box : Nat) := ri.filter (fun r => box.testBit r)
def boxCols (box : Nat) := ci.filter (fun c => box.testBit (12+c))
def room (w : Matrix) (box : Nat) (k : Int) :=
  ∀ u, u.Sublist (boxRows box) → upper w u (boxCols box)≤k

theorem inside_bit {a box q : Nat} (h : inside a box) (hit : (a ^^^ 4095).testBit q=true) :
    box.testBit q=true := by
  have eq := congrArg (fun n : Nat => n.testBit q) h
  change ((a ^^^ 4095) &&& box).testBit q = (a ^^^ 4095).testBit q at eq
  simpa only [Nat.testBit_and,hit,Bool.true_and] using eq

theorem upper_sub (w : Matrix) (u : List Nat) {a b : List Nat} (h : a.Sublist b) :
    upper w u a ≤ upper w u b := by
  induction h with
  | slnil => rfl
  | cons x h ih => simp only [upper,List.map_cons,List.sum_cons] at *; omega
  | cons_cons x h ih => simp only [upper,List.map_cons,List.sum_cons] at *; omega

theorem room_cap (t : Formula) (box : Nat) (hit : inside (word t) box) (w : Matrix) (k : Int)
    (cap : room w box k) : capacity w t 12 k := by
  have rows : (ri.filter fun r => rowOut t r 12).Sublist (boxRows box) := by
    apply variable_filter List.filter_sublist
    intro r hmem
    obtain ⟨hr,yes⟩ := List.mem_filter.mp hmem
    apply inside_bit hit
    have mask : (4095 : Nat).testBit r=true :=
      (show ∀ i∈ri, (4095 : Nat).testBit i=true by decide +kernel) _ hr
    rw [Nat.testBit_xor,positive_bits t r hr,mask]
    simpa [rowOut,outerValue,outside,invertSub] using yes
  have cols : (ci.filter fun c => !(colOut t c 12)).Sublist (boxCols box) := by
    apply variable_filter List.filter_sublist
    intro c hmem
    obtain ⟨hc,no⟩ := List.mem_filter.mp hmem
    apply inside_bit hit
    have mask : (4095 : Nat).testBit (12+c)=false :=
      (show ∀ i∈ci, (4095 : Nat).testBit (12+i)=false by decide +kernel) _ hc
    rw [Nat.testBit_xor,negative_bits t c hc,mask]
    simpa [colOut,outerValue,outside,invertSub] using no
  intro u sub
  exact (upper_sub w u cols).trans (cap u (sub.trans rows))

end PetersenNegated3971
