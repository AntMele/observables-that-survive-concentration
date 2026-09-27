import Fluctuations.PauliBrickworkCircuit

namespace Fluctuations

lemma brickworkGateSchedule_add (c s r : ℕ) :
    brickworkGateSchedule c (s+r) = brickworkGateSchedule c s ++ brickworkGateSchedule c r := by
  induction r with
  | zero => simp [brickworkGateSchedule]
  | succ r ih =>
    change brickworkGateSchedule c (s+r) ++ brickworkBlock c =
      brickworkGateSchedule c s ++ (brickworkGateSchedule c r ++ brickworkBlock c)
    rw [ih, List.append_assoc]

lemma brickworkGateSchedule_period_split (c T s : ℕ) (hs : s < T) :
    brickworkGateSchedule c T = brickworkGateSchedule c s ++
      brickworkBlock c ++ brickworkGateSchedule c (T-s-1) := by
  have hT : T = (s+1)+(T-s-1) := by omega
  conv_lhs => rw [hT, brickworkGateSchedule_add, brickworkGateSchedule]

private lemma take_append_length_add {α : Type*} (l r : List α) (n : ℕ) :
    (l ++ r).take (l.length+n) = l ++ r.take n := by
  rw [List.take_append, List.take_of_length_le (Nat.le_add_right _ _)]
  simp

private lemma drop_append_length_add {α : Type*} (l r : List α) (n : ℕ) :
    (l ++ r).drop (l.length+n) = r.drop n := by
  rw [List.drop_append, List.drop_eq_nil_of_le (Nat.le_add_right _ _)]
  simp

/-- The gates strictly before the selected even gate consist of all preceding
periods, the current odd layer, and the earlier bonds of the current even layer. -/
theorem brickworkGateSchedule_take_even (c T s : ℕ) (hs : s < T) (a : Fin c) :
    (brickworkGateSchedule c T).take (s*(2*c+1)+(c+1)+a.val) =
      brickworkGateSchedule c s ++ brickworkOddBonds c ++ (brickworkEvenBonds c).take a.val := by
  rw [brickworkGateSchedule_period_split c T s hs, brickworkBlock]
  simp only [List.append_assoc]
  have hn : s*(2*c+1)+(c+1)+a.val =
      (brickworkGateSchedule c s).length + ((brickworkOddBonds c).length+a.val) := by
    simp [brickworkOddBonds]
    omega
  rw [hn, take_append_length_add, take_append_length_add,
    List.take_append_of_le_length (by simp only [brickworkEvenBonds,List.length_ofFn]; omega)]

/-- The gates strictly after the selected even gate consist of the later bonds
of its even layer and all subsequent complete periods. -/
theorem brickworkGateSchedule_drop_even (c T s : ℕ) (hs : s < T) (a : Fin c) :
    (brickworkGateSchedule c T).drop (s*(2*c+1)+(c+1)+a.val+1) =
      (brickworkEvenBonds c).drop (a.val+1) ++ brickworkGateSchedule c (T-s-1) := by
  rw [brickworkGateSchedule_period_split c T s hs, brickworkBlock]
  simp only [List.append_assoc]
  have hn : s*(2*c+1)+(c+1)+a.val+1 =
      (brickworkGateSchedule c s).length + ((brickworkOddBonds c).length+(a.val+1)) := by
    simp [brickworkOddBonds]
    omega
  rw [hn, drop_append_length_add, drop_append_length_add,
    List.drop_append_of_le_length (by simp only [brickworkEvenBonds,List.length_ofFn]; omega)]

lemma list_take_getD_drop {α : Type*} (l : List α) (i : ℕ) (d : α) (hi : i < l.length) :
    l.take i ++ [l.getD i d] ++ l.drop (i+1) = l := by
  rw [List.getD_eq_getElem _ _ hi, List.append_assoc]
  change l.take i ++ (l[i] :: l.drop (i+1)) = l
  rw [List.getElem_cons_drop hi, List.take_append_drop]

/-- The complete chronological schedule split at the selected physical gate. -/
theorem brickworkGateSchedule_even_decomposition (c T s : ℕ) (hs : s < T) (a : Fin c) :
    (brickworkGateSchedule c s ++ brickworkOddBonds c ++ (brickworkEvenBonds c).take a.val) ++
      [brickworkEvenBond a] ++
      ((brickworkEvenBonds c).drop (a.val+1) ++ brickworkGateSchedule c (T-s-1)) =
        brickworkGateSchedule c T := by
  have hi : s*(2*c+1)+(c+1)+a.val < (brickworkGateSchedule c T).length := by
    rw [brickworkGateSchedule_length]
    have ha := a.isLt
    have hh := Nat.mul_le_mul_right (2*c+1) (show s+1 ≤ T by omega)
    nlinarith
  have h := list_take_getD_drop (brickworkGateSchedule c T)
    (s*(2*c+1)+(c+1)+a.val) (brickworkOddBond 0) hi
  have hg := brickworkCircuitBond_even c T s a hs
  change (brickworkGateSchedule c T).getD (s*(2*c+1)+(c+1)+a.val)
    (brickworkOddBond 0) = brickworkEvenBond a at hg
  rw [brickworkGateSchedule_take_even c T s hs a,
    brickworkGateSchedule_drop_even c T s hs a, hg] at h
  exact h

end Fluctuations
