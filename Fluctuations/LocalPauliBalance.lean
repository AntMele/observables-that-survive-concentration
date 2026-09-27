import Fluctuations.PauliLocalHaar

open scoped BigOperators

namespace Fluctuations

lemma twoQubitPauliCoefficient_norm_sq_eq (U : TwoQubitUnitary) (p q : TwoQubitPauliLabel) :
    ‖twoQubitPauliCoefficient p q U‖ ^ 2 = twoQubitPauliTransfer U q p ^ 2 := by
  rw [← twoQubitPauliTransfer_cast, Complex.norm_real, Real.norm_eq_abs, sq_abs]

@[simp] lemma twoQubitPauliTransfer_zero_input (U : TwoQubitUnitary) (q : TwoQubitPauliLabel) :
    twoQubitPauliTransfer U q (0, 0) = if q = (0, 0) then 1 else 0 := by
  simp only [twoQubitPauliTransfer, twoQubitPauliCoefficient_zero_input]
  split_ifs <;> rfl

@[simp] lemma twoQubitPauliTransfer_zero_output (U : TwoQubitUnitary) (p : TwoQubitPauliLabel) :
    twoQubitPauliTransfer U (0, 0) p = if p = (0, 0) then 1 else 0 := by
  simp only [twoQubitPauliTransfer, twoQubitPauliCoefficient_zero_output]
  split_ifs <;> rfl

lemma localPauliA_eq_transfer (U : TwoQubitUnitary) :
    localPauliA U = (1 / 3 : ℝ) * ∑ α : Fin 3, ∑ γ : Fin 4, ∑ δ : Fin 3,
      twoQubitPauliTransfer U (γ, δ.succ) (α.succ, 0) ^ 2 := by
  simp only [localPauliA, ContinuousMap.coe_mk, twoQubitPauliCoefficient_norm_sq_eq]

/-- Average right-output weight of the twelve right-nonidentity inputs. -/
noncomputable def localPauliB (U : TwoQubitUnitary) : ℝ :=
  (1 / 12 : ℝ) * ∑ α : Fin 4, ∑ β : Fin 3, ∑ γ : Fin 4, ∑ δ : Fin 3,
    twoQubitPauliTransfer U (γ, δ.succ) (α, β.succ) ^ 2

lemma sum_twoQubitPauliLabel_split (f : TwoQubitPauliLabel → ℝ) :
    (∑ p, f p) = f (0, 0) + (∑ α : Fin 3, f (α.succ, 0)) +
      ∑ α : Fin 4, ∑ β : Fin 3, f (α, β.succ) := by
  rw [Fintype.sum_prod_type]
  have h (α : Fin 4) : (∑ β : Fin 4, f (α, β)) =
      f (α, 0) + ∑ β : Fin 3, f (α, β.succ) := Fin.sum_univ_succ _
  simp_rw [h]
  rw [Finset.sum_add_distrib, Fin.sum_univ_succ (fun α : Fin 4 => f (α, 0))]

/-- The exact local balance identity follows from the actual orthogonal
Pauli transfer matrix, including its fixed identity sector. -/
theorem localPauliB_eq_one_sub_quarter_A (U : TwoQubitUnitary) :
    localPauliB U = 1 - localPauliA U / 4 := by
  have hrow (γ : Fin 4) (δ : Fin 3) :
      (∑ α : Fin 3, twoQubitPauliTransfer U (γ, δ.succ) (α.succ, 0) ^ 2) +
        (∑ α : Fin 4, ∑ β : Fin 3,
          twoQubitPauliTransfer U (γ, δ.succ) (α, β.succ) ^ 2) = 1 := by
    have h := twoQubitPauliTransfer_row_sq (γ, δ.succ) U
    rw [sum_twoQubitPauliLabel_split] at h
    simpa using h
  have htotal : (∑ γ : Fin 4, ∑ δ : Fin 3,
      ((∑ α : Fin 3, twoQubitPauliTransfer U (γ, δ.succ) (α.succ, 0) ^ 2) +
      (∑ α : Fin 4, ∑ β : Fin 3,
        twoQubitPauliTransfer U (γ, δ.succ) (α, β.succ) ^ 2))) = 12 := by
    simp_rw [hrow]
    norm_num
  simp only [Finset.sum_add_distrib] at htotal
  have ha : (∑ γ : Fin 4, ∑ δ : Fin 3, ∑ α : Fin 3,
      twoQubitPauliTransfer U (γ, δ.succ) (α.succ, 0) ^ 2) = 3 * localPauliA U := by
    rw [localPauliA_eq_transfer]
    have he : (∑ γ : Fin 4, ∑ δ : Fin 3, ∑ α : Fin 3,
        twoQubitPauliTransfer U (γ, δ.succ) (α.succ, 0) ^ 2) =
        ∑ α : Fin 3, ∑ γ : Fin 4, ∑ δ : Fin 3,
          twoQubitPauliTransfer U (γ, δ.succ) (α.succ, 0) ^ 2 := by
      conv_lhs =>
        arg 2
        ext γ
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    rw [he]
    ring
  have hb : (∑ γ : Fin 4, ∑ δ : Fin 3, ∑ α : Fin 4, ∑ β : Fin 3,
      twoQubitPauliTransfer U (γ, δ.succ) (α, β.succ) ^ 2) = 12 * localPauliB U := by
    unfold localPauliB
    have he : (∑ γ : Fin 4, ∑ δ : Fin 3, ∑ α : Fin 4, ∑ β : Fin 3,
        twoQubitPauliTransfer U (γ, δ.succ) (α, β.succ) ^ 2) =
        ∑ α : Fin 4, ∑ β : Fin 3, ∑ γ : Fin 4, ∑ δ : Fin 3,
          twoQubitPauliTransfer U (γ, δ.succ) (α, β.succ) ^ 2 := by
      calc
        _ = ∑ γ : Fin 4, ∑ α : Fin 4, ∑ δ : Fin 3, ∑ β : Fin 3,
            twoQubitPauliTransfer U (γ, δ.succ) (α, β.succ) ^ 2 := by
          apply Finset.sum_congr rfl
          intro γ _
          rw [Finset.sum_comm]
        _ = ∑ α : Fin 4, ∑ γ : Fin 4, ∑ δ : Fin 3, ∑ β : Fin 3,
            twoQubitPauliTransfer U (γ, δ.succ) (α, β.succ) ^ 2 := Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro α _
          conv_lhs =>
            arg 2
            ext γ
            rw [Finset.sum_comm]
          rw [Finset.sum_comm]
    rw [he]
    ring
  rw [ha, hb] at htotal
  linarith

end Fluctuations
