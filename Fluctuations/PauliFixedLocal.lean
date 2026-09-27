import Fluctuations.PauliShock
import Fluctuations.LocalPauliBalance

open scoped BigOperators
namespace Fluctuations
noncomputable section

def localPauliSquaredKernel (U : TwoQubitUnitary) (q p : TwoQubitPauliLabel) : ℝ :=
  twoQubitPauliTransfer U q p ^ 2

lemma localPauliSquared_identity (U : TwoQubitUnitary) (q : TwoQubitPauliLabel) :
    (∑ p, localPauliSquaredKernel U q p *
      (pauliIdentityWeight p.1 * pauliIdentityWeight p.2)) =
      pauliIdentityWeight q.1 * pauliIdentityWeight q.2 := by
  rcases q with ⟨q₁,q₂⟩
  simp [pauliIdentityWeight, localPauliSquaredKernel, Fintype.sum_prod_type]
  split_ifs <;> simp_all

lemma localPauliSquared_uniform (U : TwoQubitUnitary) (q : TwoQubitPauliLabel) :
    (∑ p, localPauliSquaredKernel U q p *
      (pauliUniformWeight p.1 * pauliUniformWeight p.2)) =
      pauliUniformWeight q.1 * pauliUniformWeight q.2 := by
  simp only [pauliUniformWeight, localPauliSquaredKernel, ← Finset.sum_mul,
    twoQubitPauliTransfer_row_sq]
  ring

def localPauliLeftLaw (U : TwoQubitUnitary) (q : TwoQubitPauliLabel) : ℝ :=
  ∑ p, localPauliSquaredKernel U q p * (pauliNonzeroWeight p.1 * pauliIdentityWeight p.2)

def localPauliRightLaw (U : TwoQubitUnitary) (q : TwoQubitPauliLabel) : ℝ :=
  ∑ p, localPauliSquaredKernel U q p * (pauliUniformWeight p.1 * pauliNonzeroWeight p.2)

lemma localPauliLeftLaw_eq (U : TwoQubitUnitary) (q : TwoQubitPauliLabel) :
    localPauliLeftLaw U q = (1/3 : ℝ) *
      ∑ α : Fin 3, twoQubitPauliTransfer U q (α.succ,0) ^ 2 := by
  simp [localPauliLeftLaw, localPauliSquaredKernel, Fintype.sum_prod_type,
    pauliNonzeroWeight, pauliIdentityWeight, Fin.sum_univ_succ]
  ring

lemma localPauliRightLaw_eq (U : TwoQubitUnitary) (q : TwoQubitPauliLabel) :
    localPauliRightLaw U q = (1/12 : ℝ) *
      ∑ α : Fin 4, ∑ β : Fin 3, twoQubitPauliTransfer U q (α,β.succ) ^ 2 := by
  simp [localPauliRightLaw, localPauliSquaredKernel, Fintype.sum_prod_type,
    pauliNonzeroWeight, pauliUniformWeight, Fin.sum_univ_succ]
  ring

@[simp] lemma localPauliLeftLaw_zero (U : TwoQubitUnitary) : localPauliLeftLaw U (0,0) = 0 := by
  simp [localPauliLeftLaw_eq]

@[simp] lemma localPauliRightLaw_zero (U : TwoQubitUnitary) : localPauliRightLaw U (0,0) = 0 := by
  simp [localPauliRightLaw_eq]

lemma localPauliLeftLaw_sum (U : TwoQubitUnitary) : (∑ q, localPauliLeftLaw U q) = 1 := by
  simp_rw [localPauliLeftLaw_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, twoQubitPauliTransfer_column_sq]
  norm_num

lemma localPauliRightLaw_sum (U : TwoQubitUnitary) : (∑ q, localPauliRightLaw U q) = 1 := by
  simp_rw [localPauliRightLaw_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset TwoQubitPauliLabel))]
  simp_rw [← Finset.mul_sum, twoQubitPauliTransfer_column_sq]
  norm_num

lemma localPauliLeftLaw_right (U : TwoQubitUnitary) :
    (∑ γ : Fin 4, ∑ δ : Fin 3, localPauliLeftLaw U (γ,δ.succ)) = localPauliA U := by
  calc
    _ = (1/3 : ℝ) * ∑ γ : Fin 4, ∑ δ : Fin 3, ∑ α : Fin 3,
        twoQubitPauliTransfer U (γ,δ.succ) (α.succ,0) ^ 2 := by
      simp only [localPauliLeftLaw_eq, Finset.mul_sum]
    _ = (1/3 : ℝ) * ∑ α : Fin 3, ∑ γ : Fin 4, ∑ δ : Fin 3,
        twoQubitPauliTransfer U (γ,δ.succ) (α.succ,0) ^ 2 := by
      apply congrArg (fun x : ℝ => (1/3 : ℝ) * x)
      calc
        _ = ∑ γ : Fin 4, ∑ α : Fin 3, ∑ δ : Fin 3,
            twoQubitPauliTransfer U (γ,δ.succ) (α.succ,0) ^ 2 := by
          apply Finset.sum_congr rfl
          intro γ _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := (localPauliA_eq_transfer U).symm

lemma localPauliRightLaw_right (U : TwoQubitUnitary) :
    (∑ γ : Fin 4, ∑ δ : Fin 3, localPauliRightLaw U (γ,δ.succ)) = localPauliB U := by
  calc
    _ = (1/12 : ℝ) * ∑ γ : Fin 4, ∑ δ : Fin 3, ∑ α : Fin 4, ∑ β : Fin 3,
        twoQubitPauliTransfer U (γ,δ.succ) (α,β.succ) ^ 2 := by
      simp only [localPauliRightLaw_eq, Finset.mul_sum]
    _ = _ := by
      unfold localPauliB
      apply congrArg (fun x : ℝ => (1/12 : ℝ) * x)
      have h := Finset.sum_comm (s := (Finset.univ : Finset (Fin 4 × Fin 3)))
        (t := (Finset.univ : Finset (Fin 4 × Fin 3)))
        (f := fun q p => twoQubitPauliTransfer U (q.1,q.2.succ) (p.1,p.2.succ) ^ 2)
      simpa only [Fintype.sum_prod_type] using h

lemma localPauliLeftLaw_left (U : TwoQubitUnitary) :
    (∑ γ : Fin 3, localPauliLeftLaw U (γ.succ,0)) = 1 - localPauliA U := by
  have h := localPauliLeftLaw_sum U
  rw [sum_twoQubitPauliLabel_split, localPauliLeftLaw_zero, localPauliLeftLaw_right] at h
  linarith

lemma localPauliRightLaw_left (U : TwoQubitUnitary) :
    (∑ γ : Fin 3, localPauliRightLaw U (γ.succ,0)) = 1 - localPauliB U := by
  have h := localPauliRightLaw_sum U
  rw [sum_twoQubitPauliLabel_split, localPauliRightLaw_zero, localPauliRightLaw_right] at h
  linarith

end
end Fluctuations
