import Fluctuations.HaarProcess
import Fluctuations.HaarSU4
import Fluctuations.HaarLocalVariance
import Fluctuations.QubitEmbedding

open MeasureTheory

namespace Fluctuations

section Circuit

variable {N : Type*} [Fintype N] [DecidableEq N] {m : ℕ}

/-- Successive independent gate blocks multiply on the left, matching the
paper's convention `U_(d+1) = W U_d`. -/
noncomputable def haarCircuitMatrix
    (E : ℕ → Fin m → Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix N N ℂ) :
    (d : ℕ) → GateHistory (SU4Block m) d → Matrix N N ℂ
  | 0, _ => 1
  | d + 1, p => haarBlockMatrix (E d) p.2 * haarCircuitMatrix E d p.1

lemma haarCircuitMatrix_continuous
    (E : ℕ → Fin m → Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix N N ℂ)
    (d : ℕ) : Continuous (haarCircuitMatrix E d) := by
  induction d with
  | zero => exact continuous_const
  | succ d ih =>
    exact ((haarBlockMatrix_continuous (E d)).comp continuous_snd).mul
      (ih.comp continuous_fst)

/-- The actual matrix-trace OTOC on the independently sampled circuit history. -/
noncomputable def haarCircuitOTOC
    (E : ℕ → Fin m → Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix N N ℂ)
    (ρ B M : Matrix N N ℂ) (k d : ℕ) : C(GateHistory (SU4Block m) d, ℂ) where
  toFun x := Matrix.trace
    (ρ * ((haarCircuitMatrix E d x).conjTranspose * B * haarCircuitMatrix E d x * M) ^ (2*k))
  continuous_toFun := by
    have hc := haarCircuitMatrix_continuous E d
    fun_prop

lemma haarCircuitOTOC_identity
    (E : ℕ → Fin m → Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix N N ℂ)
    (hE : ∀ d i, E d i 1 = 1) (ρ B M : Matrix N N ℂ) (k d : ℕ)
    (x : GateHistory (SU4Block m) d) :
    haarCircuitOTOC E ρ B M k (d+1) (x, 1) = haarCircuitOTOC E ρ B M k d x := by
  simp only [haarCircuitOTOC, ContinuousMap.coe_mk, haarCircuitMatrix,
    haarBlockMatrix_one (E d) (hE d), one_mul]

/-- Fixing the earlier history gives precisely the local matrix OTOC whose
Haar reverse-variance bound was proved from the raw gate polynomial space. -/
lemma haarCircuitOTOC_section
    (E : ℕ → Fin m → Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix N N ℂ)
    (ρ B M : Matrix N N ℂ) (k d : ℕ) (x : GateHistory (SU4Block m) d) :
    historySection (haarCircuitOTOC E ρ B M k (d+1)) x =
      haarLocalOTOC (E d) ρ B (haarCircuitMatrix E d x) M k := by
  ext g
  rw [haarLocalOTOC_apply]
  simp only [historySection, haarCircuitOTOC, ContinuousMap.coe_mk,
    haarCircuitMatrix, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

/-- Star-algebra homomorphisms preserve the unitary gate structure and include
the ordinary embedding of a gate tensored with an identity spectator. -/
noncomputable def unitaryHaarCircuitOTOC
    (E : ℕ → Fin m → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (ρ B M : Matrix N N ℂ) (k d : ℕ) : C(GateHistory (SU4Block m) d, ℂ) :=
  haarCircuitOTOC (fun d i => (E d i).toAlgHom.toLinearMap) ρ B M k d

end Circuit

/-- Theorem VI.14 for concrete independently sampled Haar SU(4) gate blocks.
There is no local reverse-variance, continuity, square-integrability, or feature
membership premise. The constant is chosen before the global matrix dimension,
the gate placements, the state, the observables, and the depth interval.
Each step adjoins the fixed number `m` of independent gates. -/
theorem haarCircuit_theorem_VI_14 (m k : ℕ) :
    ∃ η : ℝ, 0 < η ∧ ∀ (N : Type*) [Fintype N] [DecidableEq N]
      (E : ℕ → Fin m → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
      (ρ B M : Matrix N N ℂ),
      ∀ {a b : ℕ}, a < b →
      (1 / 2 : ℝ) ≤
        ‖(∫ x, unitaryHaarCircuitOTOC E ρ B M k b x ∂historyMeasure (su4Haar m) b) -
          ∫ x, unitaryHaarCircuitOTOC E ρ B M k a x ∂historyMeasure (su4Haar m) a‖ →
      ∀ (R : ℕ) {P : ℝ}, ((b - a : ℕ) : ℝ) ≤ P →
      ∃ d, a < d ∧ d ≤ b ∧ ∀ r : ℕ, r ≤ R →
        η * (η / (1 + η)) ^ R / (4 * P ^ 2) ≤
          complexVariance (historyMeasure (su4Haar m) (d + r))
            (unitaryHaarCircuitOTOC E ρ B M k (d + r)) := by
  obtain ⟨η, hη, hmain⟩ := history_theorem_VI_14 (su4Haar m)
    (polynomialFeatureSpace (rawSU4Features m) ((m + m) * (2*k))) (1 : SU4Block m)
  refine ⟨η, hη, ?_⟩
  intro N _ _ E ρ B M
  apply hmain (unitaryHaarCircuitOTOC E ρ B M k)
  · intro d x
    change historySection (haarCircuitOTOC _ _ _ _ _ _) x ∈ _
    rw [haarCircuitOTOC_section]
    exact haarLocalOTOC_mem _ _ _ _ _ _
  · intro d x
    exact haarCircuitOTOC_identity (fun d i => (E d i).toAlgHom.toLinearMap)
      (fun d i => (E d i).map_one) ρ B M k d x

end Fluctuations
