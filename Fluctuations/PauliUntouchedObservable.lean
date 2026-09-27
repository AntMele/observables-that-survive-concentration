import Fluctuations.UniversalEndpointObservable
import Fluctuations.PauliPairCommutation

/-! Haar updates preserve observables supported at untouched sites. -/

open scoped BigOperators
namespace Fluctuations
noncomputable section

section Untouched
variable {Site : Type*} [DecidableEq Site]

lemma pauliPairEvolution_siteObservable (i j s : Site) (hsi : s ≠ i) (hsj : s ≠ j)
    (f : Fin 4 → ℝ) :
    pauliPairEvolution i j localPauliHaarKernel (fun P => f (P s)) = fun P => f (P s) := by
  funext P
  simp only [pauliPairEvolution, pauliPairReplace_apply_away i j s hsi hsj, ← Finset.sum_mul]
  have h : (∑ p, localPauliHaarKernel (P i,P j) p) = 1 := by
    simpa using pauliHaar_one_product (P i,P j)
  rw [h, one_mul]

variable [Fintype Site]

lemma pauliPairEvolution_untouched_expectation (i j s : Site)
    (hij : i ≠ j) (hsi : s ≠ i) (hsj : s ≠ j)
    (f : Fin 4 → ℝ) (w : (Site → Fin 4) → ℝ) :
    (∑ P, f (P s) * pauliPairEvolution i j localPauliHaarKernel w P) =
      ∑ P, f (P s) * w P := by
  rw [pauliPairEvolution_selfAdjoint i j hij,
    pauliPairEvolution_siteObservable i j s hsi hsj]

/-- The expectation of any one-site observable is unchanged by a layer whose
actual local Haar gates all miss that site. -/
theorem pauliLayerEvolution_untouched_expectation (bs : List (Site × Site))
    (s : Site) (hd : ∀ p ∈ bs, p.1 ≠ p.2)
    (hmiss : ∀ p ∈ bs, s ≠ p.1 ∧ s ≠ p.2)
    (f : Fin 4 → ℝ) (w : (Site → Fin 4) → ℝ) :
    (∑ P, f (P s) * pauliLayerEvolution bs w P) = ∑ P, f (P s) * w P := by
  induction bs generalizing w with
  | nil => rfl
  | cons p bs ih =>
    rcases p with ⟨i,j⟩
    rw [pauliLayerEvolution,
      ih (fun p hp => hd p (by simp [hp])) (fun p hp => hmiss p (by simp [hp])),
      pauliPairEvolution_untouched_expectation i j s (hd (i,j) (by simp))
        (hmiss (i,j) (by simp)).1 (hmiss (i,j) (by simp)).2]

end Untouched

/-- The circuit's final even layer leaves the last-site Z commutation sign
unchanged, for arbitrary incoming Pauli-string weights. -/
theorem brickworkEven_sign (c : ℕ) (w : (BrickworkSite c → Fin 4) → ℝ) :
    (∑ P, pauliEndpointSign (P (Fin.last c,1)) *
      pauliLayerEvolution (brickworkEvenBonds c) w P) =
      ∑ P, pauliEndpointSign (P (Fin.last c,1)) * w P := by
  apply pauliLayerEvolution_untouched_expectation
  · intro p hp
    have h := brickworkEvenBonds_adjacent c p hp
    intro he
    rw [he] at h
    omega
  · intro p hp
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hp
    constructor
    · intro he
      have hv := congrArg (fun s : BrickworkSite c => s.1.val) he
      have ha := a.isLt
      simp only [brickworkEvenBond, Fin.val_last, Fin.coe_castSucc] at hv
      omega
    · simp [brickworkEvenBond]

/-- Universal endpoint-chain formula with the physical final even layer included. -/
theorem brickworkIterateOddEven_sign (c n : ℕ)
    (w : (BrickworkSite c → Fin 4) → ℝ) :
    (∑ P, pauliEndpointSign (P (Fin.last c,1)) *
      pauliLayerEvolution (brickworkEvenBonds c)
        ((brickworkPeriod c)^[n] (pauliLayerEvolution (brickworkOddBonds c) w)) P) =
      (∑ P, w P) - (16/15 : ℝ) *
        (endpointMarkov c ^ n).mulVec (brickworkEndpointCellMass w) (Fin.last c) := by
  rw [brickworkEven_sign, brickworkIterateOdd_sign]

end
end Fluctuations
