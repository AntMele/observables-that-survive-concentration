import Fluctuations.SimulationMixedCircuitCommutation

namespace Fluctuations
set_option linter.unusedSectionVars false
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- A finite physically indexed word of mixed calls is the same covariance
as the corresponding segment of the chronological circuit sampler. -/
theorem simulationMixedListEnsemble_ofFn_covariance
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (retained : ℕ → Bool) (gates : ℕ → TwoQubitUnitary) (P₀ : PauliString Site)
    (o m : ℕ) (word : Fin m → Site × Site)
    (rr : Site × Site → Bool) (gg : Site × Site → TwoQubitUnitary)
    (hw : ∀ i, word i = bond (o+i.val))
    (hr : ∀ i, rr (word i) = retained (o+i.val))
    (hg : ∀ i, gg (word i) = gates (o+i.val))
    (E : FiniteAmplitudeEnsemble (PauliString Site))
    (hE : E.covariance = (mixedPauliSampler bond hbond retained gates P₀ o).covariance) :
    (simulationMixedListEnsemble rr gg (List.ofFn word) E).covariance =
      (mixedPauliSampler bond hbond retained gates P₀ (o+m)).covariance := by
  induction m with
  | zero => simpa [simulationMixedListEnsemble] using hE
  | succ m ih =>
    rw [List.ofFn_succ_last,simulationMixedListEnsemble_append]
    change (simulationPairEnsembleStep (rr (word (Fin.last m))) (gg (word (Fin.last m)))
      (word (Fin.last m)) (simulationMixedListEnsemble rr gg
        (List.ofFn (fun i => word i.castSucc)) E)).covariance = _
    have hc := ih (fun i => word i.castSucc)
      (fun i => hw i.castSucc) (fun i => hr i.castSucc) (fun i => hg i.castSucc)
    rw [hr (Fin.last m),hg (Fin.last m),hw (Fin.last m)]
    simp only [Fin.val_last,simulationPairEnsembleStep,dif_pos (hbond (o+m)),Nat.add_succ,mixedPauliSampler]
    rw [pauliSamplerStep_covariance_local,pauliSamplerStep_covariance_local,hc]
    rfl

end Fluctuations
