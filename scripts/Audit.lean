import Fluctuations

/- Inspect the definitions at the assumption boundary and the complete final
statements, in addition to every main theorem's kernel axiom dependencies. -/
#print Fluctuations.complexVariance
#print Fluctuations.LocalReverseVariance
#check @Fluctuations.transition_window
#check @Fluctuations.theorem_VI_14
#check @Fluctuations.theorem_VI_14_interval
#check @Fluctuations.theorem_VI_14_family
#check @Fluctuations.haarLocalOTOC_reverseVariance_identity
#check @Fluctuations.haarLocalOTOC_conditional_reverseVariance
#check @Fluctuations.haarCircuit_theorem_VI_14

#print axioms Fluctuations.complex_total_variance
#print axioms Fluctuations.norm_mean_sq_le_secondMoment
#print axioms Fluctuations.slope_to_variance
#print axioms Fluctuations.forward_persistence
#print axioms Fluctuations.exists_large_increment
#print axioms Fluctuations.transition_window
#print axioms Fluctuations.theorem_VI_14
#print axioms Fluctuations.theorem_VI_14_interval
#print axioms Fluctuations.theorem_VI_14_family
#print axioms Fluctuations.finiteDimensional_reverseVariance
#print axioms Fluctuations.su4Haar_independent
#print axioms Fluctuations.matrixBlockOTOC_mem
#print axioms Fluctuations.matrixBlockOTOC_apply
#print axioms Fluctuations.qubitEmbedding
#print axioms Fluctuations.qubitEmbedding_injective
#print axioms Fluctuations.starAlgHom_su4_mem_unitary
#print axioms Fluctuations.product_condExp
#print axioms Fluctuations.product_localReverseVariance
#print axioms Fluctuations.haarLocalConstant_pos
#print axioms Fluctuations.haarLocalOTOC_reverseVariance_identity
#print axioms Fluctuations.haarLocalOTOC_conditional_reverseVariance
#print axioms Fluctuations.history_transition_window
#print axioms Fluctuations.history_theorem_VI_14
#print axioms Fluctuations.haarCircuit_theorem_VI_14
