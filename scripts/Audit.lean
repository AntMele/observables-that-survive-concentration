import Fluctuations

/- Inspect the definitions at the assumption boundary and the complete final
statements, in addition to every main theorem's kernel axiom dependencies. -/
#print Fluctuations.complexVariance
#print Fluctuations.LocalReverseVariance
#check @Fluctuations.transition_window
#check @Fluctuations.theorem_VI_14
#check @Fluctuations.theorem_VI_14_interval
#check @Fluctuations.theorem_VI_14_family

#print axioms Fluctuations.complex_total_variance
#print axioms Fluctuations.norm_mean_sq_le_secondMoment
#print axioms Fluctuations.slope_to_variance
#print axioms Fluctuations.forward_persistence
#print axioms Fluctuations.exists_large_increment
#print axioms Fluctuations.transition_window
#print axioms Fluctuations.theorem_VI_14
#print axioms Fluctuations.theorem_VI_14_interval
#print axioms Fluctuations.theorem_VI_14_family
