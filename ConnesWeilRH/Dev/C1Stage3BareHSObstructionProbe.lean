import ConnesWeilRH.Dev.C1Stage3BareHSObstruction

open ConnesWeilRH.Source.C1Stage3BareHSObstruction

/-!
# Import-facing audit for the bare Hilbert--Schmidt obstruction

The obstruction is deliberately exposed as a small public surface.  The
`#print axioms` commands below are the proof audit: each declaration should
reduce to the Lean/mathlib baseline (`propext`, `Classical.choice`, and
`Quot.sound`) and must not introduce `sorryAx` or a project-local axiom.
-/

#check @norm_cutoffWindowPostcomp_le_one
#check @cutoffPositiveBasisData_operator_eq_postcomp
#check @cutoffEnergy_le_bareHS_mass
#check @not_bare_hilbertSchmidt_of_test_ne_zero
#check @not_forall_bare_hilbertSchmidt

#print axioms norm_cutoffWindowPostcomp_le_one
#print axioms cutoffPositiveBasisData_operator_eq_postcomp
#print axioms cutoffEnergy_le_bareHS_mass
#print axioms not_bare_hilbertSchmidt_of_test_ne_zero
#print axioms not_forall_bare_hilbertSchmidt
