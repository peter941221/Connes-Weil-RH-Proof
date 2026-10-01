2346 - Global second derivative of the corrected physical owner

Date: 2026-10-01.

Proof mechanism

A support is the set of positions where a function can be nonzero. Record 2345
proved the interior derivative formula. This record extends it to both support
boundaries and the exterior, without evaluating a singular interior formula
at an edge.

Outside the support, the function is locally zero, so its first and second
derivatives are zero. The existing smooth glued bump makes the second
derivative continuous. Its zero set is closed, so the zero value extends
from each open exterior half-line to its boundary. This covers both signs.

The resulting familySecondValue2346 is a piecewise formula: the certified
interior factor inside, zero at and outside the boundary. Differentiation
commutes with the finite sum of 30 smooth families. The final theorem uses
exact storedWidth squared radii and applies directly to correctedPhysical,
with arbitrary coefficient and modulation vectors.

```text
abs(x) < radius   -> family value times second factor
abs(x) = radius   -> zero by continuity from exterior
abs(x) > radius   -> zero by local constancy
all 30 families   -> finite sum of those second derivatives
```

Validation

Focused Linux build completes 3710 build-plan jobs. Six audited theorem leaves
have exactly [propext, Classical.choice, Quot.sound]. Both Lean source hashes
match the Windows workspace and Linux mirror. The unchanged 2342 evaluator
selftests pass 15/15, including support-edge zero checks and independent
mpmath value/derivative checks; these tests are not a program-semantics proof.

Evidence: results/2346_external_owner_zero_extension_validation.json and
build-logs/2346_external_owner_zero_extension_build_final.log.

Remaining obligations

This is a symbolic analytic theorem, not a proof of the Python interpreter,
Arb/Acb execution semantics, coefficient realization, quadrature bounds,
or endpoint numerical facts. The selected detector health and complete
signed physical-kernel budget remain open. No producer GO or RH claim.

Next steps

1. Formalize the one-sided complex chord-panel inequality. It converts finitely
   many node upper bounds and a second-derivative bound into an integral upper
   bound. Completion requires a Lean theorem with explicit smoothness and grid
   hypotheses, without differentiating a complex modulus.

2. Bind the program derivative fields to this whole-line expression and the
   exact coefficient realization. Completion requires an implementation or
   certificate bridge, not only matching sample values.

3. Import the actual endpoint inequalities into the existing same-owner norm
   supplier, then continue the signed detector kernel budget. Norm bounds
   control magnitude, so this step alone does not establish the required sign.
