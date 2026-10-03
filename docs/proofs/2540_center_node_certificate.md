Record 2540: exact coefficient boxes and production center-node certificate
Date: 2026-10-03

This certificate targets x=0, index 5120 of the existing 10240-cell grid.
At this node the oscillatory factors equal one and all bump factors equal
exp(-30). The proof preserves the signed sum of the 30 coefficients and
establishes a rational node upper. Nonzero-node complex exponentials and
whole-cell numerical curvature remain open.

Imported data and coefficient uncertainty

The generator reads the 120 exact rational endpoints in
results/2338_exact_interpolation_repair.json. It writes the real and imaginary
lower/upper endpoints for each of the 30 base coefficients into
baseCoefficientBox2540. It uses Fraction arithmetic, records the source
hash, and supports --check to compare the entire generated file with the
current input. Long integers use exact base-10 arithmetic to keep source
lines readable; there is no floating-point conversion.
The acceptance checker also parses the generated arithmetic independently
and compares all 120 resulting fractions with the original JSON endpoints.
A changed-endpoint control is rejected.

A rectangle here specifies the allowed real and imaginary parts of a
complex coefficient. Lean proves that its midpoint lies in the rectangle
and that any point in it is at distance at most 10^-30 from the midpoint.
The latter follows by adding the two coordinate half-widths. This radius
is deliberately larger than the Euclidean half-diagonal used externally
by 2535; the node bound charges it. It does not change the exact midpoints
or assert that the intended interpolation coefficients belong to the boxes.

Numerical derivation

Write C for the sum of the 30 actual coefficients. Assuming each coefficient
belongs to its imported box, exact rational addition gives

```text
147426599914317 <= Re(C) <= 147426599914319
   18836521581 <= Im(C) <=    18836521582
|C| <= |Re(C)| + |Im(C)| <= 147445436435901.
```

The signed component sums come first. The final two-component norm upper
therefore preserves cancellation among families. For comparison only, a
binary64 diagnostic gives a center-node norm near 13.7956255 and a sum of
separate family norms near 69.1932841; neither diagnostic enters the proof.

The existing Taylor theorem from 2498 bounds exp(-1). Raising that upper
to the 30th power gives the following Lean inequality, with its final
rational comparison checked by norm_num:

```text
exp(-30) <= 9358/100000000000000000.
```

The identity weightedPhysical_center_eq2540 holds for arbitrary real sigma
and signed modulations. Combining it with the coefficient-sum bound gives

```text
F(0) = C * exp(-30)
|F(0)| <= 6899/500 = 13.798.
```

Finally, signedJet_center_le2540 bounds the order-zero expression used by
2539 at the exact box midpoints with error radius 10^-30 per coefficient.
The 30 coefficient-error terms cost at most 30*10^-30, since exp(-30)<=1.
The resulting unconditional numerical statement is

```text
signedJetUpper2539 0 sigma centers errors modulations 0 <= 69/5 = 13.8.
```

Here unconditional refers to this explicit midpoint-and-error expression.
Applying it to the exact interpolation function still requires coefficient
membership. The imported rectangles and the membership-to-ball theorem
expose that requirement rather than replacing it with the external solver's
status flag.

Validation and scope

The audit covers the coefficient sum, exponential upper, center identity,
actual-box node upper, membership-to-ball bound and signed-node upper. The
acceptance checker verifies the six standard-axiom reports, the audit/root
build, source identity, and regeneration of all 120 endpoints. The artifact
is results/2540_center_node_validation.json.
Final acceptance passed: 4504 build jobs, six standard-axiom leaves, 693
byte-identical project sources and 120 independently checked endpoints.
The new modules produced no warnings. Before acceptance, the source checker
detected one newline-only difference in an existing dependency; the matching
source was synchronized and the audit/root build repeated successfully.

This is one node certificate, not a full-grid or base-integral certificate.
The modulation disappears at x=0, so this result does not test oscillatory
evaluation away from zero. No correction-channel, selected-detector
positivity, Producer GO or RH claim follows from it.

Next steps

1. Certify a nonzero production node using rational complex-exponential
   approximations with proved error bounds. Preserve the complex sum before
   the norm and record the extra numerical allowance.
2. Certify the midpoint derivative and support-edge cases needed by the
   whole-cell curvature formula, then extend to segmented grid sums.
3. Prove exact interpolation-coefficient membership and discharge the other
   endpoint channels before assessing the complete signed margin.

Evidence:
ConnesWeilRH/Dev/C1RouteABaseCoefficientBoxes2540.lean
ConnesWeilRH/Dev/C1RouteACenterNode2540.lean
ConnesWeilRH/Dev/C1RouteACenterNode2540Audit.lean
scripts/generate_center_node_2540.py
scripts/validate_center_node_2540.py
results/2540_center_node_validation.json
