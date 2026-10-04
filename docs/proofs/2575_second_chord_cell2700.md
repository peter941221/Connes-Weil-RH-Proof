Record 2575: kernel-checked second-chord cell at the correction pair

Verdict: the new second-integral method has a numerical cell certificate
at both signs, not only the generic inequality from 2574. It covers
production cell 2700, between nodes 2700 and 2701. Actual coefficient
membership remains an explicit premise. This is not a full-grid or RH
certificate.

Object and connection to the consumer

Let c be the correction physical function and W(x) = exp(sigma*x)*c(x).
Primes mean derivatives with respect to x. The 2574 composite uses signed
endpoint bounds on W'' and a whole-cell bound M on W''''. For cell width h:

  second-integral summand = h/2*(leftSecond + rightSecond) + M*h^3/12.

A chord connects two endpoint values by a straight line; the last term
pays for bending away from it. This second-integral method removes the
old unsigned third-variation charge without changing the coefficient
owner, 1e-28 error, modulations, support or grid.

The radius is R = 6.5536001 and h = 2*R/10240. Nodes 2700 and 2701 are
-R+2700*h and -R+2701*h. ProductionSummand_le states the upper in exactly
these coordinates. Integral_le bounds the actual norm(W'') integral
under norm(coefficient-center) <= error for each coefficient.

Numerical content

The endpoint bounds retain signed complex aggregation. The coefficient
centers come from the 2338 ideal_correction_coefficient rows. Evaluator
and point-rounding allowances are included in the checked bounds.

```text
+----------------------+-------------------+-------------------+
| quantity             | sigma = -1/2      | sigma = +1/2      |
+----------------------+-------------------+-------------------+
| node 2700 upper      | 24.36617014       | 1.11018474        |
| node 2701 upper      | 24.57376634       | 1.12106918        |
| endpoint trapezoid   | 0.03132155982513  | 0.00142800253059  |
| fourth remainder     | 0.00001559673659  | 0.00000070487219  |
| second-integral upper| 0.03133715656172  | 0.00142870740278  |
+----------------------+-------------------+-------------------+
```

Exact rationals are in results/2575_second_chord_generation.json and the
Lean definitions. The table is display-only. No full-grid estimate is
inferred by multiplying this cell by 10240. First/value channels of the
full strip-second decomposition are not included in these figures.

Generation and proof reuse

The generator calls the committed arbitrary-position/order renderer at
order 2 for four node/sign pairs. The signed order-2 midpoint renderer
already accepts these point positions. Correction-owner substitutions
obey the 2570 remainder guard and remove runtime base-owner tokens.
Six committed base modules reproduce byte-for-byte before new emission.

Ten Lean modules are emitted: derivative and signed-bound modules for
four node/sign pairs, an assembly, and its paired Audit module.
The assembly reuses the coefficient-independent 2558 fourth-envelope
certificates. Their definitions match weightedUnitFourthCellUpper2574.
It bounds the center norm by abs(real)+abs(imag) and closes the exact
30-term weighted fourth sum in Lean. This sum is not an assumed input.

Validation

The validator reads emitted rational literals, independently replays
exponent arithmetic and order-2 factors, checks support branches and
signed rounding, and verifies both 30-family fourth-envelope payloads.
External Arb point enclosures lie below all four certified point uppers.

Twelve mutations are rejected: zero factor, changed rounded value and
opposite sign, at each point. A repeated generation reproduces all ten
modules and its JSON byte-for-byte. The dedicated audit checks 154
expected targets on exactly [propext, Classical.choice, Quot.sound].
The mirror check covers the project import closure, not only new files.

Commands in a configured Linux workspace

  python scripts/generate_second_chord_cell_2575.py
  lake build ConnesWeilRH.Dev.C1RouteACorrectionSecondChordCell2700_2575Audit
  python scripts/validate_second_chord_cell_2575.py --log BUILD_LOG --mirror BUILD_WORKSPACE

BUILD_LOG denotes successful focused Lake output. BUILD_WORKSPACE denotes
the verification copy whose source bytes must match the main checkout.
They are parameters, not commands to paste unchanged.

Remaining obligations

This certificate covers the second-integral summand of one cell, both
signs. The full-grid totals, actual exact-interpolant membership, base
norm, producer GO and RH remain unproved. Before mass generation, measure
reuse of existing endpoint exponential traces and shared endpoints.
Then kernel-check the full-grid endpoint and fourth sums.

Evidence

  ConnesWeilRH/Dev/C1RouteACorrectionSecondChordCell2700_2575.lean
  ConnesWeilRH/Dev/C1RouteACorrectionSecondChordCell2700_2575Audit.lean
  scripts/generate_second_chord_cell_2575.py
  scripts/validate_second_chord_cell_2575.py
  results/2575_second_chord_generation.json
  results/2575_second_chord_validation.json
