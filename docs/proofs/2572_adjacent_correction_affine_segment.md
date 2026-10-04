Record 2572: adjacent correction cell and affine segment

Date: 2026-10-04.

Result: the correction-pair, sigma=-1/2 certificate extends from cell 2700
to cell 2701. The two-cell segment and the generic affine finite-sum
identity compile in Lean. This does not certify the full grid or RH.

1. Certified objects

The five generated modules reuse the correction boxes and centers of
2570, with coefficient error 1e-28. The left endpoint is the existing
2570 shared position 2701; only position 2702 is newly emitted.

The exact summand bounds are:

```text
+-----------+-----------------------------------+
| cell      | certified three-piece upper       |
+-----------+-----------------------------------+
| 2700      | 414652489 / 12500000000            |
| 2701      | 33454650339 / 1000000000000        |
| both      | 66626849459 / 1000000000000        |
+-----------+-----------------------------------+
```

These bound the signedJetUpper2539 / signedCurvatureUpper2539 summands
at correctionCoefficientCenter2570 and correctionCoefficientError2570.
They are not unconditional integral bounds for the exact interpolant:
its coefficient-membership premise remains open.

2. Batch algebra

correctionCellAffine_eq2572 proves the identity, for arbitrary real inputs:

S = h*C + 2*abs(sigma)*h*(J + C*h/2)
    + sigma^2*(h/2*(L+R) + C*h^3/12)
  = K1*C + K2*J + K3*(L+R).

Here h is cell width; C is curvature upper; J is midpoint first-derivative
upper; L and R are endpoint uppers; sigma is the exponential weight.
K1 = h + abs(sigma)*h^2 + sigma^2*h^3/12;
K2 = 2*abs(sigma)*h; K3 = sigma^2*h/2.

correctionCellAffine_sum2572 proves this factorization over any finite
number of cells, including zero. correctionCellAffine_sign2572 proves
that changing sigma from -1/2 to +1/2 preserves these algebraic weights
when the input numbers are held fixed. It does NOT identify the two
signs' analytic leaf values.

correctionProduction2700_le2572 and correctionProduction2701_le2572
connect the abstract expression to the existing production-grid
summands. correctionTwoCellSum_le2572 adds their certified bounds.

3. Generation defect and repair

The old literal replacement stopped only at a theorem declaration.
The aggregate definition between the L1 literal and the next theorem
was therefore deleted. The build correctly refused the resulting unknown
identifier. Replacement now stops at either a definition or a theorem,
requires exactly one match, and asserts that the intervening aggregate
definition is preserved byte-for-byte. The validator independently checks
that this definition exists exactly once.

The generator wraps emitted lines using the existing token-preserving
formatter. Validator rejection of stale cell tokens applies to declarations,
not the historical module description.

4. Evidence and limits

The dedicated audit build succeeded with 3947 jobs. Its 52 expected targets
use exactly propext, Classical.choice, and Quot.sound, with no sorryAx.
The root integration build succeeded with 4148 jobs. The Linux 2271
integration control passed 22 tests. The new 2572 files are not members
of the existing 2271 bound-input inventory; no hash refresh was needed.

Evidence files:
- ConnesWeilRH/Dev/C1RouteACorrectionTwoCellSegment2572.lean
- ConnesWeilRH/Dev/C1RouteACorrectionTwoCellSegment2572Audit.lean
- scripts/generate_correction_pair_2572.py
- scripts/validate_correction_pair_2572.py
- results/2572_generation_readback.json
- results/2572_correction_pair_validation.json
- build-logs/2572_segment_audit_pass.log
- build-logs/2572_root_integration.log
- build-logs/2572_strip_control.log

The new finite-sum identity is an algebraic batch brick, not a measured
full-grid speedup. Two neighboring cell prices do not bound the other
10238 cells, and the 2561 direct-second-derivative price is not the same
object as the 2562 decomposed price. Full-grid decomposed pricing,
full-grid certificate production, exact coefficient membership, producer
positivity and RH remain unproved by this record.

Next steps

1. Price the decomposed expression on the whole correction grid for both
signs, using the same owner and derivative conventions. Completion means
exact totals fit the registered pin; local-cell extrapolation is not enough.

2. Measure a small shared-endpoint batch without per-cell rational closure.
Completion means the open affine interface compiles and measured cost is
recorded; the finite-sum identity alone gives no timing guarantee.

3. Connect the actual interpolation solution to the coefficient boxes.
Completion means proving membership for that exact solution, not merely
choosing a rational point inside each box.
