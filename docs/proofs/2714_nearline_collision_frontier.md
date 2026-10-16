# Record 2714: near-line collision frontier of the 2354-class consumer

**Verdict: FRONTIER PRICED, OBSTRUCTION NON-BINDING AT OPERATIONAL
SEPARATIONS.** In the committed record-2354 consumer class (q = 2^-52,
directed D4/D2 caps, N = 6, full multiplicity factor), the record-2713
collision floor starts defeating the correction-decay budget only below

```text
delta* = 1.0141e-16   at n = 2, any lambda >= 256
delta* = 2.2519e-32   at n = 3, lambda >= 4.0019e4 (record-2666 audit min)
```

where `delta = Re(rho) - 1/2`.  The fixed-window interpolation class can
therefore pay the existing tail certificate for every `delta > delta*`,
and the near-line quantifier adds NO binding constraint beyond the three
already-named obligations (gate witness, prefix completeness, source-zero
identity).  A scoped no-go survives only in `delta < 1e-16` at n = 2.
No producer GO, no family reopening, no RH claim.

## Task card (bounded-progress gate)

```text
consumer    riemannHypothesis_of_four_point_span_contradiction_producer,
            via the record-2708 contract P1-P5 + (G) + (T1)/(T2)
owner       exact compact-window base/correction of selectedOwner; the
            record-2713 explicit interpolation construction on the
            complete source-zero prefix node list
premise     near-line feasibility: whether any (C4,C2,q,n,s,lambda)
            satisfies joint acceptance as Re(rho) -> 1/2+
criterion   explicit delta* with committed-constant provenance, plus the
            verdict (candidate / scoped no-go)
budget      paper-arithmetic evaluation of committed constants only
            (record-2709 precedent); no build, no new Lean module, no
            measurement rig
stop        any required constant not on the books -> record the gap
```

## Conventions (the two lanes are different; kept explicit)

The record-2709 sensitivity scan reused the record-2033 stored convention
(`tau_q = A0 q^(2n) (1 + H^4/lambda)^2`, sampled C4/C2, unit-proxy
multiplicity factor).  The honest consumer is the record-2354 class:

```text
ratio(n, lambda) = (3/2)*4*K*(3/4)^N/m * L * (1 + L/lambda)^2
                   * (q^n * D4 * D2)^2          ratio < 1 sufficient
K <= 128.65 (C1RouteAMultiplicityBound; record 2354 explicitly does NOT
use the larger multProxy2248 = 128.70692502981), N = 6, m >= 1,
q = 2^-52 (2353 supplier cap at T = 128), D4 = 746785658244,
D2 = 71280628476, L = 44^4 (old) or d = 169/16 (record-2710 geometry).
```

Anchors: the script reproduces both committed lane ratios in-run
(relative <= 1.6e-13): `ratio_old(2, 256) = 0.7603893268553` and
`ratio_old(3, 1e-13) = 0.2456614834776`.  A first draft used
multProxy2248 as K and missed by 4.4e-4 relative - the anchor caught it;
record 2354's K is 128.65.

## Derivation (four lines)

With `C4 = D4/(2*pi)^4`, `C2 = D2/(2*pi)^2` and the exact cancellation
`(2*pi)^12 (q^n C4 C2)^2 = (q^n D4 D2)^2` (record 2354), the budget the
tail imposes on the correction decay is, under the record-2710 geometry,

```text
C2 < 1/((2*pi)^2 q^n D4 sqrt(W~ d) (1 + d/lambda)),
W~ = (3/2)*4*K*(3/4)^6/m = 137.3816162109375  (exact).
```

The record-2713 collision floor for target values `+1/-1` at the
companion nodes `(rho, 1-conjugate(rho))` (separation `2*delta`,
`|Delta y| = 2`, the strongest-floor case; the floor scales linearly in
`|Delta y|`) is `C2 >= 12/(delta * L_log)` with `L_log = 6.5536` the
conservative family max log-support radius.  Solving
`floor = budget`:

```text
delta* = 12 (2*pi)^2 q^n D4 sqrt(W~ d) (1 + d/lambda) / L_log.
```

## Readings (exact-rational ratios; artifact rows)

```text
+-------+-----------------+-------------------+--------------------+------------------+--------+
| n     | lambda corner   | ratio (old geom)  | ratio (new geom)   | delta* (new)     | pass   |
+-------+-----------------+-------------------+--------------------+------------------+--------+
| 1     | 256             | 1.542253e+31      | 2.198006e+17       | 4.754e-01        | NO     |
| 1     | 4.0019e4        | 6.445725e+26      | 2.028336e+17       | 4.567e-01        | NO     |
| 2     | 256 (lane edge) | 7.603893e-01      | 1.083701e-14       | 1.055709e-16     | YES    |
| 2     | 4.0019e4 (2666) | 3.177988e-05      | 1.000047e-14       | 1.014144e-16     | YES    |
| 2     | 1.956951e5      | 1.440466e-06      | 9.996273e-15       | 1.013931e-16     | YES    |
| 3     | 1e-13 (lane ed) | 2.456615e-01      | 5.498005e-18       | 2.377892e-18     | YES    |
| 3     | 4.0019e4 (2666) | 1.566869e-36      | 4.930613e-46       | 2.251853e-32     | YES    |
+-------+-----------------+-------------------+--------------------+------------------+--------+
```

At the n = 3 lane edge `lambda = 1e-13` the vertex factor
`(1 + d/lambda) ~ 1.06e14` lifts delta* fourteen orders above the
actual-lambda corner; at every operationally real lambda (the record-2666
audit range) delta* is lambda-independent to five digits.

## Findings

1. **The near-line obstruction is quantitatively absorbed by `q^n`.**
   The record-2713 collision concern is real as a continuum statement,
   but with the committed 2^-52 supplier the class pays the tail down to
   `delta ~ 1e-16` at n = 2 (and ~ 1e-32 at n = 3) - below any
   operationally meaningful separation and, at n = 3, below binary64
   resolution of delta itself.  The frontier is supplier-driven: in the
   older record-2033 proxy lane (q = 2^-14, sampled constants, unit-proxy
   W) the as-stored frontier at the passing row is only `2.578e-05`.

2. **The index requirement is unchanged.**  n = 1 fails (`ratio ~ 2e17`);
   n >= 2 passes with 14+ orders of margin at the actual gate lambda.
   Covering the near-line quantifier does NOT force gates at larger n,
   so the map-103 gate-availability question is not re-entered by this
   lane: n = 2 or 3 - exactly where the record-2666 certified class
   lives - already reaches delta* ~ 1e-16.

3. **The record-2710 geometry buys margin, not lanes, in this class.**
   The record-2354 lanes already passed under the old geometry
   (0.7604 / 0.2457); the new geometry improves those ratios by
   `3.2e9 (lambda = 4e4)` to `4.5e16 (lambda = 1e-13)`.  Its
   lane-opening significance is specific to the record-2033 unit-proxy
   convention, where the unit-proxy W and q = 2^-14 made the tail the
   binding half.

4. **Consistency cross-check.**  In the 2033-lane as-stored reading the
   sampled correction C2 (4657.98) sits 2.06x inside its budget
   (9605.36), matching the record-2710 inflation-window analysis
   (1.8x - 2.1x on the squared product).

5. **Residual obligations (unchanged, now with one quantified addendum).**
   The binding constraints remain the record-2666 trio: the same-owner
   gate witness at n = 2/3, prefix completeness, and the source-zero
   identity/quantifier.  The addendum: for a moved (repaired or
   near-line) rho the correction is rebuilt, and its C2 must be
   re-certified per rho; the floor <= budget margin above shows the
   budget has room for the floor itself up to delta*, but a construction
   achieving it is exactly the record-2708 P5 obligation and is NOT
   discharged by this pricing (coefficient change = owner change,
   AGENTS 2339 law).

## Nonclaims

- Not complete-owner certification: D4/D2/q are owner-conditional
  committed constants (2353/2354 supplier conditions apply); delta*
  inherits them.
- The scoped no-go region `delta < 1.0141e-16` (n = 2) is stated at the
  strongest-floor proxy `|Delta y| = 2`; it shrinks linearly with the
  formal orbit-value difference, which the Lean transport owns.
- No gate witness, no repaired-owner Gram re-run, no map-103 reopening,
  no Producer GO, no SourceRH, no RH claim.

## Evidence

- `scripts/nearline_collision_frontier_2714.py` (self-contained,
  exact-rational ratios, eight selftests, in-run 2354 anchors)
- `results/2714_nearline_collision_frontier.json`
- Inputs: `docs/proofs/2354_same_owner_tail_acceptance.md` (ratio,
  caps, K = 128.65, N = 6), `results/2666_gate_lambda_audit.json`
  (lambda range), `docs/proofs/2710_high_shell_geometry_verified.md` and
  `C1HighShellGeometry2710.lean` (d = 169/16),
  `docs/proofs/2713_quantitative_interpolation_joint_budget.md`
  (collision floor, budget form), `results/2033_gate_tail_pairing.json`
  (proxy-lane cross-check, sha256 ef82d9e8...),
  `docs/proofs/2666_gate_lambda_audit.md` (binding-obligation trio).
