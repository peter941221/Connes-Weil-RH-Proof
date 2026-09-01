# 1050 - One-shot RH route verdict after the paper-scale audit

Date: 2026-08-29.  Follows 1049.

Status: NO-GO for treating the current ROOT-window endpoint theorem as the
last step to RH.  GO for one uninterrupted proof campaign with batched
verification at ownership boundaries.  RH is not claimed.

Map role: supporting paper-scale and quantifier boundary. Its route-selection
content is superseded by the binding healthy-`CompactLog`, B5-shaped ruling in
[`003`](003_b1_b5_minimal_exit_route_selection.md); current endpoint scope is
defined by [`004`](004_endpoint_literature_interface_audit.md).

## 1. What was checked

The primary source is Connes--Consani, *Weil positivity and Trace formula,
the archimedean place*:

<https://arxiv.org/html/2006.13771>

The paper proves a single-archimedean-place theorem for tests supported in
`[2^(-1/2), 2^(1/2)]`.  In log coordinates this is exactly the ROOT window
`[-log 2 / 2, log 2 / 2]`.  Its abstract says that the ingredients make
sense in the general semi-local setting, where Weil positivity implies RH;
it does not prove that general semi-local positivity theorem.

Appendix C, equation (155), gives the RH criterion over every compactly
supported admissible test and the sum over all places.  Therefore the local
endpoint theorem and the global RH criterion have different quantifiers and
different arithmetic content.

The repository independently pins that boundary in Lean:

```lean
theorem normalizedRouteBackedCC20SquareRestrictedDetectorCriterionCoverage_iff_mathlibRH
    (hexists : CC20YoshidaDetectorExists
      normalizedCC20TestSpace cc20TripleFiniteVanishingSet) :
    NormalizedRouteBackedCC20SquareRestrictedDetectorCriterionCoverage <->
      _root_.RiemannHypothesis
```

This is in `ConnesWeilRH/Route/CC20RouteRealization.lean`.  Consequently the
current `normalizedSelectedFinalRouteDetectorCriterionCoverageRoot` is not a
routine density lemma waiting after GATE 1.  Under the landed detector
existence theorem, it is RH itself in route language.

## 2. Paper-scale correction found in this audit

Equation (119) is

```text
T = lambda * sum_(n in Z) (e_n - d(|n|) e_(alpha_n)),   d(0) = 0.
```

The generated owner previously indexed only `+/-1, ..., +/-1732`, so it
represented `T - lambda * e_0`.  The corrected owner uses

```text
Option (Fin 1732 x Bool)

none   = n = 0
some i = +/-1, ..., +/-1732
```

and keeps the old paired payload as `cc20Eq115NonzeroData`.  The readback is

```lean
cc20FiniteRankOperator (cc20Eq115Data lam) =
  (lam : ℂ) • cc20FourierProjection 0 +
    cc20FiniteRankOperator (cc20Eq115NonzeroData lam)
```

The same source reports the exceptional finite-rank scale near
`lambda_max = 1.05158 > 1`.  The Bessel estimate proved in the repository is

```text
q_T(xi) >= (1 - lam) * ||xi||^2.
```

It is useful only in the opposite regime `lam < 1`.  It remains a correct
non-paper-parameter branch, but it cannot produce the positive paper-scale
coercivity `epsilon2 ~= 0.00441`.  The paper-facing producer must use its
actual mechanism:

```text
exceptional vector
      + complement spectral bound
      + rank-one determinant repair
      = positive repaired form
```

Fact 1, equation (115), is also explicitly described in the paper as a
computer calculation giving an approximate `L1` distance `~ 0.00122`.
Formalization therefore needs a new exact interval certificate; the printed
decimal and plot are not a Lean proof object.

## 3. The real dependency graph

```text
                    LOCAL CC20 BASE CASE

  prolate modes + Appendix-F tail       finite-section / Toeplitz data
                |                                      |
                v                                      v
      certified chi enclosure             exceptional/complement bounds
                |                                      |
                +----------> eq-(115) <----------------+
                               L1 gap
                                  |
                                  v
                  Theorem-7 same-owner trace identity
                                  |
                                  v
                     qw(g) >= 0 on ROOT tests

                                  X
                     no automatic density lift

                                  |
                                  v
                   DETECTOR-SELECTED SEMI-LOCAL STEP
          finite visible prime set + same-owner positive trace
                                  |
                                  v
              nonnegativity for each constructed detector
                                  |
                                  v
                     SourceRH <-> Mathlib RH
```

Positivity on short-support pieces does not imply positivity on their sums:
the mixed quadratic terms are uncontrolled.  A partition-of-unity or density
argument would have to prove those cross terms nonnegative, which is exactly
the missing global/semi-local theorem rather than a topological closure step.

## 4. Recommended route to RH

The narrowest honest target is detector-selected semi-local positivity, not
universal positivity for every test as the first global theorem.

1. Finish the local CC20 base case with a genuine prolate owner, the
   Appendix-F uniform tail, an exact Fact-1 `L1` certificate, the paper-scale
   finite-section spectral certificate, and the Theorem-7 trace identity.

2. Add explicit support-radius and visible-prime-set fields to the already
   landed right-oriented healthy detector construction.  For each hypothetical
   off-line zero, its selected detector has finite support and hence only
   finitely many visible prime powers.

3. Prove the semi-local trace comparison only for that selected detector and
   its finite visible set.  The existing finite-prime readback infrastructure
   can supply the arithmetic side, but positivity of the matching semi-local
   compression remains new mathematics.

4. Feed detector-specific nonnegativity against the already proved strict
   negative spectral value.  This gives `SourceRH`; then use
   `RHDefinitionBridge.standard_source_rh_iff_mathlib`.

This removes the unnecessary first goal `forall g, qw(g) >= 0`, but it does
not remove the hard semi-local positivity theorem.  The ROOT-supported
detector alternative is not cheaper: once local endpoint positivity is
available, constructing a strictly negative ROOT-supported detector for each
off-line zero already proves RH by contradiction.

## 5. Verification policy for a long campaign

One final documentation pass is appropriate.  One single Lean build only at
the RH endpoint is not: an owner-type change near the bottom can invalidate
every downstream theorem without useful local diagnostics.

Use three batched gates:

```text
+----------------------+-----------------------------------------------+
| batch                | acceptance boundary                           |
+----------------------+-----------------------------------------------+
| owner correction     | eq-(119) table, symmetry, Bessel and audits   |
| local endpoint       | all four paper-scale GATE 1 producers         |
| RH exit              | selected semi-local producer through RH bridge|
+----------------------+-----------------------------------------------+
```

Within each batch, make several substantive advances before building.  At
the boundary require the success footer, zero `error:`, zero `sorryAx`, and
only `[propext, Classical.choice, Quot.sound]` in focused axiom readbacks.
Update README, MEMORY, and the design record only after the batch result is
known.

## 6. Source evidence

- Main theorem and single-place scope:
  <https://arxiv.org/html/2006.13771#S0.SS0.SSS0.Px1>
- Theorem 7 and equation (83):
  <https://arxiv.org/html/2006.13771#S4.Thmtheorem7>
- Equations (99)-(100) and the endpoint spectral series:
  <https://arxiv.org/html/2006.13771#S5.SS3>
- Fact 1, equations (114)-(115), and its computer-calculation proof:
  <https://arxiv.org/html/2006.13771#S6.SS3>
- Lemma 3 and equations (119)-(121):
  <https://arxiv.org/html/2006.13771#S6.SS4>
- Appendix F uniform remainder, equations (169)-(170):
  <https://arxiv.org/html/2006.13771#A6>
- Appendix C global RH criterion, equation (155):
  <https://arxiv.org/html/2006.13771#A3>
