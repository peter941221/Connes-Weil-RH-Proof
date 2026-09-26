# 104 — Route A: selected-owner signed physical-kernel campaign

Date: 2026-09-24.

Status: active campaign. Round 1 is FORMAL. Round 2 now has a FORMAL
physical-derivative-controlled selector, but its signed margin remains OPEN.
The former current-API no-go has been removed by this new owner construction;
the analytic sign obligation itself is not yet closed.
This record is subordinate to [003](003_b1_b5_minimal_exit_route_selection.md),
[080](080_c3p_signed_certificate_owner.md), [081](081_orbit_physical_kernel_coboundary_certificate.md),
and [082](082_direct_semilocal_gate_assault.md). RH is not claimed.

## Consumer and owner

The campaign serves the healthy detector-specific B5 consumer:

```text
actual selected detector g
  -> same-owner semi-local gate
  -> qw(g) >= 0
  -> SourceRH
  -> Mathlib RH.
```

The owner is the actual parameterized selected test
`(selectedOwner base correction n).sourceTest`, with its own support and
support-derived finite visible-prime-power set. No fixed-prime, continuous,
ROOT-only, or narrow-root surrogate is admissible.

## Four-round plan

### Round 1 — exact selected-owner expansion (FORMAL, landed)

Target:

```text
ICgate(selectedOwner.square)
  = archimedeanTerm(selectedOwner.square)
    + actual finite visible-profile sum,
```

and, under the already available triple-vanishing field,

```text
qw(selectedOwner)
  = -archimedeanTerm(selectedOwner.square)
    - actual finite visible-profile sum.
```

This removes the opaque `finitePrimeSum` presentation from the producer
obligation. The exact declarations are in
`C1RouteASelectedOwnerResidualReadback.lean`, with paired audit. Focused build
`20260924_routeA_round1_retry5.log` completed successfully (3662 jobs, zero
errors, standard axioms only, no `sorryAx`). See proof record
[1922](../proofs/1922_route_a_round1_selected_owner_readback.md).

### Round 2 — physical-derivative-controlled selector and signed residual budget (PARTIAL FORMAL)

For the same owner, expand the `081` coboundary residual and prove an explicit
strict margin:

```text
archimedeanTerm(selectedOwner.square)
  + integral (-t * actualAggregateDerivative(t))
  <= -epsilon,
epsilon > 0.
```

The finite sum must remain grouped inside the actual aggregate derivative.
Primewise absolute majorants are not an admissible substitute because they can
destroy the required cancellation.

The first attempt exposed a named underdetermination in the old owner API.
`ResidualCorrectionFamily` in `C1HealthyYoshidaCorrectionFamily.lean` exposes
only:

```text
support (value y) ⊆ (lower, upper)
laplaceAt (value y) z = y z
```

The residual in `C1P2OrbitPhysicalKernelCoboundary.lean` is instead
`-t * orbitFinitePhysicalKernelIntegrandDerivative geometry t`; its derivative
depends on the physical profile and its shifted derivatives. No field or
theorem in the current family supplies a derivative, phase, variation, or
signed-integral bound for that profile. The existing
`OrbitPhysicalKernelCoboundaryCertificate.residual_budget` records the desired
inequality as an input field, so invoking it would merely rename the missing
premise.

Therefore the requested strict margin is not derivable from the current
Round-1 owner hypotheses. The precise stop result is:

```text
NO-GO-A2-CURRENT-API:
support + finite Mellin interpolation do not expose the physical derivative
data required to prove the signed residual budget.
```

That obstruction is now addressed at the owner level by
`C1PhysicalDerivativeControlledCorrection.lean`. Its
`SelectedPhysicalDerivativeCorrection` stores the same support and finite-node
readback together with a nonnegative derivative seminorm and the pointwise
bound

```text
||deriv correction.test x|| <= derivativeCost(y).
```

The selector is constructed from the existing finite-window interpolant and
the derivative Schwartz operator, so this is a proved bound rather than a new
residual-budget premise. The paired audit is green: build
`20260924_physical_derivative_selector2.log`, 3662 jobs, zero errors, standard
axioms only, no `sorryAx`. See [1924](../proofs/1924_route_a_physical_derivative_selector.md).

The derivative residual has now also been eliminated exactly. The new leaf
`C1P2DirectCoboundaryResidualReduction.lean` proves, for the actual residual
and actual finite aggregate,

```text
integral(actualAggregate) = integral(actualResidual).
```

This uses the already proved zero boundary values of the coboundary and keeps
the full visible-prime sum grouped. Build
`20260924_direct_coboundary_reduction6.log` completed successfully (3791
jobs), with standard axioms only and no `sorryAx`; see
[1925](../proofs/1925_route_a_exact_aggregate_residual_reduction.md).

The signed margin itself is still open. The remaining analytic target is now
exactly `archimedeanTerm + integral(actualAggregate) <= -epsilon`, with no
separate derivative-residual premise. A final audit shows that the new
derivative seminorm is finite but has no uniform bound tied to the interpolation
data or to the Archimedean term. Together with the existing finite-node physical
separation theorem, this gives the scoped stop result
`NO-GO-A2-FINAL-SIGN-CURRENT-SELECTOR`: the current classical selector and its
stored derivative cost do not determine the signed aggregate margin. This is a
no-go for the current selector API, not for a new variational or
sign-constrained selector. See [1926](../proofs/1926_route_a_final_sign_current_selector_no_go.md).

### Variational replacement — formal core, physical adaptation OPEN

The next selector mechanism is now fixed precisely. The new leaf
`C1VariationalFiniteDimensionalSelector.lean` proves that every affine fibre of
a linear map from a finite-dimensional complex Hilbert space has a
minimum-norm representative. This removes the arbitrary-representative choice
from the finite Mellin interpolation stage and is audited with the standard
axioms only; see [1927](../proofs/1927_variational_min_norm_affine_selector.md).

The existing `windowedFiniteMellinVector_span_top` supplies the finite target
span needed to instantiate this mechanism. It does not yet supply the physical
source-basis quadratic form: the ordinary Hilbert norm is not being identified
with the actual derivative seminorm. The live obligation is therefore smaller
and explicit: extract a finite source basis and prove a positive quadratic
derivative-cost bound whose minimizer controls the grouped residual from 1925.
The source-to-`CompactLogTest` derivative transport is now formal; only the
finite-basis minimization and its uniform margin remain in this obligation.

The first physical-cost estimate is now formal as well. The leaf
`C1P2PhysicalDerivativeSeminormBound.lean` bounds the derivative seminorm of
the actual finite-window source combination by the exact coefficient-weighted
sum of the derivative seminorms of its supported source tests; see
[1928](../proofs/1928_route_a_source_physical_derivative_budget.md). This
strictly reduces the remaining obligation: minimize the resulting finite-basis
weighted cost and prove its uniform signed margin. The transport itself uses
the chain rule and the weighted source seminorm. The signed margin and
parameter quantifiers remain open.

The finite-basis minimization core is now formal in
`C1VariationalFiniteDimensionalSelector.lean`: a finite source family is
represented in `EuclideanSpace`, and every attainable Mellin target has a
minimum-coefficient representative. See
[1929](../proofs/1929_route_a_finite_basis_minimum_selector.md). The remaining
source-specific instantiation is now attached to the existing sparse source
support by `exists_min_norm_on_sparse_source_support`; see
[1930](../proofs/1930_route_a_sparse_support_selector_instantiation.md). The
strict grouped-residual sign is still independent and open: minimum coefficient
norm and derivative upper bounds do not imply a signed physical-kernel margin.
No conditional sign statement is being promoted to a producer theorem.

The fixed-owner reduction is now formal in
`C1RouteAFixedOwnerGroupedResidual.lean`: for every actual
`OrbitG8Geometry`, the grouped coboundary residual plus the Archimedean term is
exactly `ICgate g.convolutionSquare`, and strict residual negativity is
equivalent to strict gate negativity. See [1931](../proofs/1931_route_a_fixed_owner_grouped_residual_gate_equivalence.md).
This removes the duplicate residual formulation. The remaining producer input
is an owner-specific strict gate certificate; no exact matrix witness for that
actual owner is currently committed.
The fixed-owner explicit-margin form is also formal: an `epsilon > 0` grouped
residual margin exists exactly when that owner has `ICgate < 0`. This supplies
the correct target for the next certificate but does not supply its numerical
or analytic sign.

The sign orientation is now also formal. Under the hypothetical off-line
right-half-plane assumptions, the same actual healthy `OrbitG8Geometry`
produces healthy detector data, hence `qw g < 0`; the P2 readback therefore
forces `0 < ICgate g.convolutionSquare`. Thus an owner-specific negative gate
witness is not an intermediate construction available from the current
healthy-owner assumptions: it is precisely the contradiction-producing RH
theorem. This is a sign-orientation correction, not a no-go for Route A.
The audit/build is in record 1931 and
`20260924_routeA_fixed_grouped_residual9.log`.
The explicit parameterized no-go
`not_ICgate_nonpos_of_healthyOrbitGeometry` is now audited in the same leaf:
the proposed fixed-owner nonpositive witness cannot coexist with the healthy
owner hypotheses. This is a no-go for that witness order, not for Route A.

### Round 3 — parameter and margin closure (OPEN)

Round 3 may start only after the central sign producer is available in a
parameterized form. Its exact entry target is an explicit uniform statement
for every hypothetical right off-line zero: an actual owner geometry, all
finite-prefix/support/visible-cutoff quantifiers in the correct order, and an
`epsilon > 0` with grouped residual at most `-epsilon`. By the sign-orientation
theorem above, this target is equivalent to producing a negative same-owner
gate and therefore already contradicts the formal healthy-detector sign. It is
not merely quantifier bookkeeping. Until that contradiction-producing analytic
inequality is proved (or the owner/route is changed with a new B5 consumer),
Round 3 is not yet entered.

### Round 4 — consumer assembly and audit (OPEN)

Feed the strict budget through `081`/`082`, prove the same-owner gate and
`qw >= 0`, then invoke the existing contradiction and RH bridge. No new
generic exit wrapper is permitted.

## Round-1 ledger and stop rule

Known: selected-owner construction, support-derived finite owner, triple
vanishing, strict spectral negativity, and the generic residual identity.

Removed in this round: `finitePrimeSum` as an opaque selected-owner input; it
is now exactly the finite weighted profile attached to the actual owner.

Remaining after Round 2: prove a strict signed residual inequality for the new
owner, with the grouped finite aggregate intact. The old residual-budget field
is not accepted as progress.

Round 1 failure would be an owner mismatch or an inability to express the
finite sum using the selected owner's exact visible set. Such a failure would
stop this lane and be recorded as a named no-go; merely adding another wrapper
would not count as progress.

Evidence level: FORMAL for Round 1; PARTIAL FORMAL plus scoped final-sign
NO-GO for Round 2; PROJECT CANDIDATE/OPEN for Rounds 3–4.

## 2026-09-26 — selector status under records 2003/2004/2005

No-go status changed. The A-V no-go reported in record 2001 is withdrawn as
unsupported evidence (record 2005): its artifact carries route set
`["A", "B"]` with `spread_D = 0.0` on all four rows, so the rows had a single
certified route, and its family inflated the support radius past the `Ap`
guard and therefore measured a larger visible-prime set than the committed
owner's. A-V is UNRESOLVED, not adjudicated. The advice not to formalize it
stands, for the reason that the probe cannot be read.

New mechanism status (records 2003/2004). The support-preserving feasible-fiber
ray scan gives `A-H-CONE-MIXED`: all four anchors reproduce the committed
rows (<= 4.3e-11) on three routes with `D < 0` in 56/56 rows, and two of four
owners keep a certified healthy row at `sigma >= 0.05`. At gamma_8 direction 2
the health margin increases monotonically from `+664.35` to `+2128.7` with
`D < 0` and `det < 0` throughout, so the committed selector is not extremal
for health. The two gamma_5 owners lose health at the first non-zero
amplitude and hold the two smallest committed margins.

Also recorded in record 2003: the minimum-H1 selector endpoint of records
1999/2000 is not numerically well defined at this basis size (H1 Gram rank
deficient at `1e-14..1e-15` relative; clipped pseudo-inverses miss the pin
gate, the exact-constrained solution needs coefficients of order `1e+14`).
Future selector probes must use the ray formulation or an equivalent
well-posed one.

Binding obligation unchanged: `D < 0` on the selected healthy owner. Nothing
in these records touches the COVER layer, and no RH claim is made.

Authorized next step: the health-cone and dual-certificate desk that
`A-H-CONE-MIXED` reserves, beginning with a rank-spread direction scan, since
the two most energetic directions are a worst-case-biased sample of the
fiber.

## 2026-09-26 — health-cone shape scan under records 2006/2007/2009/2010

The rank-spread direction scan is done. Record 2006 pre-registered it; records
2007 and 2009 restated the instrument before and after the first execution;
record 2010 is the outcome. Instrument amendments were needed twice: the
route-keyed gate readout is the `Ap` route, which carries a resolution-
dependent spline error, so `C > 0` was made a route-robust conjunction and the
in-run anchor gate was moved to `D` (the binding entry, certified-route spread
`<= 6.0e-04`).

```text
verdict            H-CONE-STRATIFIED / RANK-FLAT / MECH-MIX
instrument         4/4 anchors pass, 128/128 rows certified, ident on every row
reproducibility    run 2 equals run 1 bit-for-bit on all 128 rows
health radius      G5-H none/0.02, G5-W none, G7-H 0.05..0.20, G8-H 0.80
                   at ranks 2, 4, 6 and 0.05 at ranks 1, 9, 12, 17
N                  14 of 32 pairs at sigma >= 0.05 (H-CONE-FAT needs 16)
```

Only three `(owner, rank)` pairs increase the margin with the perturbation,
all at gamma_8 and all in the energetic subspace (ranks 2, 4, 6; factors
3.20, 4.26, 4.04). The registered `RANK-FLAT` label is a rule artifact: when
every ratio `C(0.80) / C(0)` is negative the argmax returns the
least-collapsed rank. No registered threshold is changed.

Conditioning finding: `f = mm / A` at the committed anchors is 7196 (G5-H),
86087 (G5-W), 133 (G7-H) and 51 (G8-H), so the committed `A` is the residual
of a cancellation of order `f`. The obligation `D < 0` is well conditioned
while the health witness `C > 0` is not, which is why the gamma_5 owners have
no cone. Route-A numeric exposure is in the admissibility check, not in the
obligation.

Evidence level: measurements, not progress. No bound on the selected
detector, no new no-go, no smaller obligation; record 1926's selector no-go
stands, TAIL and COVER are untouched, and no RH claim is made.

## 2026-09-26 — A-HD constrained health maximization under records 2011/2014/2014a

The cone question was inverted and pre-registered as a design problem -
maximize `C` over the feasible fibre subject to `D < 0` - on an amplitude grid
extended past the record-2004/2010 range (record 2011). Record 2014 is the
outcome and record 2014a the instrument amendment it needed.

```text
registered verdict     INSTRUMENT-FAIL   (the J1 anchor band on the C
                                         coordinate at G5-W)
amended verdict        A-HD-MIXED        (same checkpoint, no new rows)
stage 2                NOT licensed (needs A-HD-GAIN)
instrument             4/4 owners pass the amended gate; 112/112 rows
                       certified on three routes, D < 0 in 112/112;
                       the sigma = 0 rows equal the committed record-2006
                       cone anchors to 0.00e+00 on C and D, and the 48 shared
                       grid cells reproduce that artifact to 0.00e+00 on
                       C, B01, D, det with identical health verdicts
```

The gain is not a height law. Ranking the four owners by the attained
`G = C(M)/C(0)` reproduces their ranking by `1 / (2 + f)`, the committed
cancellation order: `G` = `-45.873` (G5-W, `f = 8.6e+04`), `-2.288` (G5-H,
`7.2e+03`), `1.653` (G7-H, `133`), `14.096` (G8-H, `51`). The two owners that
share the ordinate `gamma_5` sit at opposite ends; the two positive owners are
the two lowest-`f` owners. At G8-H the branch is still increasing at the
largest registered amplitude (`sigma = 1.60`, rank 6), with `det < 0` and
`|D|` growing by 1.865; at G7-H it turns immediately (maximiser at
`sigma = 0.05`); at G5-H and G5-W every one of the 28 rows is unhealthy.

Two consequences for the campaign. The selector freedom is a relief on the
cancellation order, so it cannot be spent at `gamma_1..gamma_6` - the
committed selector remains the binding object at those heights, which is what
the published COVER scans (record 2012) measure on. And the measured
mass-level resolution offset at half resolution is `2.6e-07` to `7.0e-06` per
owner, with the C coordinate exposed to it by the factor `|2 + f|` - the first
measured constant behind record 2013's `P1`, with an erratum correcting 2013
section 2's factor `(1 + f)` to `(2 + f)` (record 2014 section 5).

Evidence level: measurements, not progress. No producer is licensed (record
2011 section 6 stands), stage 2 is not run, the binding obligation is
unchanged, and no RH claim is made.
