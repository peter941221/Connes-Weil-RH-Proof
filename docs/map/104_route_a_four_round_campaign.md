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

## 2026-09-27 — one-copy interval certificate stop (records 2037/2038)

The one-copy G8-H basis removes the two-copy affine-fibre freedom and gives a
stable negative floating-point reading on xi in [-40, 40]. It does not close
the required full-line interval certificate: source-transform enclosure,
signed-kernel enclosure, finite-window quadrature error, and the |xi| > 40
tail bound are all absent. The current selector is therefore
`A-DEAD-CURRENT-CERTIFICATE`. This is a scoped no-go for this certificate
attempt, not a global no-go for every future Route-A selector. Do not enter
Lean, producer assembly, or parameter expansion from this result.

Evidence: [2038](../proofs/2038_route_a_one_copy_interval_certificate_audit.md),
with numeric input [2037](../results/2037_route_a_g8h_basis_comparison.json).

Evidence level: scoped numeric/certificate no-go; no producer is licensed and
no RH claim is made.

## 2026-09-28 - Route A truncated-owner correction (2104)

The 2095-2099 gamma/delta screens are scoped to a ten-height numerical
under-approximation of `healthyCorrectionNodes rho 0 empty`. At an interior
gamma, the healthy ball includes at least 12 additional numerical known-zero
positions from the first 30, so the sampled 17/18-node family cannot close
actual-owner COVER. The scale-0.86 18-node family additionally has a positive
finite-window reading on four interior delta cells. These are scoped no-go
rulings for the inference and family, not a closure of Route A.

A shared-kill-width, direct-solve family keeps support 5.12 and the visible
prime book at 52 on the tested known prefixes; 30/33/36-node numerical
owners have 12/12 negative m=6400 finite-window readings. Its complete
source-zero owner, parameter-uniform conditioning, outward full-line sign,
and model-to-real transfer remain open. Record 2058's L2 charge does not
transfer to this different owner without re-pricing.

Evidence: [2104](../proofs/2104_route_a_continuous_owner_correction.md).

## 2026-09-28 - Owner-matched budget (2105-2109)

The compact shared-kill-width family survives an owner-matched numerical
budget on the weakest tested known-prefix cell. EM forward, a_mat transfer,
Gram diagnostic, and tail total `7.460153030234718e7` consume only
`4.4528e-5` of sampled margin `1.675397327895099e12`. The result is not yet
producer progress because the finite owner is still a numerical prefix and
formal outward promotion plus parameter-uniform owner control are missing.

Evidence: [2104](../proofs/2104_route_a_continuous_owner_correction.md).

## 2119 formal owner-cardinality bridge

The actual closed-ball owner now has a formal unconditional cardinality bridge:
`ConnesWeilRH/Dev/C1RouteAOwnerCardinality.lean` maps it into a symmetric-height
window and applies the existing dyadic xi-growth/Jensen bound. The paired audit
passes with standard axioms only.

At the current `N=0`, `rho=0.945+39.25244858548658i` point, the numerical
translation is about `3002.56` source-owner nodes versus 62 in the compact
stress family. Therefore the present Jensen/growth interface is too loose for
that family by a factor about 48.43. This is a quantitative gap, not a global
no-go; the next core target is a sharper count/anchor estimate or a construction
whose cost does not scale one-for-one with all abstract owner zeros.

Evidence: `docs/proofs/2119_routea_formal_owner_cardinality_bound.md` and
`results/2119_routea_formal_owner_cardinality_bound.json`.

## 2134 evaluator-horizon boundary

Record 2134 closes the current sampled-tail extrapolation. On the owner used
by records 2059-2062, the m=6400 tail ratio is `1.20e-6` on `40..160`,
`2.50e-5` on `160..240`, and `3.76e-3` on `240..400`, but the evaluator
enters an alias cliff in `500..550`: the measured tail ratio reaches
`1.418884e18`. Therefore no m=6400 sampled value may be extrapolated to the
full line. Route A remains open only through an analytic vertical-decay tail
bound or an independently certified quadrature rule with a proved horizon.

## 2135 root-partition Lipschitz tightening

Record 2135 removes the dominant interval-dependency inflation in the fixed
order-48 tail variation skeleton. Using the 64 exact rational root intervals
from record 2066, the value of the order-47 derivative is evaluated at each
midpoint and enlarged by an interval Lipschitz error from the order-48
derivative. The resulting variation upper bound is `2.2934394233524675e73`,
only `1.0000008509682481x` the measured `N48`, versus the record-2068 skeleton
at `1.2466403887652727e81`.

This is a strictly smaller tail obligation, not a producer result. The
independent Arb/Lean rounding audit, endpoint/monotonicity bridge, and
actual-owner transfer remain open. Do not use the record to promote the
one-copy numerical G8-H candidate to the complete closed-ball owner.

## 2136 fixed-r48 tail reprice

Record 2136 re-runs the fixed `r = 48` tail price with the record-2135
variation bound, preserving the same one-copy G8-H owner and coefficient path.
The reported `8.096843616867657e-291` is a positive-half-axis numerical
trapezoid only, not a full-line bound. Record 2137 reads the missing negative
side at `4.0432520934276974e-284` on the same grid after replacing
`abs(real(P))` by the exact `abs(P)` product. The two-sided numerical scale
remains small, but the 2136 full-line interpretation is withdrawn. Both the
integral enclosure and the infinity remainder remain open; neither the
finite-window signed C3' margin nor the complete closed-ball owner is proved.
## 2138-2139 residual-budget owner-local branch

Record 2138 adds a consumer-side shell identity allowing a finite exact
prefix plus an explicit omitted low-shell residual budget. This is a smaller
formal consumer obligation, not a producer premise discharge.

Record 2139 screens the first owner-local implementation: fixed smooth-seed
cardinal interpolation with orbit/healthy targets and a finite omitted-zero
budget. At `rho = 0.945 + 39.25244858548658 i`, `N = 0`, the orbit-only
prefix leaves an absolute residual `5.92468117481211e4` against anchor model
`1`; adding 5, 10, or 15 known zero pins increases the residual to
`1.852410508636541e15`, `1.9157305927827673e32`, and
`4.309477489612436e31` through conditioning collapse. Only all 21 known pins
remove the residual.

Decision: `SCOPED-NO-GO-FOR-NAIVE-OWNER-LOCAL-CARDINAL-PREFIX`. Reopening
requires a changed basis or regularization, a proved signed residual identity,
or a different owner construction. The abstract closed-ball owner and the
Route-A signed C3' producer remain open.

## 2140-2141 changed-basis owner-local screen

The 2139 cardinal-prefix no-go remains scoped and binding. Record 2140 changes to an overcomplete H1 basis: the minimum-norm 40-profile family lowers the 21-known-zero residual to `0.0435199584` against anchor model `1`, but has `C < 0`, `D < 0`, `det > 0`. Record 2141 moves in its 32-dimensional null fibre. Three seeded candidates retain `C > 0`, `D < 0`, `det < 0` at 4001, 10001, and 20001 nodes and residual below `0.015`; the smallest reads `0.0110714711`. This is SCREEN-GO-TO-CERTIFICATION only: the Gram condition is about `9.62e16`, target pins miss by about `2.5e-10`, the integral is sampled, and the 21 known zeros do not constitute the formal owner. Exact coefficient/interval pricing and complete-owner transfer remain open.

Evidence: `docs/proofs/2140_routea_overcomplete_h1_residual_screen.md` and `docs/proofs/2141_routea_overcomplete_h1_fibre_screen.md`.

Record 2142 audits trial 162 with 80-digit arithmetic. The 160-point Gauss-Legendre reading had a `6.56e-2` pin error, but 320 points per panel reduced the maximum base/correction errors to `2.43e-10` / `1.21e-10`. Treat the first reading as quadrature non-convergence, not a coefficient no-go. The candidate remains numerical only because the double H1 solve is ill-conditioned and no interval gate or complete-owner transfer exists.

Record 2143 reconstructs the trial-162 coefficients against a 320-point high-precision target matrix. Minimum-norm corrections reduce both pin residuals below `1.5e-14`; the signed gate is unchanged at 20001 nodes. The remaining proof gap is complete-owner transfer plus interval full-line gate/tail, not the small target residual.

Records 2144-2150 now close the changed-basis owner-local residual promotion attempt. The finite known-zero gate survives, but complete-ball transfer fails catastrophically under log-scaled sampling (`max log10 residual product ~= 1613`), and exact 29-pin repair is ill-conditioned (`s_min ~= 2.74e-35`). The next work must use a different owner-preserving analytic mechanism.

## 2026-09-29 — exact finite-zero filter and its current gate limit (2151–2153)

The construction in [2151–2153](../proofs/2151_2153_routea_finite_zero_filter.md) bypasses the ill-conditioned full-owner interpolation solve. For any finite omitted-zero set disjoint from the three nonzero correction targets, a zero polynomial, a carrier-centred smooth factor, and a quadratic target interpolant give a correction that vanishes at every omitted zero, retains all three target values, and enlarges physical support only by the chosen smoothing width, independently of the zero count. This is exact paper algebra, not yet a Lean theorem or a signed producer. Its derivative order and gate cost still grow with the zero count.

On the old trial-162 numerical under-approximation (21 known zeros plus conjugates), the width-1.0 filter has a sampled vertex sign with the complete 8755-entry visible-prime book. An independent `m=3200` rule and grid refinement reproduce the relative determinant margin `1.6653e-6`. A target-preserving null-shape scan improves its best sampled margin to `4.5762e-4` at coefficient `0.962 i`, below the preregistered `1e-3` Go bar (`go_count=0`). The third nonzero target `rho+1/2` is enforced; the earlier two-target reading is withdrawn. The `m=400` filtered window is evaluator-alias dominated and supplies no gate verdict.

Decision: **NO PRODUCER GO**. The exact zero filter bypasses the 40-profile interpolation solve with a support increment independent of owner cardinality. Generic finite interpolation was already formal, so this construction does not shrink the signed producer premise. Moreover record 1931 formally forces `ICgate > 0` for the actual healthy selected geometry under the hypothetical off-line-zero assumption; the negative sampled vertex value here concerns an auxiliary span and cannot be substituted for that gate. Formal selected-owner membership for the changed correction, the actual complete-owner signed C3′ inequality, same-index spectral tail, full-line integral certificate, and uniform off-line-zero quantifiers remain open. The null-shape trial is a scoped no-go only at its stated grid and margin bar. The earlier "construction GO" wording is withdrawn. No binding route ruling or RH status changes.

Record 2154 repairs the trial-162 base/correction target pins on the `m=1600` matrix in the same run: residuals `2.615e-10` / `2.542e-11` fall to `1.78e-15` / `1.42e-14`, while the sampled determinant moves only `6.43e-11` relative. The thin auxiliary vertex margin survives this float repair, so coefficient pin noise is not the binding issue on that numerical row. This does not repair the incomplete owner, certify the integral, or change the `NO PRODUCER GO` decision. Evidence is in [2151–2154](../proofs/2151_2153_routea_finite_zero_filter.md) and `results/2154_routea_paired_filter_pin_repair.json`.

Record [2155](../proofs/2155_minimal_height_owner_truncation_no_go.md) closes one owner shortcut exactly: choosing a least positive-height off-line zero does not make the committed closed-ball correction owner line-only. Its radius `2^(N+1)+2+dist(2,rho)` exceeds `Im rho` at every `N`, so the owner extends above twice that ordinate, where minimality gives no restriction. The scoped no-go is for this owner truncation inference, not for the full B5 route; reopening needs control of the upper part of the exact ball or a changed prefix/tail geometry. No producer Go or route ruling follows.

Record [2156](../proofs/2156_target_value_tail_floor.md) supplies an exact target-value floor for the named four-point global-`C4/C2` tail certificate. It rules out the 2151–2154 auxiliary `n=0` row under the registered unit tail proxy, independently of the filter coefficients. The formal shell consumer has the additional `beta_s/m` factor and needs a complete prefix owner. The existing dyadic multiplicity theorem removes the unknown `m`: for a genuine source zero with `Im rho>39`, the `n=0,q=2^-14` certificate fails the strict shell budget at every `s<=43`. The trial height is not claimed to be an actual source zero, and larger shells or different indices remain open. The remaining work is the same-owner signed gate with an actual shell budget or a different tail method. No producer Go or route ruling follows.

Record [2157](../proofs/2157_near_pin_derivative_cost_floor.md) gives a quantitative Route-A selector obstruction. On support `(a,b)`, target value `1` at `t` and zero at `z` force the actual correction's derivative cost to be at least `4 exp(-X S)/(|z-t| X (b-a)^2)`, where `X=max(|a|,|b|)` and `S=max(|Re t|,|Re z|)`. Thus the current support-and-pins API cannot yield a separation-independent uniform derivative budget; a nearby owner pin makes that cost diverge. This is a scoped no-go for that shortcut, not for the actual finite owner, which has positive separation at each fixed `rho`. The signed C3' budget and uniform owner control remain open. No producer Go or route ruling follows.

The exact node geometry narrows that obstruction. The closed-ball kill set contains `rho`, but `healthyCorrectionValue` prioritizes its nonzero target value, and the kill theorem excludes target nodes. The detector target `rho+1/2` is separated from every source zero by more than `rho.re-1/2`; that bound does not separate the orbit target `rho` from a different nearby source zero. Consequently the remaining separation cost concerns nonzero orbit targets or must be bypassed by a signed estimate. This is exact owner algebra, not a C3' margin.

## 2162 direct selected-g screen

Record [2162](../proofs/2162_routea_paired_filter_direct_gate_screen.md) runs
the finite-zero filter against the direct selected-g coefficient
`C = ICgate(g.convolutionSquare)`, rather than the auxiliary four-point
vertex determinant. On the 21-known-zero under-approximation, paired zeros,
carrier width `2.5`, and a 34059-entry visible prime-power book, the trusted
`[-20,20]` window gives direct-kernel `C=-0.03763279514`, stable under grid
and seed-rule changes at relative movements `1.29e-12` and `3.82e-10`.
The independent FFT read differs by `1.39e-3` absolute, so the registered
cross-route `1e-3` gate is not passed. Extending to `[-40,40]` is invalid:
the evaluator horizon is crossed and the last-five-unit mass becomes
`0.99858`/`0.999968` at the two node counts. The negative sign is therefore a
finite-model candidate only. It cannot replace the complete owner; formal
record 1931 forces the actual healthy detector's gate positive under the
hypothetical off-line-zero assumptions. No producer Go or route ruling
changes.

## 2169–2171 root-window sign screen correction

The root-window branch was rechecked after a false positive in record 2168.
The translated-bump cross matrix had used a reflected overlap for `F(0)`;
record [2169](../proofs/2169_root_window_arch_screen_false_positive.md) repairs
that term and reassembles the form by direct autocorrelation polarization.
With three node constraints and a complex detection normalization, the top
Arch eigenvalue is `-0.0062324` at `dx=.002` and `-0.0060688` at `dx=.001`;
the independent 24-mode sine screen reads a top value near `-0.859`.  A
wider-window sine scan including the exact finite prime-power terms also has
top `ICgate` values below zero over the tested radii, with the closest row
moving from `-4.39e-4` to `-2.36e-4` under grid halving.

Decision: **SCOPED NO-GO for the root-window positive-direction screen.** This
does not assert a continuum sign theorem and does not alter the selected-owner
Route-A producer obligation. Reopening requires a named smooth source family,
owner change, or a certified positive finite-prime quadratic margin.

## 2177 topology extension screen and the only surviving grandchild

Record [2177](../proofs/2177_routea_topological_extension_screen.md) screens a
weak-compactness/confluent-node extension against the actual selected owner.
Topology alone is a scoped no-go: ROOT closure does not control the mixed
quadratic terms, finite interpolation does not determine the signed aggregate,
the actual-height owner count is far beyond the compact interpolation family,
and the near-pin derivative cost has the explicit `1/|z-t|` lower bound of
record 2157. A minimizer-existence argument therefore cannot supply the
selected-owner signed C3' margin.

The only retained grandchild is `A.005.1`, an owner-preserving,
non-interpolating weighted-zero-measure certificate. It must derive a fixed
nonnegative weight from the same physical-kernel/correction formula and prove

```text
Arch + C3'_aggregate <= -epsilon(rho,N) + B_zm(rho,N),
B_zm < epsilon(rho,N)
```

on the exact closed-ball owner. It is `GO-CANDIDATE / UNPRICED`; no owner,
consumer, or RH status changes until this fixed-owner enclosure is priced.

## 2026-09-29 — A.005.1 first formal residual reduction

The first smaller brick is now formal in
`C1RouteAWeightedZeroMeasure.lean`. For the exact source-zero subtype and the
actual test `F`, it fixes

```text
W(F,z) = spectralNormTerm(F,z)
       = xiMultiplicity(z) * ||laplaceAt F (z - 1/2)|| >= 0
```

and proves that the real part of the omitted low-shell spectral residual is at
most the exact finite sum of these weights. This removes the unnamed residual
premise from the A.005.1 contract, while preserving the complete source-zero
owner. The paired audit has only `[propext, Classical.choice, Quot.sound]` and
no `sorryAx`; see proof record [2185](../proofs/2185_routea_weighted_zero_measure_residual_brick.md).

This is not yet the producer margin: the next gate is still an independently
enclosed `B_zm < epsilon` on the exact owner. The map route, consumer, and RH
status do not change.

## 2186 — scalar weighted-budget summability bridge

The new theorem
`weightedZeroMeasure_summable_of_geometric_heightMultiplicity_bound` transports
the existing quadratic vertical Laplace estimate and analytic
multiplicity-shell bound to the exact scalar weight introduced in 2185. Under
the explicit shell premise

```text
0 <= q, q < 4,
spectralHeightMultiplicity (n+1) <= K*q^n,
```

it proves `Summable (weightedZeroMeasure F)` for the same source-zero owner.
The owning module, refreshed aggregate module, and paired audit pass with the
standard three axioms and no `sorryAx`.

This is a strictly smaller quantitative obligation: it separates the future
`B_zm` certificate into an exact finite shell-prefix contribution and a scalar
tail. It does not price the shell premise, does not prove
`B_zm < epsilon`, and does not change the producer or RH status.

## 2187 — candidate weighted-budget screen

The first candidate-owner weighted-zero screen uses the 2185 weight on 90
omitted known critical-line zeros below `|Im z| < 256`. It reads
`sum W = 2.0626232011592017e-3` against the 2138 anchor multiplicity `1`,
leaving a factor about `485` before owner/multiplicity/enclosure inflation.
This is `SCREEN-GO` for the residual-budget mechanism on the candidate owner,
not a producer result. The next binding check is whether the complete
source-zero owner, analytic multiplicities, and outward evaluation enclosure
consume more than that factor; the signed comparison with the final
`epsilon` remains open.

## 2188 — inflation stress screen

The candidate weighted budget was extended from 120 to 240 known critical-line
zeros and from `|Im z| < 256` to `< 512`. The budget stayed at
`2.0626232939013377e-3`; the implied anchor headroom is `484.8195...` for the
combined multiplicity and outward-enclosure factor. This is a candidate-owner
screen only. It gives no analytic multiplicity theorem, but it removes the
immediate finite-shell growth concern and makes the next enclosure target
quantitative: prove the actual combined inflation is below `484.8` and then
compare the resulting `B_zm` to the signed `epsilon`.

## 2189 — formal factor split

The exact-owner weight now has an audited pointwise factorization bound:

```text
xiMultiplicity rho <= Mmult
||laplaceAt F (rho - 1/2)|| <= Meval
  -> W(F,rho) <= Mmult * Meval.
```

This is a formal smaller obligation, not a producer result. It isolates the
next finite-shell certificate into multiplicity/cardinality and transform
enclosure factors; both must still be priced on the actual selected owner.

## 2190 — finite weighted-budget aggregation

The factor split is now aggregated on any finite exact source-zero set:

```text
sum W(F,rho) <= card(S) * (Mmult * Meval).
```

The theorem is formally audited and does not supply the three numerical
inputs itself. The next live obligation is to instantiate `S` with the exact
low-shell owner and prove its cardinality/multiplicity and transform bounds;
the 2188 candidate headroom remains the diagnostic margin.

## 2191 — exact-shell weighted-zero bound

The existing quadratic dyadic Laplace estimate is now connected formally to
the actual source-zero shell owner. For some `B >= 0`, every shell satisfies

```text
sum W(F,rho) <= spectralHeightMultiplicity(n+1) * (B / (2^n)^2).
```

The owning module and paired axiom audit are green in record 2191. This is a
smaller obligation only: the remaining gate is an explicit multiplicity-mass
certificate (using the finite-height bound if needed), followed by the signed
epsilon comparison. No RH producer margin has yet been closed.

## 2192 — geometric weighted-zero shell budget

The existing analytic multiplicity estimate is now connected to the weighted
zero budget. Since multiplicity growth is `3^n` and the vertical Laplace
estimate contributes `4^(-n)`, the exact-owner shell sum is bounded by
`spectralMultiplicityConstant * B * (3/4)^n`. The owning module and paired
axiom audit are green in record 2192.

The next gate is no longer convergence: it is to assemble an explicit total
weighted-zero constant and compare it against the signed selected-detector
epsilon. This remains an open producer obligation.

## 2193 — actual-owner weighted-zero summability

The geometric shell bound is now instantiated into an unconditional theorem
`Summable (weightedZeroMeasure F)` for the exact source-zero owner. This
removes convergence as a separate premise. The remaining obligation is only
the quantitative size of that sum: a certified finite prefix/tail bound and
comparison with the signed selected-detector epsilon.

## 2194 — explicit high-shell weighted-zero budget

The high shells now have one scalar bound:
`sum_n sum_{rho in shell(n+1)} W(F,rho) <= 4 * spectralMultiplicityConstant * B`.
The factor `4` is the exact geometric sum for ratio `3/4`; shell zero is kept
as the finite prefix. The module and paired audit are green in record 2194.

The remaining gate is numerical/analytic pricing of `B` and the shell-zero
prefix against the selected-owner signed epsilon. Convergence is no longer a
live premise, and no producer margin has yet been claimed.

## 2195 — quadratic constant candidate screen

The first candidate-owner screen for the global quadratic Laplace constant
found `C_lower ≈ 2315.34`, `B_lower ≈ 9.14e4`, and a high-shell budget lower
screen of `1.10e8`, only `6.59e-5` of the candidate signed margin. The generic
constant path therefore does not trigger a scoped no-go. This remains a
sampled lower screen; the next required artifact is an outward enclosure of
the same constant and the shell-zero prefix on the complete owner.

## 2196 — global-C triangle enclosure screen

The first structural upper screen used second-derivative masses and absolute
coefficient triangle inequalities. It priced the high-shell budget at
`5.10e12`, while the candidate signed margin is `1.675e12`; the ratio is
`3.0446`. Therefore the specific `GLOBAL-C-TRIANGLE-ENCLOSURE` architecture
is frozen as measured-fail for this candidate. This is not a Route-A no-go:
the screen discarded signed cancellation and was not interval-certified.
Reopen only with a named owner-local/direct-product or signed cross-family
enclosure mechanism.

## 2197 — owner-local direct-product mass screen

The named direct-product mechanism was tested. Forming the complete base and
correction functions before taking absolute values reduced the high-shell
budget screen to `3.691e9`, only `0.002203` of the candidate signed margin.
This reopens the branch as `GO-CANDIDATE / UNPRICED`; it is still not an
interval certificate. The next gate is outward enclosure of the functions,
second derivatives, and coefficient solve, with roughly a factor `454` of
headroom available.

## 2198 — direct-product stability control

The direct-product screen was recomputed at quadrature orders `m=1600, 3200,
6400`. The `C_upper` drift stayed below `1.7e-11` relative, with stable matrix
condition `2.6537e5` and solve residuals below `1.81e-11`. This supports the
mechanism as a genuine candidate, while exposing the large correction
coefficient (`~5.69e17`) that must be charged in the eventual outward solve
enclosure. The branch remains `GO-CANDIDATE / UNPRICED`.

## 2199 — coefficient-error budget

Adding a worst-case relative coefficient perturbation showed little movement:
the budget/margin ratio is `0.00220337` at `1e-6` error and `0.00238287` even
at `1e-3`. The large correction coefficient therefore does not bind this
screen. The next required enclosure work is physical-grid/trapezoid error and
complete-owner transfer; the branch remains `GO-CANDIDATE / UNPRICED`.

## 2200 — direct-product physical-grid refinement

Holding the `m=6400` coefficient path fixed, physical grids from 30001 through
240001 nodes changed `C_upper` by at most `2.0e-10` relative. The physical
trapezoid/grid term is therefore not binding in the measured candidate screen.
The remaining enclosure work is outward intervalization of the physical
functions and solve error, followed by complete-owner transfer.

## 2201 — solve-enclosure preflight

The interpolation solve was given a provisional residual enclosure using the
`m=3200` to `m=6400` matrix difference and the Neumann perturbation estimate.
The factor `||A^{-1}|| ||E||` is `6.22e-7`; after propagating the resulting
base/correction coefficient radii through the direct-product mass screen, the
worst high-shell budget ratio is `0.00220402` at `sigma=1`, versus `0.00220320`
without the solve radius. Thus the large correction coefficient does not bind
this candidate screen. This is a `SOLVE-ENCLOSURE-PREFLIGHT`, not an outward
certificate: replacing the measured matrix difference by an analytic bound is
still required. See [2201](../proofs/2201_routea_weighted_zero_solve_enclosure_preflight.md).

## 2202 — endpoint-split entrywise bound is too coarse

The endpoint-split rule was priced on all 900 interpolation entries. The
largest explicit entrywise bound is `2.7215e-14`; the resulting row-sum matrix
bound gives a Neumann factor of approximately `5.53e5` against the measured
`||A^{-1}||inf = 6.77e17`. Therefore the componentwise-modulus Simpson
assembly cannot feed the solve enclosure at this resolution. This is a scoped
`ENTRYWISE-SPLIT-BOUND-NO-GO`, not a no-go for the direct-product mechanism:
matrix-level cancellation or a sharper endpoint rule remains admissible. See
[2202](../proofs/2202_routea_weighted_zero_split_quadrature_price.md).

## 2203 — matrix-level cancellation survives

Applying the measured `m=3200` to `m=6400` matrix difference to the actual
base/correction solve vectors reduces the propagated correction movement to
`4.91e6`, about `9.6e-12` relative to the `5.69e17` correction coefficient.
The base movement is `4.47e3`. This is far below the existing `1e-6`
coefficient-error screen, so matrix-level cancellation remains a
`GO-CANDIDATE / UNPRICED`; 2202 freezes only its entrywise assembly. The next
obligation is an analytic bound on `E c`, not an entrywise bound on `E`. See
[2203](../proofs/2203_routea_weighted_zero_matrix_cancellation_preflight.md).

## 2205 — vector-split binding-node refinement

The two binding rows were recomputed with `NSEG=1000`. The base bound is
`9.1285e-8` and the correction bound is `7.2251e-5`; after the 2201 inverse
norm these correspond to provisional relative coefficient movements of about
`2.2e-4` and `8.6e-5`. This remains within the candidate budget headroom, so
the matrix-level branch stays `GO-CANDIDATE / UNPRICED`. Only the two binding
nodes were refined; the full 30-node envelope and floating allowance are open.
See [2205](../proofs/2205_routea_weighted_zero_vector_split_binding_refinement.md).

## 2207 — vector-split rounding allowance

The correction binding row's GL, Simpson, and coefficient-rounding allowance
totals `1.2689e-5`, or `0.1756` of the `7.2251e-5` vector-split bound. The
combined correction price is about `8.494e-5`, corresponding to roughly
`1.01e-4` relative solve movement under the 2201 inverse norm. This remains
inside the direct-product margin, but is close to the 2199 `1e-4` screen;
increase `NSEG` modestly before treating the allowance as closed. See
[2207](../proofs/2207_routea_weighted_zero_vector_rounding_allowance.md).

## 2208 — NSEG=1100 binding refinement

Raising the vector-split Simpson resolution from `NSEG=1000` to `1100` lowers
the correction binding bound from `7.2251e-5` to `4.9349e-5` and the base bound
to `6.2350e-8`. With the 2207 rounding allowance at the same scale, the
correction solve movement is about `7.4e-5` relative, restoring margin below
the `1e-4` screen. This is a binding-node pass only; the full-node and
analytic outward assembly remain open. See
[2208](../proofs/2208_routea_weighted_zero_vector_split_binding_refinement.md).

## 2209–2210 — full-node refinement and matched allowance

The full 30-node vector-split run at `NSEG=1100` has worst bounds
`6.23497e-8` (base) and `4.93489e-5` (correction), with the same worst nodes
29 and 2 and no hidden spike. The matched rounding allowance is `1.31768e-5`;
the combined correction price is about `6.253e-5`, or `7.44e-5` relative after
the inverse-norm propagation. The measured numerical budget is therefore
below the `1e-4` screen. Analytic transcendental allowance and complete-owner
transfer remain open. See [2209](../proofs/2209_routea_weighted_zero_vector_split_full_refinement.md)
and [2210](../proofs/2210_routea_weighted_zero_vector_rounding_allowance.md).

## 2211 — transcendental allowance price

The AMP-style exponent-argument allowance at the correction binding row is
`2.4594e-8` total (`2.4377e-8` argument smear plus `2.1685e-10` operation
rounding). The combined vector bound, rounding, and transcendental price is
`6.25503e-5`; transcendental error is only about `0.04%` of the total. This
closes the numerical pricing question but not the formal outward `exp` lemma.
See [2211](../proofs/2211_routea_weighted_zero_transcendental_allowance.md).

## 2212 — formal exponential perturbation lemma

The Lean brick
`C1RouteAExpPerturbation.norm_exp_add_sub_exp_le` now proves the reusable AMP
propagation inequality
`‖exp (z + δ) - exp z‖ ≤ 2 * exp (Re z) * ‖δ‖` whenever `‖δ‖ ≤ 1`.
The paired audit passes with exactly the standard three axioms and no
`sorryAx`. This closes the formal lemma used by the transcendental allowance
price; the outward floating-point assembly, complete-owner transfer, and
selected-detector signed margin remain open. See
[2212](../proofs/2212_routea_exp_perturbation_lemma.md).

## 2213 — coefficient-weighted exponential propagation

The same audited module now proves the directly usable form
`‖c * (exp (z + δ) - exp z)‖ ≤ 2 * ‖c‖ * exp(Re z) * ‖δ‖` under
`‖δ‖ ≤ 1`. This closes the formal coefficient propagation step used by the
AMP allowance price. IEEE/outward input assembly, summation certification,
and complete-owner transfer remain open. See
[2213](../proofs/2213_routea_exp_coefficient_propagation.md).

## 2214 — finite-sum exponential propagation

The audited exponential module now lifts the coefficient-weighted bound to
every finite quadrature family:
`‖Σ cᵢ (exp(zᵢ+δᵢ)-exp(zᵢ))‖ ≤ Σ 2‖cᵢ‖exp(Re zᵢ)‖δᵢ‖`, assuming
`‖δᵢ‖ ≤ 1` on the finite index set. This closes the analytic aggregation
step used by the GL/Simpson AMP price. IEEE operand and summation allowances,
and complete-owner transfer, remain open. See
[2214](../proofs/2214_routea_exp_finite_sum_propagation.md).

## 2215 — finite accumulator error interface

The exponential/finite-sum chain now has an explicit accumulator interface:
if each approximate term has radius `‖Eᵢ‖` and the final complex accumulator
has radius `‖r‖`, then the total readout error is bounded by
`‖r‖ + Σ‖Eᵢ‖`. This closes the mathematical aggregation seam for the AMP
price; concrete IEEE/ulp radii and complete-owner transfer remain open. See
[2215](../proofs/2215_routea_exp_accumulator_error_interface.md).

## 2216 — final finite AMP aggregation interface

The analytic chain now has a single final interface for the finite GL/Simpson
readout: final accumulator radius plus the sum of the coefficient-weighted
exponential perturbation radii. The paired audit remains standard-axiom-only.
This closes the AMP aggregation seam; concrete IEEE/ulp radii and
complete-owner transfer remain open. See
[2216](../proofs/2216_routea_exp_final_aggregate_interface.md).

## 2217 — full-node IEEE-style AMP radius screen

The parameterized AMP forward-error radius was evaluated over all 30 nodes,
all 30 families, and the complete `NSEG=1100` finite rule. The maximum is
`2.459424789942387e-8` at node 2, exactly the previous binding row to shown
precision; the minimum is `5.294892110768219e-10`, so no hidden node spike was
found. This closes the finite-node scope gap, but remains a forward-error
price rather than an outward IEEE proof. See
[2217](../proofs/2217_routea_weighted_zero_ieee_radius_screen.md).

## 2218 — relative-error to complex-radius interface

The Lean interface now turns a supplied real relative operation error
`|e| ≤ u` into the exact complex radius `u‖x‖`, which can feed the 2216 final
AMP aggregation. Mathlib's FP layer was checked and its arithmetic is
`unsafe` without a soundness theorem, so the remaining task is a separate
binary64 semantics/rational-ulp certificate, not an unverified Mathlib call.
See [2218](../proofs/2218_routea_float_relative_error_interface.md).

## 2219 — binary64 exp-cell scope no-go

The exact-Fraction atom screen checked three representative exponent atoms on
the binding node against adjacent-binary64 midpoint cells. Five of six real/
imaginary components were contained; one imaginary component was not. Thus
the stronger “NumPy `exp` is correctly rounded” assumption cannot be used as
the outward certificate. This freezes only the rounding-cell-only assembly;
the next admissible move is a certified transcendental implementation
remainder or a correctly-rounded MPFR backend. See
[2219](../proofs/2219_routea_binary64_exp_atom_scope_no_go.md).

## 2220 — implementation-radius replacement

The 2219 rounding-cell assumption is now replaced on the same three-atom
scope by exact-Fraction `exp/sin/cos` brackets. The mathematical exponential
is enclosed around the returned binary64 value with an explicit implementation
radius; the largest observed radius is `0.7352658427507756` adjacent-ULP-cell
widths, or `1.6001640668480035e-16` relative to the returned value, including
the previously failing family-0 imaginary component. This
is the first quantitative replacement for the 2219 assumption. It remains an
atomic interface brick: the full quadrature term, finite sum, owner transfer,
and signed producer margin are not yet certified. See
[2220](../proofs/2220_routea_exp_implementation_radius_certificate.md).

## 2221 — black-box exponential fallback no-go

The complete 2211 finite rule was priced with the unconditional bound
`|exp(q)-v| <= exp(Re q)+|v|`. Its `2.659471411358396e+05` charge is
`4.251730900507734e+09` times the `6.2550323e-05` combined-correction target.
Thus the triangle-inequality fallback is closed for this owner; it cannot
replace the missing implementation certificate. The 2220 explicit-radius
route remains admissible and must be lifted term-by-term. See
[2221](../proofs/2221_routea_exp_blackbox_triangle_no_go.md).

## 2222 — all-family atom lift

The exact-Fraction implementation-radius screen now covers all 30 families at
the binding node's central GL atom. All 60 real/imaginary components are
finite; the maximum relative radius remains `1.6001640668480035e-16`, and the
maximum radius is `0.9232114502239269` adjacent-ULP-cell widths. No family
spike appeared. This closes the family-selection gap only; the full
quadrature-point and finite-sum lift remains the next gate. See
[2222](../proofs/2222_routea_exp_all_family_atoms_certificate.md).

## 2223 — MPFR full quadrature at binding node

The implementation-radius route has now been lifted from atoms to the full
binding-node quadrature rule: 30 families, all GL points, and 12 Simpson
panels at `NSEG=1100`, using 256-bit MPFR RNDD/RNDU calls. The charge is
`7.039855400051501e-12`, only `1.1254706710389811e-07` of the 2211
combined-correction target. An independent MPFR ABI self-test passed for
`exp(1)`, `sin(1)`, and `cos(1)`. The remaining gates are input-`q`
construction, finite-sum accumulation, the other nodes, and owner transfer;
the library implementation itself is no longer the binding gate at node 2.
See [2223](../proofs/2223_routea_mpfr_exp_binding_radius_certificate.md).

## 2224 — binding-node combined budget

Adding the certified 2223 MPFR implementation charge to the existing 2217
input/operation price gives `2.460128775482392e-08` on the same full binding
quadrature, only `3.933039283398092e-04` of the 2211 target. The remaining
binding-node issue is therefore the outward certification of the `q` input
construction and accumulation, not the transcendental library. The 2217
component remains explicitly parameterized rather than certified. See
[2224](../proofs/2224_routea_binding_combined_mpfr_budget.md).

## 2225 — q-construction interval at binding node

The full binding-node q construction is now enclosed with MPFR directed
interval operations: 30 families, `1,944,360` GL/Simpson terms, and zero
containment failures. Using the valid all-delta exponential bound (rather
than the `delta <= 1` linear lemma at endpoint cells), the propagated charge
is `2.436718255644566e-09`, or `3.89561258643631e-05` of the 2211 target.
The remaining input question is the provenance of the binary64 operands and
finite-sum accumulation; see [2225](../proofs/2225_routea_q_mpfr_interval_binding_certificate.md).

## 2226 — adjacent-node q stability

The same MPFR q interval was run at node 3, the next-highest nearby 2217 row.
Its full 30-family quadrature charge is `2.233376170985172e-09`, below node
2's `2.436718255644566e-09`; both have zero containment failures and the same
endpoint q-radius maximum `36.099947214126594`. This is not yet the universal
30-node envelope, but it removes the immediate adjacent-node spike concern.
See [2226](../proofs/2226_routea_q_mpfr_two_node_stability.md).

## 2227 — remote-tail q stability

The MPFR q interval was also run at remote high-imaginary node 29. Its charge
is `1.7939006677210619e-09`, below node 2 and node 3, with zero containment
failures. Together nodes 2, 3, and 29 show no adjacent or remote-tail spike;
this remains a stability certificate rather than a universal 30-node bound.
See [2227](../proofs/2227_routea_q_mpfr_three_node_stability.md).

## 2228 — corrected complex-weight audit

An audit found that 2225–2227's first charge implementation cast complex
coefficients/weights to `float`, dropping imaginary parts. Those readings are
superseded. The corrected `abs(c)`/`abs(w)` runs at nodes 2, 3, and 29 have
zero interval failures and charges `8.792971355816332e-09`,
`8.063938632912915e-09`, and `6.475830084303228e-09`, respectively. Only
2228 is authoritative for this numerical charge. See
[2228](../proofs/2228_routea_q_mpfr_complex_weight_fix.md).

Record [2182](../proofs/2182_routea_chebyshev_majorant_sign_obstruction.md)
also closes the unsigned Chebyshev shortcut as a scoped no-go: its sharpened
majorant is nonnegative and can only absorb against a separately proved
same-owner `archimedeanTerm <= 0`. The ROOT-support sign theorem cannot be
transported to the actual selected owner. The live producer therefore remains
the signed C3′/weighted-zero-measure mechanism, not an absolute-value
majorant.

Record [2183](../proofs/2183_routea_quantifier_integrity_audit.md) confirms that
the selected-owner and `SourceRH` quantifiers are genuine and that no existing
master exit preloads RH. Thus the remaining signed margin is a real universal
producer obligation, not a missing wrapper or vacuous quantifier.

Record [2184](../proofs/2184_routea_rh_exit_axiom_boundary_audit.md) separately
rejects the repository's unconditional skeleton as Route-A evidence: it uses
project-root axioms outside the allowed library trio and does not instantiate
the selected-owner signed margin. Only the axiom-clean conditional exits are
admissible for the final GO.

## 2229 — all-30-node outward q-interval envelope

Record [2229](../proofs/2229_routea_weighted_zero_all_node_outward_envelope.md)
extends the corrected 2225/2228 evaluator to every owner node and upgrades
the charge accumulation to directed MPFR arithmetic (`mpfr_exp`/`mpfr_mul`/
`mpfr_add` RNDU, 256-bit). The binding node stays node 2 and is now
outward-certified at `8.792971355816406e-09`; the minimum over the 30 nodes
is `4.441432860466601e-09` at node 1 (`max/min = 1.9798`); interval failures
are zero at every node. The three 2228 control nodes drift outward by
`+8.4e-15`, `+8.0e-15`, `+5.6e-15` relative, i.e. at the binary64 rounding
level. The node-independent operands are pinned in
`results/2229_operand_cache.npz` (md5 `c78a0342fad8ac0166c23d01f653f666`,
same call chain as 2225). Ladder item 1 of the q-construction terminal is
executed; items 2 and 4 remain open.

## 2230 — operand provenance convention and transfer preflight

Record [2230](../proofs/2230_routea_weighted_zero_operand_provenance_and_owner_transfer_preflight.md)
fixes the discrete-defined operand convention: the stored binary64 tuple
`(K, a, theta, node, x, c, w)` is exact, and every interval artifact
2217--2229 bounds the finite sum for exactly that tuple. The
ideal-to-stored-tuple gap is item 2a of the acceptance ladder (coefficient
solve, quadrature generation error; interfaces 2199/2200/2201). The record
also inventories the complete-owner transfer obstructions with their
numbers: the 2119 cardinality bridge (`3002.5554464806` bound vs `62`-node
family, `48.43x`), the 2157 near-pin derivative floor, the 2134 evaluator
horizon, and the 2197 direct-product screen
(`3.691230708643563e9 = 0.0022031972041408675 x` the `1.675397327895099e12`
anchor). Convention choice, drift control, and ladder status are recorded;
no numeric claim is added.

## 2231 — uniform charge vs candidate budget

Record [2231](../proofs/2231_routea_weighted_zero_uniform_charge_vs_budget.md)
prices one uniform charge against the candidate budget chain. The maximum
over the 30 nodes, `8.792971355816406e-09`, consumes
`1.4057435572021598e-04` of the `6.2550323e-05` combined-correction target;
assembled with the certified 2223 implementation price it reads
`1.4068690278731986e-04`, a `2.7956` factor below the parameterized 2224
assembly (`3.933039283398092e-04`). The outward charge is `2.797 x` tighter
than the 2217 parameterized AMP price it replaces. The Simpson fourth-order
remainder of the combined price, the operand construction ledger, the
low-shell side, and complete-owner transfer remain open.

## 2232 — family-stitch closure

Record [2232](../proofs/2232_routea_weighted_zero_family_stitch_closure.md)
closes the binary64 stitch of the 2229 node totals. Lemma: two
round-to-nearest steps lose at most one spacing of the result and one
`nextafter` step upward adds one spacing, so
`nextafter-up(fl(fl(T+g)+s)) >= T+g+s` for outward-rounded nonnegative
family charges. Verified by directed re-accumulation of all 30 committed
node artifacts with 256-bit MPFR RNDU: no deficits, relative slack between
`2.536371840662237e-15` and `4.656045912096321e-15`; worst node 2 recomputes
to `8.792971355816368e-09` under the reported `8.792971355816406e-09`. The
family accumulation step of ladder item 2 is closed; the operand ledger is
priced in 2233.

## 2233 — operand construction ledger (c, w, x channels)

Record [2233](../proofs/2233_routea_weighted_zero_operand_ledger.md) prices
the three measurable channels of the 2230 item 2a. c channel: the
record-2201 provisional radius charges the q-chain charge by
`1.1225276886070804e-05` relative (base-labeled `5.478274212797956e-09`);
`|coeff|_max = 5.6875117346762605e+17` is bitwise the 2235 `corr_c_inf`, so
the 2225 q-chain and the 2197 direct-product solve are the same 30x30
system. w channel: the GL moment identities (`2a`, `2a^3/3`, `2a^5/5`)
close in directed MPFR on all 30 stored grids with worst relative gap
`9.164518758595832e-14` (family 8). x channel: an ideal node differing by
`k` ulps shifts q by the analytic `|dq/dx| d_k + (1/2)|q''| d_k^2`; sampled
re-evaluation at the two extreme nodes gives base drift `0.0` (bitwise
against 2229, all 30 families at node 2), `k = 1` inflation
`+0.15158672812255491` (node 2) and `+0.015164728187683663` (node 1),
`k = 16` `+2.4253876499608817` / `+0.24263565100294815`. Read into the 2231
budget the one-ulp channel costs about `2.1e-05` of the target.

## 2234 — direct-product outward envelope (first brick)

Record [2234](../proofs/2234_routea_weighted_zero_direct_product_outward_envelope.md)
re-evaluates the 2197 direct-product screen with 256-bit MPFR RNDN plus
documented outward allowances (slack `2^-200` magnitude sum, trapezoid panel
majorants, sigma Lipschitz cover, coefficient mass bounds). The four sigma=1
sums reproduce the committed 2197 values at the binary64 rounding level, but
the envelope is measured *too loose*: `C_upper = 2.4866178385966296e9`,
`32108.532816055962x` over the 2197 screen, `70.74142972939994x` the signed
margin. Attribution at the binding row: the coefficient allowance dominates
(`coeff_infl_corr_D2 = 55085.076713871786` relative), the panel allowance is
second (`panel_corr_D2 = 17018191.948288612` against the `1.5261406872e6`
norm). The defect is separated and repriced in 2235/2236.

## 2235 — coefficient-channel reprice from the 2197 scales

Record [2235](../proofs/2235_routea_weighted_zero_direct_product_reprice.md)
measures the 2197 system (`A_inf = 7.94200337904096e-13`,
`Ainv_inf = 6.77049894501907e+17`, `cond_inf = 537713.2549913471`,
residuals `6.4676997486962715e-15` / `1.1417431493021041e-11`) and refutes
the "wrong system" reading of the 2234 defect: the recomputed radii
(`1.4925623914296788e8` / `3.0583277493621344e11`) land within 13 percent of
the 2201 values, so the envelope was not repairable by rescaling
(`1.3253659305957348x` only, still `53.3750174924163x` over margin). What it
establishes instead is the attribution: one radius was charging the
generation channel and the solve channel together.

## 2236 — solve-floor envelope: viable

Record [2236](../proofs/2236_routea_weighted_zero_direct_product_solve_floor.md)
charges the coefficient channel at the computed binary64 solve floor
`r_c = Ainv_inf (||resid||_inf + gamma_30 A_inf c_inf)` with
`gamma_30 = 6.661338147750985e-15`: `r_base = 998596.0653225501`,
`r_corr = 2044934208.0214145` (the 2201 radius overcharged this channel by
`172.93818557922884x`). The envelope becomes viable: `C_upper =
2721865.34164875` (`35.14617376530097x` over the 2197 screen), high-shell
budget `129732635893.80194`, `tail/margin = 0.07743395177596035`, i.e.
`12.9x` below the anchor; the stored-exact reading of the coefficient
channel reads `1850509.4347934648` / `0.05264487413912939` on the same
binding row. This opens the first gap of ladder item 4. The generation
channel (screened at `1e-12`), the panel allowance, the multiplicity proxy,
owner transfer and the signed margin remain open.

## 2237 — certified generation channel

Record [2237](../proofs/2237_routea_weighted_zero_matrix_enclosure.md)
replaces the `eta = 1e-12` generation screen by a measured 256-bit MPFR
enclosure of all 900 stored matrix entries: `delta_max =
9.490758943075902e-29` at entry `[7, 7]` (`1.1950081723865955e-16` of
`A_inf`, about half an ulp), interval halfwidth at most
`8.361167990095088e-86`, 30/30 bitwise columns against the rebuilt system,
operand dump md5 `599e1714c9beb092b6704bcde3670caf`. The certified charge
is `3.967890880851082e-05` of the screen on the corr vector (`2.52e4x`
tighter; base `4.616507721922061e-05`), so the envelope moves by only
`+0.22%`: `C_upper = 2727859.2133313827`, `tail/margin =
0.07760447056089889`. The largest registered 2236 lever is retired.

## 2238 — dx^2 panel law with measured zero-free cells

Record [2238](../proofs/2238_routea_weighted_zero_panel_dx2.md) replaces the
2234 O(dx) panel by the composite-trapezoid identity on the uniform grid
(two integrations by parts; the `Delta` sum telescopes; `g'` vanishes
exactly at `+-a_max` by the `phi` extension, so every kink rate is `dx^2`).
Risk cells (node test `|h_k(x_p)| > dx m_{k+1}`, both endpoints) measured
from the committed chunks: 182747 / 199759 / 189618 / 207826 of 240000,
because the corner mass still uses global `m_{k+1}` (the classification
wall). Panels `1.8076571806532764`, `11693.314770969451`,
`2862.4920101295183`, `17018191.948288612` fall to `0.9194450801774107`,
`6422.964947252888`, `1510.5771804832668`, `9716500.106800418`
(`1.75..1.97x`). Stacked on the 2237 radii the envelope reads `C_upper =
1249100.8031538636`, `tail/margin = 0.03553548732728288` (`28.14x`
headroom; `16.12905429459266x` over the 2197 screen; `1990.73x` below
2234). Registered composite-EM lever: a numpy scan finds zero real zeros of
all four channels (deepest interior dips `2.487e-12` / `4.920e-09` on the
base channels), projecting panels `1.6e3..1.8e3x` below the 2234 values
and `tail/margin ~ 0.010940194125321153` once `Z = 0` is certified.

## 2239 — x-channel charge over all 30 owner nodes

Record [2239](../proofs/2239_routea_weighted_zero_xwidth_charge_all_nodes.md)
extends the 2233 x-channel sweep from the two sampled nodes to all 30
(900 chunk files; families sorted, one `nextafter`-up per `gl + sim`
addition). The reduction reproduces the committed 2233 two-node artifact
entry for entry (bitwise gate) and the per-node base column is bitwise
equal to the committed 2229 `exp_lipschitz_charge` at all 30 nodes (drift
`0.0`). Worst node is 2 at both levels: `k = 1` inflation
`+0.15158672812255491`, `k = 16` `+2.4253876499608817`; the worst one-ulp
absolute charge is `1.332898e-09`, `2.1309206641563692e-05` of the target.

## 2240 — the multiplicity constant is formal

Record [2240](../proofs/2240_routea_weighted_zero_multiplicity_constant_formal.md)
audits the `spectralMultiplicityConstant_proxy` carried since 2234: it is a
binary64 evaluation of the Lean
`spectralMultiplicityConstant` (`ConnesWeilRH/Dev/C1SpectralSummability.lean:303`,
with `xiGrowthFixedConstant` at `:38` and `kernelSmallMomentConstant` at
`:29`, tail constant `ConnesWeilRH/Source/CC20ZetaCounting.lean:85`),
bitwise equal at `301.83032993648527` (relative `0.0`; `‖xi(2)‖ = pi/6`
exactly). The `4 *` factor is the `3/4` geometric assembly of
`exists_weightedZeroMeasure_highShell_tsum_bound`. The multiplicity item
is therefore not a numerics lever; the only slack inside the constant is
the flat `+192` (`276.997447850681` of `301.83032993648527` in log2 units),
registered as a Lean-side task.

## 2241 — owner-transfer re-check at the 2238 standing

Record [2241](../proofs/2241_routea_weighted_zero_owner_transfer_recheck.md)
re-checks the three transfer items. The 2119 cardinality ratio `48.43x`
against the 62-node screened family, read as a linear count transfer, now
costs `48.43 x 0.03553548732728288 = 1.721x` over the margin (`3.750x` at
the 2236 standing; `0.530x` with the projected composite-EM panel) - the
binding transfer gap, needing a `1.721x` count refinement or the
composite-EM landing. 2157 (near-pin separation) is unchanged and open;
2134 (sampled-tail horizon) is bypassed: the current lane never
extrapolates a sampled tail, its tail is the Lean geometric assembly over
the certified 2197-screen budget - the independently certified rule 2134
listed as the admissible replacement.

## 2242 — certified zero count Z = 0

Record [2242](../proofs/2242_routea_weighted_zero_zero_count_certificate.md)
certifies the last open item of the 2238 composite-EM lever. Directed
256-bit MPFR interval paving over `[-a29, a29]` (`a29 = 2.32`) plus a
single-family analytic certificate on the edge arcs `+-(a29, a30)`
(`a30 = 2.5600000000000005`, `theta = -39.25244858548658`) gives `Z = 0`
for all four channel functions (`h_0 = F`, `h_2 = F''`, base and corr):
`n_failures = 0` in every channel (box counts `8780 / 9247 / 21219 /
12500`; bisections `40 / 236 / 13364 / 4509`; floors
`1.2760421464680534e-63 ... 1.0615649871831736e-53`, every floor box at
`[-2.32, -2.3199249487652582]`). The `~5e-314` candidates at `+-2.5079`
are the phi-decay denormal tail, bypassed analytically: on the arcs
`B2_re >= 435200.11369115417 > 0` (decreasing in `q`; infimum at
`q29 = 0.17871093750000044`). The boundary zeros at `+-a30` are flat.

## 2243 — composite-EM panel landing

Record [2243](../proofs/2243_routea_weighted_zero_panel_cem.md) lands the
lever: with `N_risk = 0` the panel is `(dx^2/12)(2 a_max) M_k(sigma)` and
the 2238 envelope (bitwise the same loop) reprices by
`5.187365461729664x` to `C_upper = 240796.76135588222`,
`tail/margin = 0.006850392090059914` (`146.0x` headroom;
`3.109295925568858x` the 2197 screen). The `sigma = 1` panels reproduce
the 2238 projection bitwise (`888.370x / 888.378x / 947.150x / 999.480x`
below the 2238 values); the registered projection's scalar gain (`3.248x`)
undercounted the recomputed composition gain (`5.187x`), so the landing
sits `1.597x` below the projection. The 2119 coarse transfer product now
closes: `0.3317529367828551` (`3.01x` slack).

## 2244 — ladder at the 2243 standing

Record [2244](../proofs/2244_routea_weighted_zero_transfer_ledger_at_2243.md)
re-inventories the ladder: 1 executed, 2a paid at the rounding level
(node-position exactness booked to the 2119 item), 2b closed, 3 priced,
4 open (2119 reading inside, 2157 open, 2134 bypassed, 2197 enclosure
executed at `C_upper = 240796.76135588222`), 5 open - the strict signed
margin is now the terminal analytic obligation, with `146.0x` numeric
headroom against the anchor `1675397327895.099`. The formal transfer
reading does not prove transfer; no producer GO, no RH claim.

## 2245 — explicit owner zero-count brick

Record [2245](../proofs/2245_routea_weighted_zero_owner_count_brick.md)
replaces the 2119 Jensen cardinality bound at the three stress candidates
by the explicit window count `N(T) = (theta(T) + Phi(T))/pi` with the cited
Trudgian `|S(T)|` bound (J. Number Theory 134 (2014) Theorem 1,
`0.111 log T + 0.275 log log T + 2.450` for `T >= e`) plus the
Platt-Trudgian import: owner `<= 26 / 29 / 32` unconditional, `= 21 / 24 /
27` imported; at the stress point `3002.5554464806 -> 26` (`115.48x`) or
`21` (`142.98x`), so the 2119 count ratio drops `48.428313652912905 ->
0.41935483870967744 / 0.3387096774193548` and the coarse readings against
the 2243 `tail/margin` become `0.0028727450700251254 /
0.0023202940950202934`. Instrument finding: the 1980 `GAMMAS[3] =
27.67032193035704` labelled `gamma_4` is not a zeta zero (`|zeta| =
2.845101349`; no Hardy-Z sign change; the exact phase identity gives
`N(82.519...) = 21`); the true `gamma_4 = 30.424876125859513210`. The
count side of the transfer is done; the per-node half stays open.

## 2246 — strict signed-margin statement

Record [2246](../proofs/2246_routea_weighted_zero_item5_margin_statement.md)
fixes the item-5 inequality `(-q_lo) - (4 * mult * B_upper * transfer +
known_error_sum) >= eps0` at the candidate and assembles the ledger:
anchor `1675397327895.099` (a binary64 sample), known errors
`74601530.30234718`, high-shell tail `4894093747.764274` (2248 standing),
transferred totals `2126963424.5260766 / 1732278444.8676672`, readings
`0.0012695277646158757 / 0.0010339508223067488`, slacks
`0.9987304722353841 / 0.9989660491776933`. Bricks: `L1` downward
enclosure of `|Q|` OPEN (load-bearing), `L2` count side done (2245) /
per-node open, `L3` strict arithmetic fixed. The statement exists; it is
not proved.

## 2247 — measured separation input

Record [2247](../proofs/2247_routea_weighted_zero_separation_input.md)
measures the 2157 near-pin input at the three candidates: minimum
target-to-pin separations `1.7246687029005743 / 1.2837708405212573 /
2.380992966914273`, all against true critical-line zeros; 2157 floors at
those separations `0.0030755954591358543 / 0.004131877017085821 /
0.0022278029817236807` (per-target minimum `0.0005846130698864416` at the
`rho + 1/2` target of candidate 3, where `S = 1.445`). Target-to-target
distances `0.5 / 0.89 / 1.39`; the detector target's automatic `0.445`
bound is dominated by measured `1.53 ... 2.52`. Uniform in `rho` remains
research-grade; per fixed `rho` it is a finite certified check.

## 2248 — multiplicity constant 192 -> 72

Record [2248](../proofs/2248_routea_weighted_zero_multiplicity_tightening.md)
lands the registered Lean tightening: the absorption lemma
`2 (n+4) + (n+4) 2^(n+4) <= 72 * 3^n` (`72` the exact supremum, attained
at `n = 0`) replaces `192 = 3 * 64` at all four sites, so
`spectralMultiplicityConstant` reads `128.70692502980964` (was
`301.83032993648527`, `2.345x`), the high-shell tail reprices
`11477128602.720102 -> 4894093747.764274` (`tail/margin
0.0029211540846331738`), and combined with 2245 the readings are
`0.00122500010000746` (unconditional) / `0.000989423157698333` (imported).
Module+probe build `3532` jobs and full library build `4148` jobs both
exit 0; the probe axiom audit stays `[propext, Classical.choice,
Quot.sound]`.

## 2249 — certified downward enclosure of the finite-window functional (L1)

Record [2249](../proofs/2249_routea_weighted_zero_l1_enclosure.md) closes
the load-bearing L1 brick of 2246. Every float operation of the 2103
pipeline carries a first-order forward-error shadow (`U = 2^-52` per
elementary op, `64 * 2^-53 * sum |terms|` per pairwise reduction, final
`1e-6` inflation), giving `q = -1675397327923.575` with
`E_total = 1281535.3012791811` (`7.649142564095338e-07` of `|q|`), so the
certified margin reads `margin_lo = 1675396046388.2737` (`= -q_hi`).
Readings at the certified margin: `0.0012695287356749262` (unconditional)
and `0.0010339516131735035` (imported), slacks `0.9987304712643251 /
0.9989660483868265`, eps0 `1673269082963.7476 / 1673663767943.406`
(positive, i.e. the strict inequality holds against a certified margin).
Cross-checks against the plain pipeline: `g` peak relative difference
`3.0620944708905883e-13`, kernel `3.55e-15`, `p` bitwise. An instrument
bug (complex power update in the sigma recursion, kernel drift `6.1e-07`)
was found and fixed. Ideal-to-discrete gaps stay registered (GL
quadrature choice, numerical owner list, window vs integral, float solve
vs exact solve).

## 2250 — per-node count uniformity

Record [2250](../proofs/2250_routea_weighted_zero_pernode_count_uniformity.md)
extends the 2245 count brick to all 30 construction nodes with
window-framed family-height counts `[|h| - a, |h| + a]` (mirrored,
non-cumulative). Worst-node bound `<= 8` unconditional (node 26,
`h = 72.0671576744819`), densest window 2 true zeros (node 1, the
`rho + 1/2`-target family, `gamma_6 + gamma_7`); histograms `{0: 3, 3: 1,
6: 1, 7: 21, 8: 4}` and `{0: 5, 1: 17, 2: 8}`; the ball-window row
reproduces the 2245 stress values bitwise (`26 / 21`). Worst per-node
ratios `8/62` and `2/62` against the ball-window `26/62` and `21/62`. The
charge half of the transfer stays open.

## 2251 — certified per-node isolation and local uniform-in-rho separation

Record [2251](../proofs/2251_routea_weighted_zero_separation_certified.md)
upgrades the 2247 separation input: 21 Hardy-Z sign-change brackets
(bisected to width `<= 5.293955920339377e-25`, min pairwise gap
`1.4401493697908734`, no coordinate conflicts, refined endpoint margin
`2.91e-26` against a `1e-58` evaluation error), per-target minima
`1.7246687029005743 / 1.7246687029005743 / 1.915589239572187` (bitwise
the 2247 candidate-1 numbers), floors
`0.0030755954591358543 / 0.009608984322583001 / 0.0007699022126940044`.
Local uniform-in-rho lemma: for `|rho' - rho| <= eps_rho =
0.18587152073670352` the node set is unchanged and every separation is
`>= 1.3529256614271667`, the 2157 floor `>= 0.0015137680096211589`.
Global uniformity remains open.

## 2252 — Lean brick: item-5 transfer arithmetic

Record [2252](../proofs/2252_routea_weighted_zero_item5_arithmetic_lean.md)
lands `ConnesWeilRH/Dev/C1RouteAItem5Arithmetic.lean`: the 2248 tail,
2109 known-error sum, 2245 count ratios, and 2249 certified margin frozen
as constants, four `norm_num` theorems (two strict arithmetic slacks
`943.406... / 963.747...`, two strict signed-margin conclusions). Module +
probe build `3521` jobs, full library `4148` jobs, both exit 0; axiom
audit `[propext, Classical.choice, Quot.sound]` for all four. The numeric
inputs remain artifact-level facts.

## 2178 algebraic infinity remainder

Record [2178](../proofs/2178_routea_infinity_algebraic_remainder.md) replaces
the floating-point-underflow remainder in the fixed order-48 tail screen by an
explicit two-sided algebraic integral.  On the one-copy G8-H numerical owner,
the bound for `|xi| >= 10^6` is `6.9025590685960082e-974`, or
`1.5644201794645804e-984` of the inherited L2 charge.  This closes the
infinity-remainder sub-obligation at the candidate-owner level and evaluates
both signs with the complex polynomial modulus.

The record is not a producer Go: the N48 interval candidate, shifted-Stirling
envelope, stored-float coefficient path, complete-owner transfer, finite-window
signed margin, and selected-detector compatibility remain open.  It is a
strictly smaller quantitative tail obligation and does not promote `A.005.1`.

## 2179 exact-rational N48 audit

Record [2179](../proofs/2179_routea_n48_rational_horner_audit.md) independently
rebuilds the order-48 numerator with exact rational coefficients and Horner
intervals.  The deliberately coarse sign-free enclosure has
`log10 N48 = 146.2702132174163`; after repricing the 2178 algebraic tail, the
two-sided tail is still `10^-681.522...`, or `10^-692.166...` of the inherited
L2 charge.  The tail margin therefore does not depend on the mpmath `N48`
candidate or on exponential underflow.

This is a tail-margin pass only.  The finite-window signed budget and
complete-owner transfer remain open.

## 2180 exact-rational Sturm completeness

Record [2180](../proofs/2180_routea_root_sturm_audit.md) uses a 143-term
Fraction Sturm chain to verify 64 roots in `(-1,1)`, one in each of the 64
2066 intervals, and zero roots in every gap.  This closes the root-completeness
premise of the sign partition; it does not close the selected-detector
producer.

## 2253 — per-node charge uniformity falsified; count-free fallback

Record [2253](../proofs/2253_routea_weighted_zero_pernode_charge_falsification.md)
measures the only canonical per-node split of the binding screen channel
(absolute-value decomposition over the 30 construction nodes): the heaviest
zero node costs `97.03078624970799 x` the uniform budget `tail/62`
(`1.57 x` the whole tail), all-nodes max `207.1204982551802 x` (node 0),
and the 21 zero nodes together `6.199637763470248 x` the tail.  The
`owner/62` transfer factor of the 2246 ledger is withdrawn.  The count-free
Lean bound (`4 * mult * B`, no count factor) gives the fallback ledger:
charge `4968695278.066621`, reading `0.0029656840176851677`, eps0
`1670427351110.207` at the 2249 margin.

## 2254 — certified separation screen and local uniform-in-rho disks

Record [2254](../proofs/2254_routea_weighted_zero_separation_screen.md)
upgrades 2251 to all three 2103 stress configurations: 72 Hardy-Z brackets
(max width `5.293955920339377e-25`, min endpoint margin `2.9109288740357516e-26`),
certified separations `1.7246687029005743 / 1.283770840521257 /
2.380992966914272`, local disks `eps_rho = 0.18587152073670574 /
0.2613019397045188 / 0.2499569408768854`, local floors (min over targets)
`0.0003688351374802202 / 0.00038388813750691464 / 0.00020275988007744964`.
A continuum uniform-in-rho statement is obstructed at ball-edge ordinate
crossings (the edge `gamma + R` sweeps across three ordinates per step,
in-ball added `12 -> 15 -> 18`; `eps_rho` degenerates at each crossing);
the discrete screen is certified member by member instead.

## 2255 — ideal-to-discrete gaps measured and charged

Record [2255](../proofs/2255_routea_weighted_zero_l1_gaps.md) measures the
registered L1 gaps by refinement doubling: quad `m 6400 -> 12800`
(`delta q = -127417.24731445312`, gap `2690487.8687415244`), window ring
`40 <= |x| <= 80` (`delta q = -1.8895946191892285e-16` — the truncation is
below the committed `E_total`, `|g(+=40)| = 5.86e-20`; gap
`1281535.3012791811`), step `0.02 -> 0.01` (`delta q = 52.992919921875`,
gap `2565926.579282266`).  Total `6537949.749302972`; the gap-adjusted
margin reprices the transfer-free reading to `0.00296569559081069` with
`eps0 = 1670420813160.4578`.  The charges are deliberately redundant (the
committed `E_total` is charged in each channel) and are refinement
estimates, not analytic bounds.

## 2256 — terminal item-5 ledger; stored-solve residual audit

Record [2256](../proofs/2256_routea_weighted_zero_item5_terminal_ledger.md)
assembles the terminal ledger — margin `1675396046388.2737`, gap
`6537949.749302972`, full-tail charge `4968695278.066621`, reading
`0.00296569559081069`, `eps0 = 1670420813160.4578` — and freezes the Lean
constants (`gapCharge2255 = 1e7` measured-rounded-up, `eps0FullTail2249 =
1.67e12`, strict arithmetic slack `417351110.20703125`).  The
stored-operand residual audit closes convention A operationally: relative
residuals `2.3301336946878703e-29 / 2.0074563404256314e-29` (backward
consistency; condition `265373.1999607843`), with the forward amplification
`cond * u ~ 5.9e-11` explicitly left to convention A.

## 2257 — count-free Lean assembly of the producer gate

The item-5 terminal consumer is repriced in count-free form.
`ConnesWeilRH/Dev/C1RouteAItem5Arithmetic.lean` freezes the 2243 screen
constant `bUpper2243 = 9506275.102584327` and the 2240/2248 multiplicity
proxy `multProxy2248 = 128.70692502980964` and proves, by `norm_num`:
`4 * multProxy2248 * bUpper2243 <= highShellTail2248` (the exact rational
product sits `6.32e-6` below the frozen tail — the tail is the rounded-up
bound, so this is a strict inequality, not an identity), its monotone
generalization over any `mult <= multProxy2248` and nonnegative
`B <= bUpper2243`, and the terminal theorem
`a005_item5_terminal_count_free` consuming the bound shape
`charge <= 4 * mult * B + knownError2109` directly — the exact shape
delivered by `exists_weightedZeroMeasure_highShell_tsum_bound`.  No count
factor enters anywhere; the `owner/62` transfer theorems remain as
history.  All ten audited theorems are axiom-clean
(`propext, Classical.choice, Quot.sound`); the numeric tie
`spectralMultiplicityConstant <= multProxy2248` stays an artifact-level
fact (the constant is transcendental).

## 2258 — cancellation-aware split recon

Record [2258](../proofs/2258_routea_weighted_zero_cancellation_split.md)
reconstructs the four 2234 sigma rows as cancelled signed L1 norms
(relative error `1.77e-15` against the committed MPFR anchors) and prices
the canonical cancellation-aware splits.  Cancellation factors
`19.25 / 64.55 / 10.30 / 61.12`; the pro-rata two-sided split fails at max
diagonal ratio `8.1166` (channel a) / `9.0918` (channel b) with 3/30 nodes
over budget while its total charge is only `0.1997 / 0.2241` of the screen
product — localization, not total; node 0 `(1.60, -39.25)` carries
32.0–41.7% of every row.  Mandatory floors are ~0 (`<= 0.00288` singleton,
`<= 8.7e-3` top-3 coalition, in budget units): the failure is an
allocation-design gap, not mandatory integrand mass.  Flat-factor splits
are structurally impossible (`>= 62/30`) and per-factor-bounded splits die
on the all-node Hall condition (30 nodes < 62 slots); the coalitional Hall
LP stays registered open.  The `owner/62` transfer stays withdrawn; the
count-free assembly of 2257 remains the live route.

## 2259 — rigorous Arb re-certification of the Hardy-Z brackets

Record [2259](../proofs/2259_routea_weighted_zero_brackets_arb.md)
re-derives the 2251/2254 separation input with certified ball arithmetic
(python-flint `acb.zeta` / `acb.lgamma`, 200-bit, arb bisection on
certified signs, IVT): all 72 brackets re-certified (21/24/27), max width
upper `1.6543612251060554e-26`, min pairwise gap lower `1.383836594509236`,
min certified endpoint margin `8.656304746693204e-28`; the nonzero kill
pin at `27.67032193035704` is certified with `|Z| >= 2.8451013491344974`.
The screening values reproduce 2254 to 15 digits with ball-grade
enclosures.
