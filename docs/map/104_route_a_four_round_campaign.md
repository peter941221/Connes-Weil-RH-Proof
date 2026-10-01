# 104 — Route A: selected-owner signed physical-kernel campaign

Date: 2026-09-24.

Status: active campaign. Round 1 is FORMAL. Round 2 now has a FORMAL
physical-derivative-controlled selector, but its signed margin remains OPEN.
The former current-API no-go has been removed by this new owner construction;
the analytic sign obligation itself is not yet closed.
This record is subordinate to [003](003_b1_b5_minimal_exit_route_selection.md),
[080](080_c3p_signed_certificate_owner.md), [081](081_orbit_physical_kernel_coboundary_certificate.md),
and [082](082_direct_semilocal_gate_assault.md). RH is not claimed.

Current owner guard (2026-09-30, record 2276): the legacy 2267 strip
envelope uses width-a physical profiles, while the 2249 transform uses
width-a^2 profiles. The numerical coefficient vectors agree but the
functions do not. That envelope is not a supplier for the current
owner's hstrip. The generic Lean producer remains conditional and valid.

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

## 2240 — Historical multiplicity proxy audit (corrected in 2274)

Record [2240](../proofs/2240_routea_weighted_zero_multiplicity_constant_formal.md)
audits the `spectralMultiplicityConstant_proxy` carried since 2234. Record
2274 withdraws its exact identification with the Lean
`spectralMultiplicityConstant` (`ConnesWeilRH/Dev/C1SpectralSummability.lean:348`,
with `xiGrowthFixedConstant` at `:38` and `kernelSmallMomentConstant` at
`:29`, tail constant `ConnesWeilRH/Source/CC20ZetaCounting.lean:85`),
because the historical binary64 reading `301.83032993648527` used the
standard half-normalized value `pi/6`. The project value is `pi/3`;
bitwise agreement at relative `0.0` shared the wrong convention. The
`4 *` factor is still the `3/4` geometric assembly of
`exists_weightedZeroMeasure_highShell_tsum_bound`. The historical
calculation's flat slack was
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

## 2260 — producer-side assembly recon: the count-free chain and its single remaining lemma

Record [2260](../proofs/2260_routea_weighted_zero_producer_assembly_recon.md)
is docs-only: it traces the proved count-free chain leaf to root
(`C1SpectralWeil.lean:248/275/385`,
`C1RouteAWeightedZeroMeasure.lean:117/158/219`) and verifies that the
screen lane computes exactly the chain's constant.  The 2197 header
formula `C <= min(‖base''‖₁ ‖corr‖₁, ‖corr''‖₁ ‖base‖₁)/(2π)²`
reproduces the frozen constants: `(2π)² · 77444.14398633591 =
3057372.2573045553` bitwise equals the 2197 `B_upper`, and `(2π)² ·
240796.76135588222 = 9506275.102584315` against the frozen 2243
`B_upper = 9506275.102584327` (relative difference
`1.175630914820416e-15`, the frozen value rounded up).  The producer-side
obligation is therefore exactly one Lean lemma — the direct-product
decay estimate for the concrete factorization, i.e. that the compactness
constant of `exists_spectral_laplaceAt_quadratic_bound` can be taken as
the min-product of the factor L¹ norms over `(2π)²` — with count-freeness
automatic (the factor norms contain no zero count).  The 2257 consumer
already consumes the `B_upper` side; this lemma is the last formal gap
between the proved chain and the concrete screen constants.

## 2261 — coalitional Hall screen of the direct-product rows

Record [2261](../proofs/2261_routea_weighted_zero_hall_screen.md)
computes the decidable pieces of the 2258 allocation question on the
committed grid: the greedy coalition scan gives single-factor lower
bounds `2.1475 / 5.5627 / 2.5011 / 5.4124` (rows `base_M0 / corr_M0 /
base_D2 / corr_D2`, coalitions of size `28 / 9 / 18 / 8`), all above the
exact pigeonhole `62/30 = 2.0667`; hence every single-factor split of
every row exceeds the uniform budget by at least `max(found, 62/30)`.
The `parity` and `halves` partitions are disjoint self-covers on both
sides of all four rows (both Hall ratios `<= 0.0067` of budget), so the
pointwise-universe product split is degenerate there: feasibility must be
posed on the fixed analytic per-node pieces.  The `theta_sign` split is
emphatically not a self-cover (the shield side alone carries Hall ratios
`8.38 / 62.0 / 36.10 / 62.0`).  The coalitional Hall LP stays registered;
the count-free assembly of 2257/2260 remains the live route.

## 2262 — directed MPFR ball-ization of the 2258 split quantities

Record [2262](../proofs/2262_routea_weighted_zero_cancellation_split_ball.md)
replaces every 2258 reading by a certified one-sided enclosure at 256-bit
MPFR along the 2234 path (one `nextafter` guard per operation; no
accumulated-drift correction needed).  Certified intervals bracket the
readings — `base_M0 [19.25392469924447, 19.25392469936748]`, `corr_M0
[64.55476819263616, 64.55476819302037]`, `base_D2 [10.296262425921586,
10.296262425988186]`, `corr_D2 [61.12031609013271, 61.120316090533244]`
— and every failure count is reproduced exactly at the certified lower
ratios (rows `10 / 4 / 11 / 4` nodes over budget; channels `a` and `b`
both `3/30`), with 0 ulp reading residuals over norms/triangles/shares/
family masses (all four anchors `>=` the certified lower norms) and
certified mask decisions (min `|q - 0.04| = 1.819057697104165e-06`, 0
disagreements, 0 undecided).  The certified floor-ratio uppers are all
`<= 0.00288` of budget (the float64 floor readings are cancellation
noise at the `S ~ 1e19` scale, kept for audit only).  Two extraction
laws became canonical: the phi-underflow law (strictly positive
magnitudes take directed RNDU/RNDD conversions with relative-only pads —
absolute pads leak `2^-52`-scale garbage amplified by `hypot(g,h)` in
the deep-`phi` band) and the hypot box law (lower bounds via
`hypot(boxmin|g|, boxmin|h|)`; the naive nonnegative-part form collapses
the dominant `h ~ 0, g < 0` zone and loses an order of magnitude).  The
2258 conclusions survive interval certification.

## 2263 — Arb certification of the census non-zero pins

Record [2263](../proofs/2263_routea_weighted_zero_census_arb.md)
completes the 2259 extension to the kill-list non-zero side: all 18 pin
instances at the three candidates certify `xi != 0` — 15 by `acb` balls
(smallest certified lower bound `9.227272168362652e-13`; per-candidate
minima `5.547830231357397e-11 / 4.354577967736868e-12 /
9.227272168362652e-13`) and 3 at `s = 1` by the classical exact
`xi(1) = 1/2` (the pole point: `acb.zeta` is indeterminate and interval
arithmetic cannot cancel `(s-1) zeta(s)`).  Distinct geometry: 3
real-axis pins (`|xi(0.5)| >= 0.4971207781883137` = classical `Xi(0)`;
`|xi(1.5)| >= 0.5087310387263231`), 6 off-line pins in
functional-equation mirror pairs, and the kill pin re-certified at
`|xi| >= 3.8781880974656257e-07`, consistent with the 2259
`|Z| >= 2.8451013491344974`.  The 2245 census classification is now
ball-checked end to end: zeros by certified brackets, non-zero pins by
certified lower bounds (the mpmath `siegelz` rule remains the
classifier, not the certificate).

## 2264 — sigma-range audit: frozen constant vs the centered strip

Record [2264](../proofs/2264_routea_weighted_zero_sigma_range_audit.md)
audits the convention gap between the committed screen and the Lean
chain: the chain evaluates `laplaceAt F` at
`centeredXiCoordinate ρ = (ρ.re - 1/2) + i ρ.im`, i.e. at Laplace real
parts `σ ∈ (-1/2, 1/2)`, while the 2197/2234/2243 envelope tabulates
`σ ∈ [0, 1]` certified at `σ = 1`.  Raw binary64 re-measurement over
`σ ∈ [-0.6, 1.1]` (341 points) reproduces the committed 2197 binding row
at `σ = 1` bitwise (relative deviation `0.0` on all four norms) and
finds: max min-product over `[0, 1]` = `3057372.2573045553` at
`σ = 1` (the raw 2197 number, channel b); over the centered strip
`[-1/2, 1/2]` = `2874525.124523096` at the edge `σ = -1/2` (channel b),
which is `0.302382` of the frozen `bUpper2243 = 9506275.102584327`,
margin `3.3071x`; over `[-0.6, 0]` = `2901133.1486646286` at `-0.6`,
still `0.305181` of frozen.  Verdict: **COVERED at screen grade** — the
frozen constant dominates the centered strip with the screen's own
headroom.  The certified envelope on `[-1/2, 1]` (2234-style panel /
coefficient / Lipschitz re-run) remains the registered numeric obligation
before the tie holds at certified grade.

## 2265 — Lean brick: the direct-product decay estimate (producer lemma)

Record [2265](../proofs/2265_routea_weighted_zero_direct_product_decay_lean.md)
lands the 2260 single producer-side lemma.
`ConnesWeilRH/Dev/C1RouteADirectProductDecay.lean` defines the strip
functionals `stripNorm σ f = ∫ e^{σx} ‖f‖` and
`stripSecondNorm σ f = ∫ e^{σx} ‖f''‖`, proves the two-IBP identity
`s² ∫ e^{sx} f = ∫ e^{sx} f''`, the per-factor bound
`t² ‖∫ e^{(σ+it)x} f‖ <= D2_f(σ)`, the min-product quadratic bound
`‖t/2π‖² ‖L(b⋆c)(σ+it)‖ <= min(D2_b·M_c, D2_c·M_b)(σ) / (2π)²`, and the
producer-shaped corollary `laplaceAt_convolution_spectral_bound_of_strip`:
a strip-norm envelope `B` on `σ ∈ [-1/2, 1/2]` gives, for every source
nontrivial zero, `‖ρ.im/2π‖² ‖L(b⋆c)(centeredXiCoordinate ρ)‖ <=
B / (2π)²` — the exact shape of
`exists_spectral_laplaceAt_quadratic_bound`.  The earlier convention
mismatch is resolved at the interface: the hypothesis is stated on
precisely the strip the chain uses, and the numeric envelope enters only
through `hB` (screen-grade value by 2264).  All 9 declarations are
axiom-clean (`[propext, Classical.choice, Quot.sound]`); module + probe
build `3518 jobs`; log
`build-logs/routea_direct_product_decay_20260930.log`.

## 2266 — Exact two-end Hall enumeration with certified middle brackets

Record [2266](../proofs/2266_routea_weighted_zero_hall_exact.md) upgrades
the 2261 Hall screen to exact enumeration at both ends of the curve
(exhaustive for `k <= 6` and, via complements, for `k >= 24`; fork-
parallel chunked matmul, `k = 30` reproducing the row norm bitwise) plus
certified ceilings in the middle, the four-way minimum of trivial
(`62/k`), mass, cover, and a new complement-m-smallest bound
`∫ (|G| - L_m)^+` (`L_m` = pointwise sum of the `m = 30 - k` smallest
family magnitudes; every excluded complement of size `m` dominates it
pointwise).  Result: `base_M0` is now EXACT —
`t* = 2.1475067585012337` at `k = 28` (its maximum lies in the
complement-exact range and every middle ceiling stays below it); the
other three rows are bracketed to relative width `<= 4.8e-4`:
`corr_M0 [6.1624990602415091, 6.1654080613840732]` at `k = 8`,
`base_D2 [2.6403870620083922, 2.64068660502853]` at `k = 17`,
`corr_D2 [6.0894516916697183, 6.0917247299667272]` at `k = 7` (upper
ends certified ceilings, binding bound always complement-m-smallest;
lower ends 1-swap climbs from greedy prefixes).  The best coalitions
beat the 2261 greedy bounds by `5.6% / 10.8% / 12.5%` on the three open
rows, so the certified single-factor infeasibility factors rise to
`2.1475 / 6.1625 / 2.6404 / 6.0895` against the pigeonhole floor
`62/30`.  All cross-checks green on every row: greedy vs 2261 bitwise
(`rel 0.0`), `k = 30` vs row norm `rel 0.0`, exact-range monotonicity,
ceilings `>=` exact, `ub >= lb` throughout.  A direct MILP encoding of
the exact problem remains unavailable (positive-part epigraph maximizes
unboundedly; disjunctive form needs one binary per grid node); the
two-end enumeration + certified ceilings is the sound replacement.

## 2267 — Certified centered-strip envelope of the direct-product screen

Record [2267](../proofs/2267_routea_weighted_zero_sigma_envelope_certified.md)
discharges the numeric obligation left open by 2264/2265: the certified
envelope of the two-channel product
`N(σ) = min(D₂_b·M_c, D₂_c·M_b)(σ)` on the centered strip
`σ ∈ [-1/2, 1/2]` at the frozen constant
`bUpper2243 = 9506275.102584327`.  The reduction is the 2234/2243
machinery run over the full `j = -50..50` grid (`σ = j/100`; the 50
negative-σ point sums are fresh 256-bit MPFR sigma-worker runs over the
committed per-node upper chunks), with the panel and coefficient
inflation in the σ-symmetric form (support-supremum weight
`e^{|σ|a_max}` and cross term `2|σ| m_{k+1}`, reducing to the 2243
form at `σ >= 0`), and the grid coverage applied once at the end by the
log-derivative transfer `|d/dσ log N| <= 2 a_max` at half-step `0.005`
(`factor 1.0259304941903822`).  Result: **CERTIFIED-STRIP-COVERED** —
certified sup `6663660.437141987 <= 9506275.102584327`, margin
`1.4266x`; the maximum grid point sits at the strip edge `σ = -1/2`
(channel a binding, because the corr-side D2 inflation is dominated by
the 2237 radius `r_corr ≈ 2.057e9`).  Anchors: the `σ = 1.0` row
recomputed through this reduction reproduces the 2243 binding row
`C_upper` bitwise (`rel 0.0`); all 101 certified point sums are uppers
of the 2264 raw readings (`rel_max 2.44e-15`).  Combined with the frozen
2234 reduction's own certified envelope on `[0, 1]`, the union
`[-1/2, 1]` is covered at the 2243 standard, superseding the 2264
screen-grade audit.

## 2268 — Producer-side wiring of the direct-product decay brick

Record [2268](../proofs/2268_routea_weighted_zero_producer_wired_lean.md)
wires the 2265 producer brick into the 2257 count-free consumer chain at
the frozen constants.  `ConnesWeilRH/Dev/C1RouteAProducerWired.lean`
proves: `directProduct_dyadic_shell_bound` (the per-shell dyadic tail
with `bUpper2243`, mirroring `exists_spectral_laplaceAt_dyadic_tail_bound`),
`directProduct_weightedZeroMeasure_shell_bound` (the frozen re-run of
`exists_spectralHeightShell_weightedZeroMeasure_bound` with
`F = b ⋆ c`), `directProduct_highShell_tsum_bound` (the high-shell
weighted-zero tsum `<= 4 · spectralMultiplicityConstant · bUpper2243`),
and the end-to-end `a005_item5_producer_wired`, which places the actual
high-shell tsum of `b ⋆ c` inside `a005_item5_terminal_count_free` and
reduces the chain to four explicit inputs: the strip hypothesis (2267's
certified target), the count-side
`spectralMultiplicityConstant <= multProxy2248`, and the 2249/2109/2255
analytic enclosures.  All four theorems are axiom-clean
(`[propext, Classical.choice, Quot.sound]`); module + probe build
`3524 jobs`.

## 2269 — Ball-grade Hall quantities for the four direct-product rows

Record [2269](../proofs/2269_routea_weighted_zero_hall_ball.md) re-runs
the 2262 directed-MPFR node machinery and ball-izes the Hall quantities
2266 bracketed in float64.  Per node and row it accumulates the witness
coalition Hall pair (the 2266 convention `Hall(J) = ∫ w (AG - Σ_{j∉J}
M_j)^+`, i.e. the complement's magnitudes are deducted), the full
complement-m-smallest table `ms[m] = ∫ w (AG - L_m)^+` for `m = 1..30`
via the sorted-domination law, and the norm/triangle/weight pairs, all
with one-sided guards.  Result: **HALL-BALL-CERTIFIED** — all four rows
carry certified two-sided brackets, each containing the 2266 float
bracket with both ends within `2e-11`: `base_M0
[2.1475067584947944, 2.147512373192978]`, `corr_M0
[6.162499060223501, 6.165408061402101]`, `base_D2
[2.6403870620001513, 2.6406866050367617]`, `corr_D2
[6.0894516916512975, 6.091724729985202]`.  The certified upper is valid
at every `k` through `min(62/k, 62·msmall_u[30-k]/(k·norm_lo))` alone
(the other 2266 ceiling components are not re-certified and not
needed); the witness Hall readings reproduce the 2266 float64 values to
`<= 1.6e-12` relative; anchors green (0 mask disagreements, certified
mask margin `1.82e-06`, norm/triangle inside the 2262 certified
intervals, weight sum bitwise).  The `base_M0` certified upper
(`2.147512373192978`) sits `2.6e-6` above the float "exact"
`2.1475067585012337` — the price of not re-verifying the exhaustive
enumeration in directed arithmetic; the other three rows certify at
exactly their 2266 widths (ceiling-limited).  The single-factor
infeasibility factors are now certified at both ends.

## 2270 — Exact middle-k enumeration for the two open Hall rows (reserve)

Record [2270](../proofs/2270_routea_weighted_zero_hall_middle_exact.md)
runs the reserve exact enumeration registered by 2266: the two deciding
middle `k`'s of the open rows are swept exhaustively on the committed
float64 machinery with one full `combinations` index table per job
(`corr_M0` `k = 8`, `C(30,8) = 5,850,925` subsets; `corr_D2` `k = 7`,
`2,035,800`).  Result: **MIDDLE-EXACT-CONFIRMED** — the exact maxima
`726.3375614016927` (ratio `6.1624990602415135`) and
`1049250.3213751798` (ratio `6.089451691669726`) land within `7.1e-16` /
`1.3e-15` relative of the 2266 climb lower ends, and the exact argmax
witnesses are *identical* to the 2266 `witness_idx` on both rows
(`{0,1,11..16}` and `{0,1,12..16}`).  The 2266 climbs were globally
exact at the deciding `k`; the remaining 2266 bracket widths
(`4.72e-04` / `3.73e-04`) are entirely ceiling slack, and only a sharper
certified ceiling or a directed-MPFR exhaustive run could narrow them.
Cost calibrated for future budgeting: `2472.6 s` + `878.1 s` =
`3350.6 s` wall.  Certified-grade statements of the same quantities are
2269; the certified upper ends are unchanged.

## 2271 — Strip replay controls and fail-closed verdict

Record 2271 closes the 2267 artifact reproducibility gap. The 50 negative-
sigma inputs are versioned, the exact stored binary64 construction operands
are committed, and a 123-file SHA-256 manifest binds the replay to its
parameters. The 2267 consumer now refuses to report
CERTIFIED-STRIP-COVERED when an input or anchor fails; it emits
STRIP-CONTROL-FAIL instead. The control suite passes 22 tests, including a
real anchor-failure injection. This is evidence hygiene only: the strip
envelope remains an artifact-grade input to the Lean FrozenStripHypothesis,
not a Lean proof, and no producer GO or RH claim is made.

## 2273 — Multiplicity proxy rounding correction

WITHDRAWN by record 2274: the 2273 diagnostic substituted the standard
half-normalized xi value `pi/6` into the project's doubled-xi expression.
Lean proves the project value is `pi/3` and the multiplicity constant is
at most `128.65`; the former proxy `128.70692502980964` is therefore safe.
The slightly increased proxy `128.70692502981` and tail `4894093747.7643`
remain conservative, but their increase was not mathematically necessary.
The original diagnostic is preserved as superseded evidence; the current
script and artifact use the project normalization.
No producer GO, no gate sign change, and no RH claim.

## 2272 — Mathematical-core closure order

Record 2274 discharges hmult and supplies a producer consumer without that
argument. The original conditional theorem remains for existing callers.
The residual hypotheses are hstrip, hmargin, hcharge-rest, and hgap.
These remain proof obligations. The closure order is now:

1. COMPLETED in 2274: the Lean theorem proves
   `spectralMultiplicityConstant <= 128.65 <= multProxy2248`.
2. Replace the refinement-measured 2255 gap charge with an analytic error
   enclosure; the measured refinement delta is not itself a proof bound.
3. Consume the 2267 strip envelope through a formally checked certificate
   interface. The replay manifest establishes provenance, not analytic truth.
4. Return to the selected detector and prove the same-owner signed
   `qw >= 0`, including the finite prefix, signed physical-kernel term, and
   tail remainder.

The Hall enumeration branch remains reserve infrastructure because the
count-free fallback already supplies the producer shape. Route D
operator-sign and identity-split mechanisms remain closed under the existing
no-go records. No producer GO, no gate sign change, and no RH claim.

## 2274 — Multiplicity comparison proved; xi normalization corrected

Record [2274](../proofs/2274_routea_multiplicity_bound.md) proves the exact
project identity `completedRiemannXi(2) = pi/3`, the Gamma and kernel
component bounds, and `spectralMultiplicityConstant <= 128.65`. This
discharges `hmult` without a numeric artifact hypothesis.
`a005_item5_producer_wired_certified_multiplicity` consumes the result for
the same tests, same shell sum, and unchanged signed-margin budget; its
arguments retain only hstrip, hmargin, hcharge-rest, and hgap. The original
conditional consumer remains available. The original-proxy theorem also
formally refutes the 2273 under-rounding interpretation.

The final build covers the new paired audit, producer probe, and root
aggregate (4244 jobs); all 15 audited declarations use only the permitted
axioms. Seven multiplicity regressions and all 22 Linux strip controls
pass. The reviewed replay manifest now binds 126 files; the strip replay
keeps its numerical rows and anchors unchanged, with only provenance and
input-validation metadata updated.

The next unresolved item is the analytic hgap enclosure, followed by the
formal strip certificate and the selected-owner signed inequality. This
is one removed producer premise, not producer GO or an RH proof.

### Record 2275: hgap inference audit; analytic supplier still open

Record [2275](../proofs/2275_routea_gap_owner_audit.md) reconstructs the
2249 coefficient vectors and matches both original MD5 anchors exactly.
The captured binary64 vectors, target nodes, family parameters and rule
hashes are available in results/2275_gap_owner_audit.json. This captures
the numerical owner; it does not identify it with a selected Lean detector.

The 2255 quad refinement changes the rule AND re-solves both vectors.
The finite-rule ring cannot supply an ideal infinite tail: its nonzero
family sums recur exactly, with common phase period
T = (pi / pi_stored) * 2^106 for these stored tables. An exact positive
polynomial has equal zero coarse/fine trapezoids but integral 20000000,
so agreement plus arithmetic bars alone cannot establish the 1e7 gap cap.
This freezes only those inference mechanisms, not the actual ideal gap
or the CompactLog producer. Record 2255's window-exact/resolved wording
is withdrawn; its numeric artifact remains historical and unchanged.

The analytic bridge now explicitly separates ideal tail, same-coefficient
window rule error, analytic trapezoid remainder and stored-coordinate
transfer. The stored grid differs from -40+j/50 by at most
55/4398046511104. The basic C2 window bound is M2/375, where M2 bounds
the second derivative; using all 1e7 on it would require M2 <= 3.75e9.
No derivative cap, ideal-tail cap, owner readback or hgap theorem is
claimed. Ten exact/provenance controls pass. The live task remains a
fixed-owner analytic supplier, not another refinement ledger or a
conditional wrapper. hstrip, hmargin, hcharge and hgap remain open.

### Record 2276: physical-scale owner no-go; analytic majorants priced

Record [2276](../proofs/2276_routea_owner_scale_price.md) identifies the
ideal integral underlying 1980/2249 by y = a*x: its physical bump width
is a^2, not a. At y = 6 every legacy family vanishes, while exactly
stored family 4 survives at squared width with nonzero base/corr
coefficients. C1RouteAOwnerScaleAudit proves the support mismatch and
its stored-entry specializations; all eight paired audit declarations
use only the permitted three axioms. The 2943-job build succeeds.
The paired audit plus root aggregate also pass together (4283 jobs).

This rules out transfer of the 2267 envelope to the 2249 ideal owner;
2267's raw artifact and replay are preserved as legacy-input evidence.
The new comparison finds zero coefficient-component mismatches, so the
failure is profile scale, not a different solve or rounding convention.

For the correctly scaled, same-stored-coefficient functions, directed
MPFR evaluates analytic absolute-family strip and ideal two-sided tail
majorants. Their upper expression endpoints are 1.907160891918978e13
(2.006e6 times the frozen strip cap) and 1.005130285058951e41 (1.005e34
times the gap cap). These figures price a rejected sufficient-bound
method, NOT lower bounds on the true norms/tail. The tail keeps the
frozen visible-prime kernel and does not establish selected-detector
readback or its support-derived prime set. Thirteen new controls pass.

The live order is now: bind the squared-width CompactLog functions and
the selected owner/visible set; preserve cancellation in corrected-owner
analytic pricing; prove the complete window, ideal-tail and grid bridge;
only then attach an hgap supplier. No generic conditional wrapper is
added, no producer premise is removed by this record, and RH is not claimed.

### Record 2277: corrected-owner cancellation screen

Record [2277](../proofs/2277_routea_corrected_cancellation_screen.md)
forms the corrected width-a^2 physical families before taking absolute
values. The refined strip screen reads B = 337039.47691484215, 28.2x below
the frozen strip cap, with refinement movement 1.30e-12. This remains a
numerical screen, not an enclosure.

The same cancellation-preserving D3 norms inserted into the old elementary
tail envelope price 1.285918889357026e25, still 1.2859e18 times the 1e7
hgap budget. The strip lane is promising but the tail method is rejected.
hstrip and hgap remain explicit; no Lean supplier is attached.

### Record 2278: signed-kernel FFT tail screen rejected

Record [2278](../proofs/2278_routea_signed_kernel_tail_screen.md) uses
the corrected width-a^2 support and therefore 41136 visible prime powers,
not the legacy 52-term kernel. The finite signed-kernel FFT screen reads
tiny values on 40 <= xi <= 500, but coarse-to-fine movement is 6.315x
for the signed integral and 5.191x for its absolute integral. The result
is marked FFT-TAIL-UNTRUSTED and cannot close hgap. The next tail route
must use direct oscillatory quadrature or a certified panel rule with a
measured trust horizon.

### Record 2279: direct Gauss-Legendre tail trust horizon rejected

Record [2279](../proofs/2279_routea_direct_oscillatory_tail_screen.md)
replaces FFT with direct composite Gauss-Legendre integration and uses the
corrected support-derived 41136-term kernel. The order-64 to 128 signed
reading changes 4.618x, order 128 to 256 changes 10.307x, and an
independent order-512 to 1024 run changes 4.583x. The instrument is marked
DIRECT-GL-TAIL-UNTRUSTED. The next tail attempt needs interval quadrature,
a transformed oscillatory variable, or a certified remainder formula.

## 2026-09-30 — hgap supplier split after records 2275–2285

The hgap obligation is now split into two independent interfaces. A finite-window
numerical evaluator cannot silently include the infinite xi tail, and an infinite
tail estimate cannot be inferred from sampled refinement.

```text
corrected width-a^2 owner
          |
          +-----------------------------+
          |                             |
          v                             v
finite-window evaluator          infinite xi tail bound
(certified complex enclosure)    (analytic signed-kernel estimate)
          |                             |
          +-------------+---------------+
                        v
             same-owner hgap supplier
```

The evidence has the following meaning:

- Record 2277 preserves cross-family cancellation and finds a strip screen below
the frozen cap, but its tail price is still `1.2859e18` times the `1e7`
hgap budget. It is not a supplier.
- Records 2278 and 2279 reject the current FFT and floating composite-GL
instruments by refinement movement. They do not reject the true tail.
- Records 2280–2283 reject the current unproved Filon profile/residual route.
The generic derivative residual price remains many orders too large.
- Record 2285 corrects a Chebyshev endpoint coefficient bug in 2281/2282.
After correction, binary64 agrees with the 100-digit reconstruction to at most
`2.0121396395e-7` on the sampled transforms. The corrected Chebyshev profile
is still untrusted because its panel/degree refinement changes reach
`484.0690x`; the old arithmetic-failure interpretation is withdrawn.
- Record 2284 rejects bare `mpmath.quad` as a truth oracle: panel magnitudes
are substantial while 35/50/70-digit totals drift by more than `1e14`.

The next admissible evaluator must therefore satisfy all of the following:

1. Preserve the complete corrected owner sum before taking modulus.
2. Use an independently certified complex enclosure, such as Arb/ball or a
proved directed-rounding oscillatory rule.
3. Report panel contributions, enclosure widths, precision movement, and
partition movement separately.
4. Keep the finite window and infinite tail as separate theorem obligations.
5. Pass the same-owner/readback and support-derived `41136` prime-power guards
before any Lean supplier is attached.

Do not continue increasing FFT nodes, GL order, Chebyshev degree, or generic
derivative order without a named enclosure or residual theorem. A numerical
reading without that theorem is a diagnostic only. No producer GO or RH claim
is permitted from these screens.

### Record 2292: derivative-instrument erratum

Record [2292](../proofs/2292_routea_explicit_grouped_fifth_derivative_preflight.md)
withdraws the astronomical prices, direct-interval no-go, and subdivision freeze.
The instrument evaluated exterior families as growing exponentials, used wrong
derivative numerators, took a component maximum instead of a complex modulus,
and omitted panel length. Repaired formulas pass independent containment tests,
but endpoint-crossing cells require the 2293 handler.

### Record 2293: grouped centered derivative and flat-endpoint preflight

Record [2293](../proofs/2293_routea_grouped_centered_derivative_preflight.md)
adds grouped Taylor jets, centre-fifth/sixth-variation bounds, and flat endpoint
envelopes. The 8/16/32-subcell ladder reads a 32-subcell Lobatto interpolation
proxy of `2.02183024e4` for base and `2.39897951e6` for correction; the correction
is 2.71x tighter than same-run direct intervalization. Nineteen tests pass.
These are transform-interpolation prices, not kernel-weighted hgap charges.
Node/moment arithmetic, finite-window quadrature, infinite-xi tail and actual
selected-owner readback remain open. No supplier, producer GO, or RH claim follows.

### Record 2294: uniform independent-radius functional propagation is priced out

Record [2294](../proofs/2294_routea_uniform_radius_functional_floor.md) prices
the 2293 transform radii through an absolute functional majorant. With two
independent uniform radii E/F, the squared-product error majorant has unavoidable
floor E^2 F^2. On the origin cell [-1e-5,1e-5], complete enumeration of all 41136
support-derived prime powers and a nonnegative archimedean sign bound give a
weight-integral floor 3.15754323433e11. At the 32-subcell radii, the chosen
majorant costs at least 7.42833974e32, or 7.42833974e25 times the 1e7 budget.

Freeze this uniform-independent-ball/absolute propagation for windows containing
that cell. The ruling is about the chosen majorant, not actual error, actual
Weil sign, Filon globally, or tail-only intervals. Reopening requires a named
change: a frequency-dependent residual, correlated channels, direct signed
functional difference, or a sufficient radius reduction. The optimistic common
radius-scale ceiling is 3.40625424e-7 (necessary, not sufficient). Ten controls
pass. hstrip/hgap, selected-owner readback and infinite-tail proof remain open.

### Record 2295: direct signed difference rejects the sampled current profiles

Record [2295](../proofs/2295_routea_direct_functional_difference_screen.md)
changes the 2294 independent-ball hypothesis and evaluates the signed functional
difference directly on the same [-40,40] grid, full 41136-term kernel and stored
owner. After repairing near-zero Filon moments and exact grid-zero generation,
the 24:4 profile reads -1.95312399e16 at step 0.01; 24:6 reads +8.10997332e15.
Both are many orders above the 1e7 diagnostic budget, with 256/512 reference-
order agreement and the 0.02/0.01 grid controls retained. Six tests pass.

These are measured profile mismatches, not continuous-integral certificates or
global Filon no-gos. Do not use the transform-only price gate as a functional
gate. The next candidate needs a named representation/profile change and a
same-functional diagnostic before enclosure work. Arithmetic precision alone
cannot repair the current sampled low-degree function mismatch. hstrip/hgap,
the actual selected-owner bridge and infinite tail remain open.

### Record 2296: carrier-separated 192:6 passes the sampled functional gate

Record [2296](../proofs/2296_routea_carrier_separated_functional_screen.md)
changes the 2295 representation: the 25 known carrier phases enter shifted
analytic moments, while envelope polynomials retain all 30 captured families
and both coefficient hashes. Complex carrier contributions are summed before
modulus. The same run reproduces the old 24:4 controls bitwise at steps 0.02
and 0.01, with the full 41136-prime-power kernel.

The carrier-separated 96:6 profile passes the signed diagnostic only. At 192:6,
all six 0.02/0.01/0.005-grid and 256/512-reference controls pass both signed and
absolute sampled diagnostics. Worst absolute difference is 3.33863911e5 =
0.0333864 times the 1e7 budget. Twelve tests pass, including the exact degree-six
Lobatto nodal-product integral 1/32, whose transform remainder target is
M r^8/(32*7!). The signed near-zero difference has no certified sign.

This is a finite-window candidate, not a quadrature certificate or hgap supplier.
Next price the seventh-derivative enclosure and carrierwise cancellation loss;
shape/node/moment arithmetic, certified reference remainder, finite-window
integration, actual selected-owner readback and infinite tail remain open.

### Record 2297: interpolation-only radii clear the origin floor

Record [2297](../proofs/2297_routea_carrier_envelope_remainder_price.md)
prices seventh/eighth envelope derivatives on 192 panels with two cells each.
The base/correction method radii are 2.43880724e-9 / 4.50084236e-6, including
carrierwise triangle loss. The chosen majorant's origin-cell floor is only
3.80444985e-24 times budget. Five independent controls pass, including both
support-edge signs and seventh/eighth derivative orders.

This clears a necessary condition, not the full functional gate. Next price
the full-window majorant before arithmetic certification. Exact partition,
support-radius, node/polynomial/moment arithmetic, continuous integration,
infinite tail and actual selected-owner readback remain open; no hgap claim.

### Record 2298: full-window uniform propagation still overprices 192:6

Record [2298](../proofs/2298_routea_carrier_full_window_propagation_screen.md)
continues 2297 with the full [-40,40] kernel and both transform magnitudes.
The 0.02/0.01/0.005 sampled majorant ratios are 1998.56 / 1999.54 / 1999.65;
the correction-error channel carries about 99.4%. Same-candidate 2296 signed
integrals reproduce bitwise. Six controls cover the error algebra, endpoints,
provenance and ledger.

This is a scoped sampled price failure, not a lower bound on real error or
an analytic no-go. Do not certify the current 192:6 uniform-majorant path.
Next reprice a named 768:6 profile using the summed r^7 remainder scaling,
or change to frequency-dependent/correlated propagation; neither option is
pre-approved as a proof. Exact arithmetic, continuous integration, tail and
actual selected-owner readback remain open.

### Record 2299: 768:6 clears the sampled interpolation-method price

Record [2299](../proofs/2299_routea_carrier_refined_remainder_screen.md)
reproduces the full 2297 baseline panel ledger and 2298 window prices in the
same run, bitwise. The 768:6 base/correction interpolation radii are
3.36711709e-14 / 6.11635156e-11; finest-grid price is 0.02717614 times budget,
a measured 73581.15-fold gain. Seven controls pass. This is interpolation-only
and sampled: executable arithmetic, continuous integration, tail and the
actual selected-owner bridge remain open.

### Record 2300: old coordinate/coefficient bridge consumes the margin

Record [2300](../proofs/2300_routea_carrier_coefficient_bridge_price.md)
uses the exact degree-six Lobatto cosine clock and directed interval envelope
values to compare ideal coefficients with stored binary64 fit coefficients.
The correction coefficient/geometry charges are 2.17023140e-9 / 8.07732452e-9;
combined interpolation plus partial bridge prices at 4.5840351 times budget.
Regenerated coefficients with ideal geometry price at 0.02878483 times budget,
but that alternative is not a complete implemented evaluator and its magnitude
readings are diagnostic. Eight controls pass.

The next named move is regenerated coefficients plus higher-precision physical
coordinates, followed by separate moment/phase/accumulation pricing, not more
panel refinement alone. Both readings remain partial, sampled and captured-
owner only: no hgap, infinite-tail or actual selected-owner claim.

### Record 2301: regenerated executable clears the transform-model price

Record [2301](../proofs/2301_routea_regenerated_carrier_evaluator.md)
implements regenerated degree-six coefficients, extended physical coordinates,
real Horner phase/moment series and a depth-15 streaming pairwise sum. Both
2300 coefficient-cast readings reproduce exactly. The full captured owner and
41136-prime-power kernel are retained. Combined base/correction radii are
1.38378507e-13 / 2.31151627e-10; finest-grid sampled price is 0.10275924 budget.

Ten independent high-precision polynomial checks stay within the execution
allowance, worst ratio 0.0005759913; nine controls cover the new execution path.
This is a declared round-to-nearest model, not a machine or integral certificate.
Kernel/annihilator/functional arithmetic, continuous integration, infinite tail
and actual selected-owner readback remain open. Next target a local-frequency
Taylor enclosure of the full complex transforms, with charged remainders; a
global amplitude cap or sampled grid agreement is not an integral certificate.

### Record 2302: transform cells covered; continuous weights remain open

Record [2302](../proofs/2302_routea_local_frequency_taylor_model.md)
forms frequency derivatives through order six using exact represented y-power
polynomials and moment degrees through twelve. Order zero reproduces 2301
bitwise; higher binary64 derivative paths have separate modeled error charges.
Rational frequency cells cover [-40,40], including stored-midpoint displacement.
The fine-grid base/correction Taylor remainders are 1.30368197e-9 / 2.11703341e-6.

Twenty-four independent derivative controls pass. Eight controls cover moment
parities, y powers, between-node bounds, end coverage and provenance. Sampled-
weight proxy ratios are 0.04944301 / 0.04120909 / 0.04049288. They compare the
original transform against exact regenerated polynomials, not the same
execution-including object priced by 2301; no gain claim between them is valid.

Next enclose the continuous full kernel and annihilator on the same cells,
then sum the cell majorants with directed arithmetic. Arithmetic models,
sampled weights, infinite tails and actual selected-owner readback are still
not certificates or hgap suppliers.

### Record 2303: corrected-owner strip envelope certified at artifact grade

Record [2303](../proofs/2303_routea_corrected_strip_envelope.md) rebuilds the
2267 centered-strip reduction on the corrected physical owner of 2276, whose
profiles are `phi_(a^2)(y) exp(i theta y)`. Only the family-radius interface
changes, because the 2234/2238/2242 machinery is radius-generic. The result is
CORRECTED-STRIP-COVERED: certified continuum sup 2823660.8460007603 against the
frozen `bUpper2243` 9506275.102584327, margin 3.36664904924696x.

All four 2242 pavements are ZERO-FREE-CERTIFIED on the corrected radii and the
single-family edge arc is certified by the exact `e1^2 + e2` factorization. The
raw 2277 reading 337039.47691484215 is reproduced bitwise and every certified
point sum is an upper of its raw row. The binding channel switches to `a` at
sigma = -0.5, so the corrected corr_D2 inflation enters only the non-binding
channel. The frozen constant is unchanged; `hstrip` stays a Lean hypothesis and
the owner-identification bridge remains open.

### Record 2304: flat-edge moment tail; probe-grade no-go with a measured price

Record [2304](../proofs/2304_routea_hgap_tail_moment_probe.md) prices the
infinite-xi tail by flat-edge integration by parts: the profile is flat at its
support edge, so every boundary term vanishes and `|B(xi)| <= V_N/(2 pi xi)^N`.
Verdict TAIL-MOMENT-DEAD at probe grade: the best closed-form bound over the
tested orders is 2.9973776e17 at N = 28, above the 1e7 budget, while the
measured ladder clears the budget by 4.3e12 at N = 20.

The failure is entirely the closed-form sup-ladder: the partition majorant is
1.1229e-11 at j = 1 against a measured 4.5095e-13 and grows to 9.8537e30 at
j = 20. Certification price: a ladder within 74x of the partition majorant at
N = 28, with grouped interval Bell evaluation (2291 law) and sharper partition
algebra as the named suppliers. A probe erratum (inverted `sup_{s<=1}` branch)
was caught and recorded.

### Record 2305: M2 cap and per-cell intervalization both priced out

Record [2305](../proofs/2305_routea_hgap_trapz_m2_probe.md) prices the two
remaining window instruments on the ideal integrand. The 2275 trapezoid cap
needs `M2 <= 3.75e9`; the measured `|Gi''|` reaches 1.610654527471709e15 on the
precision-validated zone alone, so M2-CAP-FAILED by 4.30e5x. The panel-local
sum at the design h = 1/50 is PANEL-LOCAL-FAILED by at least 398x and needs
h <= 1.0e-3. Exact per-cell intervalization of the prime-power cosine sum, the
quartic annihilator and the sigma slope charges at least 1.08e4x budget, so
KERNEL-INTERVAL-FAILED-NEEDS-GROUPING.

The structural result is a precision finding: the corr coefficient scale is
5.69e17 and the float64 family-sum cancellation floor is 3.086636908941589e5,
so float64 loses `|C|` past `|x| ~ 1`; the high-precision control (mpmath,
dps 50-60, bitwise stable) gives `|C|` = 3.0363003090952906e-06,
4.2780015472502136e-10, 9.440112224881565e-16 at x = 1, 2, 4, and the float64
reading at x = 4 is 3.7e3x wrong. The weight lives at `|x| <= 2`, so a
localized directed instrument on `[-2, 2]` is the natural successor to the
global mesh. No verdict uses the unresolved band; no hgap, no route change.

### Record 2306: the grouped flat-edge tail goes live; TAIL-SHARP-COVERED

Record [2306](../proofs/2306_routea_hgap_tail_grouped_sharp.md) rebuilds the
2304 mechanism as a direct grouped instrument and TURNS IT LIVE. The derivative
h_f^{(N)} = e^{lambda_f y} e^{-K/s_f} Q_f is evaluated in the (u, s) variables
with positive powers of s (one log-scaled exponential per Leibniz term); an
expanded y-polynomial form was implemented first and rejected by measurement
(coefficient-magnitude sums up to 1.37e16x the value near |y/R| ~ 0.5). The
enclosure on 11277 rational cells uses honest triangle bounds: the coefficient
triangle on |A_j|, the unimodal sup of e^{-K/s} s^{-m}, and derivative bounds
from the exact ODE identity A_j' = (A_{j+1} - 2u(2j s - K) A_j)/s^2.

Verdict TAIL-SHARP-COVERED at artifact grade. Best bound 2.145448788e-32 at
N = 36 (margin 4.661029457099352e38 on the 1e7 budget); every N >= 16 clears
(N = 16: 553.76, margin 1.81e4; N = 20: 2.620431005e-6, margin 3.82e12), only
N = 8 and N = 12 are dead. The same order-20 cell that read 5.083377274e31
before the u-space rewrite now reads 2.620431005e-6. Grouped inflation:
base 1.008 at the crossing order, corr 4.60; cap-never-binding above N = 32.
Controls: kappa variation moves the bound by <= 1.1e-7 relative over six
decades of kappa; the mpmath Bell-path control puts the base cell bound 4.84x
above the true sup at its argmax; 2304's own rigorous V values reproduce its
recorded tail bounds through the 2306 formula to stored precision. Errata
carried from 2304: the missing 2 R_f length factor and the 416x (not 74x)
price arithmetic.

Scope: this frees the tail half of hgap at artifact grade. The live constraint
on the 1e7 budget is now the finite-window half (records 2295-2302); a
certified window enclosure plus intervalization of this same cell scheme are
the named successors. No hgap certificate, no producer GO, no route change.

### Record 2307: the grouped flat-edge tail is certified; TAIL-CERTIFIED

Record [2307](../proofs/2307_routea_hgap_tail_certified.md) removes the
declared kappa = 2^-30 slack model of 2306 and re-encloses the same grouped
scheme in mpmath.iv interval arithmetic (dps 40, 136 bits): exact big-int A_j,
the monotone-clip S-function sup, certified a1 and C_W closed forms (own
sieve, 41136 prime powers up to 492475), and the exact tail-integral closed
form verified against normalized quadrature (rel 1.32e-20). No sampled
maximum, no float64 on the certificate path.

Verdict TAIL-CERTIFIED. Best rung N = 36 on the 2048 master grid:
1.9586382184619955e-27, margin 5.1055881100147315e+33; the full certified
ladder is N = 16: 6918.973606907223 (margin 1.445301e3, the tightest rung and
the crossing order), N = 20: 2.452555829669849e-5 (4.077379e11), N = 24:
3.362393870024703e-12 (2.974072e18). Any single rung discharges tail <= 1e7.
The certified bounds sit (2-8)e-9 relatively below the float64 bounds on the
same lattice -- the kappa signature, i.e. the certified path carries only
interval inflation (1e-29..1e-40 relative). Certified constants vs the 2306
float64 conventions: a1 upper +0.76 ulp, c_w upper -0.16 ulp, widths
2.3e-40 / 4.6e-37 relative (the certificate resolves both closed forms ~25
orders beyond one double ulp).

The certified lattice is the master grid only (no adaptive refinement; a pure
function of n0 and the family cuts). The 2306 refined-lattice ladder remains
artifact grade; the refinement gain between the columns is 9x (N = 20) to
9.1e4 x (N = 36) and is a cost optimization, not a requirement. Lessons
locked: iv endpoints round outward (verified) but must never be re-rendered
outside a high-precision context; s_lo is the min of the endpoint lowers (an
early max was unsound, caught at a cell reading 3.6e34 vs 9e-134); the
S-clip is the monotone image (a swap fallback inflated ~158 orders); the
prime cutoff floor of e^{2S} needs no margin (+64 primes inflated c_w by
7.5e-5); float64-convention constants differ from the certified forms at the
ulp level and references must be rebuilt from the same float64 terms.

Scope: the tail half of hgap is now numerically free at certificate grade.
The finite-window half stays screen-grade (2295-2302); its certified
enclosure plus the localized [-2, 2] instrument are the named successors. No
hgap certificate, no producer GO, no route change.

### Record 2308: the finite-window weight factor is certified; WINDOW-WEIGHT-CERTIFIED

The 2302-registered obligation -- a continuous kernel/annihilator weight
bound on the window cells, retaining all 41136 prime powers and signed
cancellations before bounding variation, then a directed summation -- is
discharged on the weight side. Per dyadic cell the sup of |kernel| |ann|^2
is enclosed by a degree-4 centre Taylor polynomial of the frozen 2280
kernel convention with certified float64 execution budgets
u[(6j+40) A_j + 40 |c| B_j + 2] (S-moment ladders A_j = sum 2 w phi^j and
B_j = sum 2 w phi^j log n accumulated in mpmath.iv, all 41136 signed terms
grouped before any triangle bound), a certified Lagrange remainder obeying
the exact d^5 law (1.4047 -> 0.04390 -> 0.00137, factor 32.000 per
halving), an interval sigma at the cast-widened true argument, and the
interval product form of the four frozen annihilator nodes (+-4u casts).
The cell charge h * supW * T_cell is summed in mpmath.iv at dps 80, with
T_cell the inherited 2298/2302 perturbation majorant on the same cells.

Certified ladder (dyadic cells, midpoint gap exactly zero -- a strict
improvement over the 2302 decimal grids): denom 64: 863819.2938082191
(0.0864x budget, 2.0026x same-grid proxy), denom 128: 571815.9153523268
(0.0572x, 1.3993x), denom 256: 477248.9862236567 (0.0477x, 1.1828x); the
best certified charge is 1.17860x the 2302 finest sampled proxy
404928.783977559. Charge intervals cohesive to < 1e-38 relative; the
T-side readings are grid-stable (t_sum_max ~ 8.9e-9, max_cell_sup_corr
65.74 -> 65.16), so the decay is weight-side. The kernel sup/center mean
rises at denom 256 (2.73 -> 3.88) while the charge ratio falls: centers
land near kernel zeros (per-cell max 15211) in low-T cells -- the
T-weighted ratio is the convergence measure.

Grade: the weight factor is interval-certified; the transform-side
majorant and the object difference radii stay inherited from the
2297/2301/2302 chain at its declared standard-arithmetic/BLAS model.
Lessons locked: the true-parameter control reference must multiply by
phi^j = (2 pi log n)^j (a dropped (2 pi)^2 produced a phantom 9.6e4 gap
against budget 2.9e-5 while est - ref_conv on the same float64 parameters
was 5.6e-9); the derivative trig selector is (1,0,1,0) with signs
(1,-1,-1,1); float interval endpoints built from center +- radius need one
outward nextafter per side; 492475 is the sieve limit, not a book element
(largest entry: the prime 492467). Module selftest 9/9 PASS, artifact
selftest 13 tests OK. No hgap certificate, no producer GO, no RH claim.

### Record 2309: the transform side is certified; TRANSFORM-SIDE-CERTIFIED, hgap closed

2308 left exactly one model-grade factor in the window half: the
transform-side perturbation majorant T_cell inherited from 2298/2302
(complex128 BLAS gemm leg, model execution bounds, float64 cell
assembly). Record 2309 re-derives the whole cell majorant on the
exclusive-extended path: order-0 leg bitwise identical to the stored
evaluator (np.array_equal control on every rung), orders >= 1 via
explicitly counted clongdouble elementwise contractions; every stored
float64 jet becomes an interval through the exact rational cast plus a
mechanical budget M_ch,k R_k (L1 coefficient ladder over all 30 families
x 768 panels grouped before bounding, compiled-operation counts 546..927,
extended unit 2^-64); a degree-6 iv Taylor cell assembly with exact
Fraction delta powers; iv error_terms; directed charge sum with the 2308
certified weight factor on the same dyadic cells.

Certified ladder: denom 64: 863819.2915438175 (0.0864x budget), denom
128: 571815.9145338645 (0.0572x), denom 256: 477248.9858117574
(0.0477x). Cross-record: the certified T moves the charge only
-2.6e-9 / -1.4e-9 / -8.6e-10 relative below the 2308 charge (budgets
are pointwise below the model errors on all 14 channel/order slots, so
the certified majorant is strictly tighter; the 2302/2308 predictions
confirm to 9 decimal places). The dps-100 reference control measures
true execution residuals >= 1000x below the budgets (worst allowance
ratio 9.617e-4, base order 0 at xi = -3.605). Subsample sandwich:
certified >= zero-padding stored-jet witness (min margin 1+3.2e-12) and
<= model-grade T (max margin 1-5.5e-12); order-0 bitwise true on every
rung; cross-path ratio <= 2.1e-4. Closure with the 2307 tail (order 36,
1.96e-27): sum 477248.9858117574 <= 1e7 at margin 20.953x; the cheapest
tail rung (order 16) also closes at 20.66x.

Grade: hgap is closed at NUMERIC grade end to end (2275 split / 2308
weight / 2309 transform / 2307 tail all interval-certified); the platform
contract and counted-operation assumptions, the inherited structural
lemmas (interpolation model, carrierwise grouping, mass bounds,
error_terms), and the 2299/2301 radii ledger remain declared. Lessons
locked: ivmpf.a/.b are degenerate intervals whose sum can widen -- use
.mid for float readouts; the soundness direction of a tightened majorant
is measured against the zero-padding witness, not the model T;
iv-scale units must be built as mp.iv.mpf(2)**-k, never from a plain
mpf; mp.iv.mpf([lo, hi]) is the list-form constructor; the extended-jets
polynomial tensor is (chunk, length, 2). Module selftest 5/5 PASS,
artifact selftest 17/17 OK. No Lean hgap discharge, no producer GO, no
RH claim.

### Record 2310: the certified gap closure is wired into Lean; GAP-CLOSURE-WIRED

2309 left hgap closed at numeric grade only: the producer's gap
hypothesis stayed a single opaque `gap <= gapCharge2255` input. Record
2310 moves the closure into Lean. `C1RouteAItem5Arithmetic` pins the two
certified uppers as exact decimal constants -- `windowCharge2309 :=
477248.98581176` (the 45-digit directed-ceiling render of the 2309
transform-side interval upper, rounded up) and `tailCharge2307 :=
2e-27` (the 2307 best rung order 36, rounded up) -- proves the join
`windowCharge2309 + tailCharge2307 <= gapCharge2255` by `norm_num` on
these exact rationals, and packages the consumer as
`hgap_of_certified_split`: the registered 2275/2286/2304 decomposition
`gap <= windowCharge + tailCharge` plus the two pinned enclosures
`windowCharge <= windowCharge2309` and `tailCharge <= tailCharge2307`
give `gap <= gapCharge2255`. `C1RouteAProducerWired` gains
`a005_item5_producer_wired_certified_multiplicity_gap_split`, the
producer with multiplicity discharged (2274) and the gap hypothesis
now consumed through the split; the original conditional theorems stay
for existing callers.

Pin soundness is machine-checked in exact rational arithmetic by
`scripts/routea_gap_closure_lean_pin_2310.py` (verdict
PINNED-UPPERS-VERIFIED, all seven transcription guards, controls
including a negative shifted-pin rejection): the window pin sits
2.575e-9 above the directed-ceiling render and the render sits 5.82e-11
above the stored float endpoint, so `pin >= render >= exact <= true` is
chained without slack in the wrong direction; the tail pin sits 4.136e-29
above the float64 render (17 orders above its half-ulp bound). Join
margin 9522751.01418824, ratio 20.953423259749517, matching the 2309
closure ratio to 1.2e-13.

Build acceptance: targeted log `build_2310_step1.log`
(`Build completed successfully (3572 jobs)`, 0 errors, 0 sorryAx, 0
warnings from the four touched files); root aggregate log
`build_2310_root.log` (`Build completed successfully (4244 jobs)`, 0
errors, 0 sorryAx, same axiom profile). All three new declarations
print `[propext, Classical.choice, Quot.sound]`.

Grade: the join arithmetic and the hypothesis restructuring are
machine-checked; the 2275/2286/2304 split and the two numeric
enclosures remain named obligations (artifact-grade certificates, not
Lean-formalized). Registrations updated: the 2305/2307/2308 localized
[-2, 2] instrument is retired -- the regenerated evaluator (2301) and
grouped S-moment ladders (2308) removed the precision wall it answered,
and the global dyadic mesh is certified end to end over [-40, 40] with
a 21x margin. Producer residual set: `hstrip`, `hmargin`,
`hcharge-rest`, and the gap pair `hsplit` + window/tail enclosures.
Lessons locked: Lean upper-bound pins must be >= the directed-ceiling
render with the comparison done in exact rationals (round-up is the
sound direction); float64-render references need pin slack above the
render's half-ulp bound (2.2e-43 at this magnitude); when restructuring
hypotheses, keep the old theorem and add a new variant so existing
callers compile unchanged. No Lean formalization of the certificates,
no producer GO, no gate sign change, no RH claim.

### Record 2311: the certified strip envelope is pinned and consumed; STRIP-ENVELOPE-WIRED

2303 certified the centered-strip envelope on the corrected width-a^2
owner at artifact grade (continuum sup 2823660.8460007603 = grid maximum
2644542.851480454 times the log-derivative transfer factor
1.0677311749439153, margin 3.3666x under the frozen bUpper2243) and
registered two missing pieces: the certificate interface and the owner
bridge. Record 2311 lands the interface. `C1RouteAItem5Arithmetic` pins
the two certified factors as exact decimals -- `stripGridMax2303 :=
2644542.8515` and `stripTransfer2303 := 1.0677312`, each rounded up from
its committed render with slack above 4e4 / 1e8 ulp of that render -- and
proves their product below `bUpper2243` by `norm_num` (pinned product
2823660.912283517, margin 6682614.19030081, ratio 3.366648970218073 vs
the certified 3.36664904924696, matching to 8e-8 relative).
`C1RouteAProducerWired` gains
`frozenStripHypothesis_of_certified_envelope`: any pair whose
centered-strip min-product is bounded on [-1/2, 1/2] by the pinned
product satisfies the producer's `FrozenStripHypothesis`, through the
machine-checked join -- and the consumer
`a005_item5_producer_wired_certified_multiplicity_gap_split_envelope`,
which consumes that envelope plus the 2310 certified gap split and the
2274 multiplicity discharge; the original conditional theorems remain
for existing callers.

Pin soundness and tightness are machine-checked in exact rational
arithmetic by `scripts/routea_strip_envelope_lean_pin_2311.py` (verdict
PINNED-ENVELOPE-VERIFIED; transcription guards on both def literals, the
join theorem and its norm_num list, the conversion and consumer names and
call lines; controls: synthetic parse, join direction, negative
shifted-pin rejection). Grid-max pin slack 1.9546e-5 (4.2e4 ulp);
transfer pin slack 2.5056e-8 (1.1e8 ulp); product pin slack 6.6283e-2
(1.4e8 ulp); the artifact's own last multiply is internally consistent
(rendered product vs sup_certified, 1.08e-15 relative).

Build acceptance: targeted log `build_2311_step1.log` (`Build completed
successfully (3572 jobs)`, 0 errors, 0 sorryAx, 0 warnings from the four
touched files); root aggregate log `build_2311_root.log` (`Build
completed successfully (4244 jobs)`, 0 errors, 0 sorryAx, same axiom
profile). All three new declarations print `[propext, Classical.choice,
Quot.sound]`.

Grade: the envelope arithmetic (factor pins + join) and the hypothesis
conversion are machine-checked; the 2303 reduction itself and the owner
bridge remain named obligations, so the strip lane now reads: `henvelope`
(artifact-grade, on the captured owner) + owner bridge -> `hstrip`.
Lessons locked (AGENTS §2ac): product-form pins pin the factors
separately with per-factor direction checks (a product pin alone can mask
a below-render factor); the render-chain slack floor is the render's ulp
times the number of chained roundings, with the measured slack/ulp ratio
registered (4.2e4 / 1.1e8 / 1.4e8 here) and asserted >= 100; assert the
artifact's internal factor-product consistency to a registered tolerance
(1e-12); hypothesis-shape conversions that mention a downstream-defined
type live in the downstream module, pins and joins in the owning
arithmetic module. No Lean formalization of the 2303 reduction, no owner
bridge, no producer GO, no gate sign change, no RH claim.

### Record 2312: the transfer law is machine-checked; STRIP-TRANSFER-FORMALIZED

2303's envelope splits into a grid maximum times a continuum-transfer
factor, and the transfer half rested on the registered log-derivative law
`|d/dsigma log N| <= 2 rmax`. Record 2312 lands that transfer in Lean in
exponential form -- the form the envelope consumes. Core
`expWeightedIntegral_le_transfer_of_neighbor`: for continuous `g >= 0`
supported in `[-R, R]`, exponents within `h` obey
`∫ e^(sigma x) g <= e^(R h) ∫ e^(sigma_0 x) g`; on the support
`e^(sigma x) <= e^(sigma_0 x + R h)` is integrated against `g >= 0`, so
no differentiation under the integral appears (the exponential form is
per-point stronger than the infinitesimal law and is exactly the 2311
consumer's hypothesis shape). Two strip-weight corollaries
(`stripNorm`, `stripSecondNorm` with the `support_deriv_subset` /
`tsupport_deriv_subset` chain), the min-product transfer
`N sigma <= e^(2 R h) N sigma_0` from the four factor transfers, and the
consumer `frozenStripHypothesis_of_certified_grid`: grid-existence
(every centered `sigma` within `h` of a certified node whose min-product
is at most `stripGridMax2303`) + support radius `R` + the record 2312
exponent pin yield the 2311 certified envelope, hence
`FrozenStripHypothesis`; the corner
`frozenStripHypothesis_of_certified_grid_rmax` instantiates the pins.

New pins in `C1RouteAItem5Arithmetic`: `stripRadius2303 := 6.5536001`
(a sound upper of the committed `owner.rmax` render
`6.553600000000003`; a pin at the exact decimal 6.5536 would strictly
exclude the artifact's own radius, so the pin sits 1e-7 above the render
-- 1.13e8 ulp, an order of magnitude inside the ~2.25e-6 radius-slack
failure frontier of the Taylor margin), `stripHalfStep2303 := 0.005`
(the exact `1/200` grid half-step), and
`real_exp_transfer_le_stripTransfer2303 :
Real.exp (2 * 6.5536001 * 0.005) <= 1.0677312`, proved by
`Real.exp_bound'` at order 6 with the exact-rational evaluation by
`norm_num`.

Pin soundness and tightness are machine-checked in exact rational
arithmetic by `scripts/routea_strip_transfer_lean_pin_2312.py` (verdict
PINNED-TRANSFER-VERIFIED; 15 transcription guards on the def literals,
the theorem statement, the exp_bound' order and norm_num list, the six
new declarations and the support chain; controls: synthetic parse,
negative shifted-pin rejection, radius +5e-6 overshoot rejection, render
dust acceptance). Numbers: order-6 Taylor bound
`1.0677311760289467` below the pin `1.0677312` at margin 2.3971053e-8
with overshoot over `e^x` of 1.7301e-11; radius pin slack 1e-7
(1.13e8 ulp); half-step exact; `e^(2 * rmax_render * 0.005)` at dps 60
matches the committed `grid.transfer` render to 8.3e-16 relative, and
the pinned transfer dominates that render.

Build acceptance: targeted log `build_2312_step1.log` (`Build completed
successfully (3573 jobs)`, 0 errors, 0 sorryAx, 0 warnings from the four
touched files), post-cleanup confirmation `build_2312_step2.log` (the
ring-to-ring_nf rewrite and the missing final newline fixed; the only
rebuilds are the transfer module and its probe, the rest of the counted
jobs are cached replays), root aggregate log `build_2312_root.log`
(`Build completed successfully (4245 jobs)` -- the 2311 root count 4244
plus the new module -- 0 errors, 0 sorryAx, 0 warnings from the touched
files, replayed probe output carrying the axiom trio).  All seven new
declarations print `[propext, Classical.choice, Quot.sound]`.

Grade: the transfer inequality and the transfer-exponent arithmetic are
machine-checked; the strip lane now reads: grid sampling (Lean-able
next) + node values over the captured owner (artifact) + support radius
(owner bridge) -> `henvelope` -> `FrozenStripHypothesis` -> producer.
Lessons locked (AGENTS §2ad): transfer laws land in exponential form
(integrate the pointwise bound; skip differentiation under the integral
unless the derivative statement itself is needed); when a render's
decimal value is not representable (6.553600000000003 vs 6.5536), pin at
the next decimal with slack >= 100 ulp AND <= a tightness bar derived
from the downstream numeric margin (here 1e-6, with the ~2.25e-6 failure
frontier measured by an overshoot control); after `congr 1` peels a
function application, the argument goal compares two `Real.exp` atoms
that `ring` sees as distinct -- use `ring_nf`, and give every new file a
final newline (whitespace linter). No Lean formalization of the 2303
reduction, no grid-sampling proof, no owner bridge, no producer GO, no
gate sign change, no RH claim.

### Record 2313: the grid-sampling arithmetic is machine-checked; GRID-SAMPLING-FORMALIZED

The record 2312 "Lean-able next" item landed.  New module
`ConnesWeilRH/Dev/C1RouteAGridSampling.lean` proves `gridSample2303`:
every `sigma` in the centered window `[-1/2, 1/2]` lies within the
pinned half-step `stripHalfStep2303` of a grid node `j / 100` with
`j : Z`, `-50 <= j <= 50` -- the record 2303 sigma grid (101 nodes,
spacing `1/100`, covering radius `1/200`).  The proof is the `Int.floor`
round-to-nearest argument `j = floor (sigma * 100 + 1/2)`: index bounds
by `Int.le_floor` / `Int.floor_le_iff`, distance bound by the floor
sandwich `Int.floor_le` / `Int.lt_floor_add_one` giving
`|sigma*100 - j| <= 1/2`, then `abs_div` and `norm_num` against the pin
`stripHalfStep2303 = 1/200`.  No enumeration of the 101 nodes: the Lean
statement is the continuum one.  The new consumer
`frozenStripHypothesis_of_certified_nodes` takes node values only at
the exact 101 nodes of the committed `grid_rows`, which together with
the support-radius bound yields `FrozenStripHypothesis` through the
2312 corner consumer.  The strip lane now reads: 101 node values
(owner) + support radius (owner) -> `FrozenStripHypothesis` ->
producer.

Pin check `scripts/routea_grid_sampling_lean_pin_2313.py` (verdict
PINNED-GRID-SAMPLING-VERIFIED, failures empty): the Lean statement
geometry parses back exactly (50/50/100) and matches the committed
artifact (101 contiguous `grid_rows` `-50..50`; all `sigma` renders
round-trip to the design decimal `j/100` with max deviation 0.0); the
half-step pin equals the exact design value `1/(2*(101-1)) = 1/200`
and the committed `grid.half_step` render; the covering radius is
certified exactly in `Fraction` arithmetic (distance-to-nearest-node
sup over the window, attained on endpoints/nodes/midpoints, equals
`1/200` = the Lean bound target); and cross-record hash continuity is
asserted -- the live md5s of the 2312 files (`b3fb88c3...` arithmetic,
`9bcd576a...` transfer) equal the hashes recorded in the 2312 pin
artifact, so the 2312 module is provably byte-frozen.  Controls:
synthetic 60/60/120 parse, shift +6e-3 rejection, short-grid (100
nodes) rejection, tight-bound (1/1000) rejection.  One control premise
was falsified by measurement first: a uniform +1e-3 node shift does NOT
break the covering radius at midpoints (only the window endpoints move,
and 1e-3 < 1/200), so the rejection control uses a shift above the
radius -- a negative control must falsify the bound, not merely perturb
the object.

Build acceptance: `build_2313_step1.log` (`Build completed successfully
(3573 jobs)`, 0 errors, 0 sorryAx, 0 warnings from the two new files);
root `build_2313_root.log` (`Build completed successfully (4245 jobs)`,
0 errors, replayed probe output carrying `[propext, Classical.choice,
Quot.sound]` for both declarations; both root runs report 4245, so no
per-module census delta is claimed).  Grade: the covering arithmetic is
a Lean theorem with no hypothesis; the residual strip-lane inputs are
exactly the 101 node values and the support radius, both owner-bridge
obligations.  Lessons locked (AGENTS §2ae): control-premise validation
(a control must fail the bound when the object is broken -- verify the
rejection case exceeds the threshold before trusting it); regex/parse
guards must be run against the real source once before the artifact is
trusted (the first `(100)`-vs-`100` pattern slip was caught only by the
first run); cross-record hash continuity makes "old files untouched"
mechanically checkable when pin artifacts record md5s.  No owner
bridge, no producer GO, no gate sign change, no RH claim.

### Record 2314: the owner support radius is a Lean theorem; OWNER-SUPPORT-FORMALIZED

The second strip-lane input named by record 2311 (support radius) now has
a Lean proof for the actual corrected width-a^2 owner family sum.  New
module `ConnesWeilRH/Dev/C1RouteAOwnerSupport.lean` (12 declarations,
namespace `ConnesWeilRH.Dev`) proves, with no hypothesis on the
coefficient and modulation vectors:

  - the bump `widthBump r x` vanishes off `|x| < r` (real and complex
    forms), a single family term is supported in `[-r, r]` (coefficient
    and modulation free), the finite family sum is supported in
    `[-R, R]` once every radius is at most `R`, and the same for
    `tsupport` via `isClosed_Icc.closure_subset_iff`;
  - the width block is completely classified in Lean: `storedWidth
    index <= storedWidth 4` for all 30 indices (family 4 is the unique
    largest width `a_4 = 1441151880758559 / 562949953421312`), hence
    `storedWidth index ^ 2 <= a_4^2` (`pow_le_pow_left₀`);
  - `a_4^2 <= stripRadius2303` in exact rational arithmetic
    (`change` to the explicit literals plus `norm_num`), and the two
    corrected-owner instances: `tsupport (correctedPhysical c m) subset
    [-a_4^2, a_4^2] subset [-stripRadius2303, stripRadius2303]`.

Pin check `scripts/routea_owner_support_lean_pin_2314.py` (verdict
PINNED-OWNER-SUPPORT-VERIFIED, failures empty): the 30 width literals
parse back bit-exact against the 2275 capture
(`Fraction.from_float (float.fromhex ...)` equals the Lean literals);
family 4 is the unique strict max; the exact radius `a_4^2 =
2076918743413931858457251756481 / 316912650057057350374175801344`
equals the 2276 artifact's `corrected_max_radius_exact`, and its float64
render is bitwise the committed `owner.rmax` `6.553600000000003` from
the 2303 envelope artifact -- the certified radius is the owner's own
radius at render level.  The pin `6.5536001` dominates with exact slack
`9.999999745341483e-08` (1.1259e8 ulps of 2^-50), and a decimal pin at
`6.5536` would strictly exclude the owner (`a_4^2 > 6.5536` exactly),
validating the 2312 pin choice.  Cross-record hash continuity: the 2312
arithmetic/transfer md5s, the 2313 grid md5, and the audit module's
sha256 against the 2276 price artifact input hashes all hold.  Controls:
synthetic 3-entry parse; tie rejection (family 6 raised to `a_4` kills
the unique max); widened rejection (`a_4 + 1e-7` exceeds the pin and
changes the render); low-pin rejection (`a_4^2 - 1e-8`); decimal
strictness.  The parse-guard-first-run rule from 2313 fired as designed:
run 1 raised `ValueError` on the parenthesized literals instead of
silently mis-parsing.

Build acceptance: `build_2314_step1.log` (`Build completed successfully
(3658 jobs)`, 0 errors, 0 sorryAx, 0 warnings from the two new files);
root `build_2314_root.log` (`Build completed successfully (4329 jobs)`,
0 errors, all 12 declarations replayed with `[propext,
Classical.choice, Quot.sound]`; the root count moved 4245 -> 4329 with
the added import closure, no census delta claimed).  Grade: the
support-radius half of the owner bridge is a Lean theorem; residual
strip-lane inputs are the `CompactLogTest` packaging of the owner (with
the captured coefficient/modulation vectors) and the 101 node values at
`stripGridMax2303`.  No producer GO, no gate sign change, no RH claim.

### Record 2315: the corrected owner is packaged as a CompactLogTest; OWNER-TEST-PACKAGED

The structural half of the owner bridge lands.  New module
`ConnesWeilRH/Dev/C1RouteAOwnerTest.lean` (12 declarations, namespace
`ConnesWeilRH.Dev`) closes the gap between record 2314's raw-function
support theorems and the record 2312/2313 consumer type
`CompactLogTest = { test : SchwartzMap ℝ ℂ, compactSupport :
HasCompactSupport test }`, for arbitrary coefficient and modulation
vectors.  The bridge is the flat-junction identity

    widthBump radius x = expNegInvGlue ((1 - (x / radius)^2) / 30)
      (0 < radius),

where `expNegInvGlue t = exp (-t⁻¹)` on `t > 0` and `0` on `t ≤ 0`:
`|x| < radius` matches `u / 30 > 0` with `u = 1 - (x / radius)^2`
(`abs_div` + `div_lt_one` + `sq_abs` against `one_le_div` +
`one_le_pow₀`), the arguments agree on `-30 / u = -((u / 30)⁻¹)`
(`inv_div`, `neg_div`), and both sides vanish literally at `|x| =
radius`.  Smoothness is inherited from Mathlib's `expNegInvGlue.contDiff`
(no boundary-flatness argument of our own), composed with the smooth
rational map (`widthBump_contDiff`); family terms are constant × coerced
bump × unimodular phase (`Complex.ofRealCLM`, `Complex.contDiff_exp`),
the sum is `ContDiff.sum`, and compact support is
`IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)` over
the 2314 pin interval.  The packaging
`correctedPhysicalCompactLogTest coefficients modulations :
CompactLogTest` comes with `_toFun` (the underlying function is the
owner, via `HasCompactSupport.toSchwartzMap_toFun`),
`_tsupport_subset` (the support bound in exactly the record 2313
consumer hypothesis shape), and `_compactSupport`.

Pin check `scripts/routea_owner_test_lean_pin_2315.py` (verdict
PINNED-OWNER-TEST-VERIFIED, failures empty): the record 2314 module is
byte-frozen (live md5 `6fc7303d…` equals the 2314 artifact provenance);
the `CompactLogTest` shape is still `test : TestFunction` +
`compactSupport : HasCompactSupport test` (live md5 `352c40fb…`
recorded as the anchor); transcription guards cover all 12 declarations
plus the base-function guard (`expNegInvGlue` present,
`Real.smoothTransition` absent — the logistic transition is a different
function) and the free-parameter shape of the packaging; the sampled
identity witness at dps 70 over the exact owner radius a_4^2 (9
interior + 8 boundary/outside points, exact counts pinned) has max
branch difference `2.778e-83` (bar 1e-50), exact zeros at `|x| >=
radius`, strict positivity inside, and dip `e⁻³⁰ =
9.3576229688401746049e-14` at zero.  Wrong pairings are rejected: an
argument offset `-1/50` changes samples by up to `9.357623e-14` and a
halved radius by `4.1473394e-14` (bar 1e-20).

Build acceptance: `build_2315_step1.log` (`Build completed successfully
(3659 jobs)`, 0 errors, 0 sorryAx, 0 warnings from the two new files);
root `build_2315_root.log` (`Build completed successfully (4330 jobs)`,
0 errors, all 12 declarations replayed with `[propext, Classical.choice,
Quot.sound]`; plan counts quoted verbatim, no census delta claimed).
Grade: the strip lane's inputs are now fully owner-shaped — the record
2313 consumer takes `b c : CompactLogTest` plus node values, and the
owner supplies the test and support bound for free vectors.  Residual:
the 101 node values at `stripGridMax2303` (the value half, where the
captured coefficient and modulation vectors enter bitwise); then signed
margin, non-tail charge.  No producer GO, no gate sign change, no RH
claim.

### Record 2316: the 101 node values of the captured owner min-product; NODE-VALUES-CERTIFIED

The value half of the owner bridge becomes a first-class table.  Record
2313's consumer `frozenStripHypothesis_of_certified_nodes` asks, at each
of the 101 grid nodes `j/100`, that the centered min-product
`min(D2_b M_c, D2_c M_b)` of the owner pair be at most
`stripGridMax2303`; record 2303 had computed certified per-node uppers
of exactly this quantity (the `B_point` field of its 101 `grid_rows`).
This record re-derives that table end to end and pins it.  New check
`scripts/routea_node_values_2316.py` (verdict NODE-VALUES-CERTIFIED,
failures empty) -> `results/2316_node_values.json`:

1. continuity: the live 2275 capture parses and is bitwise equal to the
   2267 replay operands (families, base and corr vectors — the captured
   coefficient and modulation vectors enter bitwise); the 101
   `2303_sigma_j.json` files are present, indexed (`sigma_index`,
   `nodes = 240001`) and bitwise equal to the corresponding
   `grid_rows.point` values; the 2303 envelope artifact bytes are frozen
   by md5 `b7814e73…` (first record to do so);
2. assembly replay: for all 101 rows the check re-derives, with the
   record 2303 expressions verbatim (2238 `ladder` + panel law `(dx²/12)
   (2 rmax) e^{|σ| rmax} (m_{k+2} + 2|σ| m_{k+1} + σ² m_k)`, 2234
   `majorant_phi_le` inflation, upward-rounding chains), the four panel,
   four inflation and four certified-norm values, the two channel
   products, their min, the binding channel and `B_point`, and requires
   bitwise equality with the committed fields; rmax, dx, the 2238
   ladder (both copies), the transfer `1.0677311749439153`, the
   continuum sup `2823660.8460007603`, the covered flag, the margin
   `3.36664904924696x`, the raw-check floats and the `anchor_raw`
   summary replay bitwise the same way; mismatches = {};
3. exact rational directions: every `B_point` is an upper of the
   certified min-product and at most the pin `stripGridMax2303 =
   2644542.8515` (parsed from the Lean source, literal guard), and the
   certified min-product dominates the live numpy raw screen (the 2277
   reproduction, recomputed here bitwise from the capture) at all 101
   nodes;
4. the binding node is `j = -50`, `sigma = -0.5`, channel "a", with
   `B_point = 2644542.851480454` and pin margin `1.9545793533325194e-5`
   = 41974.272 ulp of the render — the same 4.2e4-ulp figure as the
   2311 pin artifact, now per node; margin range over the 101 nodes
   41974.272 ... 1.6956e16 ulp; worst raw ratio (min over nodes)
   2.4661322656498452 at j = 0; raw ratio rel_max 7.2765792264717994
   (replayed); cross-record pins 2311 and 2313 both consistent, and the
   arithmetic pins file is byte-frozen since 2312 (`b3fb88c3…`).

Controls: synthetic pin parse; shifted pin rejected; a one-ulp point
mutation is detected by the bitwise replay; an inflated raw screen
(x2.5 at j = 0) is rejected — the first-run control premise ("x2") was
falsified by measurement (the certification price at j = 0 is 2.466x)
and replaced; a capture mutation fails the operand anchor.  Grade:
artifact; the sigma quadrature itself is not re-run (its committed
files are re-linked and direction-checked), the 2303 analytic majorants
stand as recorded, no Lean certificate.  Residual strip-lane work: the
Lean instantiation of `frozenStripHypothesis_of_certified_nodes` with
the 2315 packaged owner pair, leaving this table's 101-node bound as
the single strip hypothesis; then the signed margin and the non-tail
charge.  No producer GO, no gate sign change, no RH claim.

### Record 2317: the strip consumer instantiated with the packaged owner pair; OWNER-NODES-WIRED

The Lean side of the owner bridge closes.  New module
`ConnesWeilRH/Dev/C1RouteAOwnerNodes.lean` (1 declaration, namespace
`ConnesWeilRH.Dev`) instantiates the record 2313 consumer
`frozenStripHypothesis_of_certified_nodes` with the record 2315 packaged
owner pair:

    theorem frozenStripHypothesis_of_owner_nodes
      (baseCoefficients corrCoefficients : Fin 30 → ℂ)
      (modulations : Fin 30 → ℝ)
      (hnode : ∀ j : ℤ, −50 ≤ j → j ≤ 50 →
        min (stripSecondNorm (j/100) (correctedPhysical base mods) *
             stripNorm (j/100) (correctedPhysical corr mods))
            (mirror term) ≤ stripGridMax2303) :
      FrozenStripHypothesis (packaged base) (packaged corr)

The proof is the consumer plus the record 2315 facts: the two support
goals close by `correctedPhysicalCompactLogTest_tsupport_subset`, and
the node goal rewrites the packaged tests back to the raw owner through
the two `correctedPhysicalCompactLogTest_toFun` lemmas (explicit
arguments — two instantiations share the goal) and closes by the
hypothesis.  One shared modulation vector, matching the record 2275
capture shape; the vectors stay free (the numeric instantiation is
artifact-grade).  The residual strip hypothesis is now literally the
record 2316 node table's 101-node bound.

Pin check `scripts/routea_owner_nodes_lean_pin_2317.py` (verdict
PINNED-OWNER-NODES-VERIFIED, failures empty): the record 2315 module
(b88ce3ef…) and the record 2313 module (3581e512…) are byte-frozen
against their pin artifacts; the record 2316 node artifact is frozen
from here on (07d3f9e5…), verdict intact, table 101 contiguous rows
with sigma = j/100 and max 2644542.851480454 at most the pin; the
arithmetic pins file still b3fb88c3… (chain from 2312); statement
guards cover the params, hnode binder, min shape, bound constant,
conclusion, the consumer call, both tsupport calls, both toFun
rewrites and the close; controls: synthetic statement probe, a mutated
`≤ bUpper2243` constant fails the bound guard, a missing final newline
fails the newline guard.

Build acceptance: `build_2317_step1.log` (`Build completed successfully
(3708 jobs)`, 0 errors, 0 sorryAx, 0 warnings from the new files after
the trailing-newline fix); root `build_2317_root.log` (`Build completed
successfully (4148 jobs)`, 0 errors, probe replay with `[propext,
Classical.choice, Quot.sound]`; plan counts verbatim, no census delta
claimed).  Two first-run incidents, both loud: `correctedPhysical`
unknown until the record 2314 auxiliary namespace was opened (the 2315
module carries the same `open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit`),
and the `linter.style.whitespace` `'' starts on column N` warning is a
missing final newline.  Grade: the strip lane is fully wired on the
Lean side; remaining strip-lane work is only the numeric `hnode`
instantiation for the captured vectors (the frozen 2316 table).  Then
the signed margin and the non-tail charge feed the producer alongside
the record 2310 gap closure; the selected-owner signed inequality
remains the summit.  No producer GO, no gate sign change, no RH claim.

### Record 2318: the certified L1 enclosure enters the producer margin lane; L1-ENCLOSURE-WIRED

Record 2249 certified the finite-window functional at the captured owner
inside a two-sided first-order shadow enclosure (q in [q_lo, q_hi],
results/2249_l1_enclosure.json).  Record 2318 wires it into the producer
margin lane as a Lean interface.  New module
ConnesWeilRH/Dev/C1RouteAL1Enclosure.lean (8 declarations, axiom trio),
importing the record 2311 producer module and the record 2317 owner-nodes
module without editing either:

* outward-rounded constants: l1MarginEnclosure2249 = 1675396046388.2736
  (certified |Q| lower bound) and l1UpperEnclosure2249 =
  -1675396046388.2736 (signed functional upper), exact negatives of each
  other; the consumer hmargin_of_certified_l1_enclosure turns
  q <= l1UpperEnclosure2249 into the producer shape
  l1MarginEnclosure2249 <= -q;
* the record 2252 transfer-free ledger re-run at the certified constant
  (HST + knownError2109 + gapCharge < l1MarginEnclosure2249 - eps0) and the
  count-free terminal variant at the same constant;
* the composed producer a005_item5_producer_wired_owner_nodes_margin: the
  record 2317 strip interface + this enclosure + the record 2109 charge +
  the record 2310 gap split into the item-5 strict signed inequality
  tsum + chargeRest + gap + eps0FullTail2249 < -q, residuals exactly hnode
  (the 2316 table), hq, hcharge, and the gap split trio.

Sub-ulp finding, measured in exact Fractions: the exact shadow upper bound
q + E sits 0.0395 ulp above the stored render q_hi and 0.1147 ulp above the
shortest-decimal transcription -1675396046388.2737, so a Lean pin at that
decimal would sit strictly inside the certified enclosure (the record 2314
hazard on the margin side; the four stored binary64 relations all hold
bitwise).  The shipped constants round outward by 1e-4 (0.41 ulp), covering
the exact bound with 0.295 ulp slack; margin2249 (the 2252 transcription)
is not routed through the enclosure and asserts no artifact direction.

Replay evidence: the full record 2249 instrument re-run (~190 s, the
original run recorded 190.2 s) reproduces every certified field of the
artifact bitwise; exactly three of ~40 fields differ, all plain-float
cross-check diagnostics routed through BLAS dgemv and np.trapezoid
(q_plain rel 1.5737871286495764e-14; rel_lb_diff_mid abs
6.820900295631004e-17; rel_lc_diff_mid abs 1.1442748970580396e-09, a
documented near-cancellation midpoint channel).  A representative dgemv is
bitwise-stable across processes and OPENBLAS_NUM_THREADS values in the
current environment, so the difference is library drift since the
2026-09-29 capture, not live nondeterminism; the artifact bytes stay frozen
(4fb81ff7...).  Pin check scripts/routea_l1_enclosure_pin_2318.py (verdict
PINNED-L1-ENCLOSURE-VERIFIED, failures empty): the four stored relations
bitwise; the exact-Fraction readings; owner cross-tie (base d461872e... /
corr c37e16a9... == record 2316 claimed, 2275 capture root d83ee0ff...
frozen); continuity (arithmetic pins b3fb88c3... since 2312, producer
3b15d733... since 2311, owner-nodes 68550f52... since 2317, 2317 artifact
408bfb5a... + verdict); 20 statement guards; the joins and the consumer
replay in Fractions; replay diff vs the documented volatile set; controls
(synthetic parse, naive-decimal rejection in both directions, one-ulp q_hi
mutation, sign-flip literal).

Build acceptance: build_2318_step1.log (Build completed successfully (3709
jobs), 0 errors, 0 sorryAx, warning-free after the trailing-newline fix);
root build_2318_root.log (Build completed successfully (4148 jobs), 0
errors, 0 sorryAx, probe axiom trio for all six theorems; plan counts
verbatim).  Two first-run incidents, both loud: the resource runner execs
in a non-login shell, so lake needs its absolute elan path (exit 127
otherwise), and the whitespace linter again flagged the missing final
newline on both new files.  Grade: the producer's hmargin lane is
discharged by the certified enclosure; residual inputs are hnode (2316
table), hq (this enclosure), hcharge (the 2109 ledger), and the gap split
trio; the remaining unwired lane is hcharge-rest (the non-tail charge).
No producer GO, no gate sign change, no RH claim.

### Record 2319: P-only direct detector readback is obstructed

The producer audit of records 2318/2249 distinguishes the sampled functional
from the actual selected-square sign consumer. The committed four-point
annihilator multiplier vanishes at the marked centered pair; its P-only
Hermitian readback is zero, while the selected square with raw 1/-1 values
reads -1 at that same point. This is a scoped no-go for direct identification,
not a rejection of the local strip or hgap certificates. Record 1914 already
proved orbit annihilation; 2319 adds the producer-facing incompatibility audit.

The growth check gives zero marked gain for the P-only shape at every cutoff.
The exact coefficient-growth control also shows that (4/3)^N cancels the
fixed-owner (3/4)^N tail factor. It is not a measured law for the actual owner,
whose coefficient-to-gain ratio remains uninstantiated. Do not replace that
gain by the sampled negative functional magnitude. The 2249 52-term kernel
and 2308 41136-term convention also need a proved kernel/owner transfer before
their certificates can be composed as facts about one functional.

The binding next obligation is an actual selected-square physical-kernel
readback retaining the nonzero marked pair, then a joint signed margin for
that same object. The map-103 four-point family remains frozen; this record
does not reopen its gate or fixed-lambda branches. No producer GO or RH claim.

Evidence: docs/proofs/2319_routea_producer_readback_no_go.md,
ConnesWeilRH/Dev/C1RouteAProducerReadback.lean and paired Audit,
scripts/routea_producer_readback_2319.py, results/2319_producer_readback.json.

### Record 2320: 2249 and 2308 are not the same kernel owner scope

Scope clarification 2336: neither convention here has been proved to be the
actual assembled detector complete prime book. The composed-source support
cover uses 4R at n=0, not the 2308 2R convention; exact nonzero indices remain
uninstantiated.

The first live scope audit confirms that the 2249 and 2308 owner families
are bitwise identical, but their support-derived prime books are not. Record
2249 uses `2 * max(width)` and stops at prime power 167 (52 terms); record
2308 uses `2 * max(width^2)` and reaches 492475 (41136 terms). Therefore the
2249 signed L1 margin cannot be applied to the actual selected-square physical
kernel by coefficient or family hash alone. The omitted prime-power interval
`167 < n <= 492475` must be explicitly evaluated and enclosed on the actual
selected owner. No producer GO and no RH claim.

Evidence: `scripts/routea_kernel_owner_scope_audit_2320.py`,
`results/2320_kernel_owner_scope_audit.json`, and
`docs/proofs/2320_kernel_owner_scope_mismatch.md`.

### Record 2321: omitted prime-book contribution is cancellation-dominated

Scope correction 2334: records 2321-2333 below are historical P-only auxiliary
diagnostics. Their selected-owner wording and producer-margin interpretations
are withdrawn. The numbers remain as diagnostics, not actual-owner evidence.

On the same 2249 owner and grid, replacing the 52-term book through 167 by
the 41136-term book through 492475 changes the signed functional by only
`+1.554582542873e8`, while the direct absolute-value charge is
`2.225576909988e16` (about `1.3285e4` times the full signed value). The
termwise triangle route is therefore too loose by construction. The next
binding mechanism must preserve prime-power cancellation through grouped
summation or a certified oscillatory evaluator. This is a diagnostic, not a
certificate and does not transfer the 2249 margin.

Evidence: `scripts/routea_omitted_prime_book_diagnostic_2321.py`,
`results/2321_omitted_prime_book_diagnostic.json`, and
`docs/proofs/2321_omitted_prime_book_diagnostic.md`.

The 2321 follow-up grouped the omitted integrand in xi panels before taking
absolute values. Width 2.0 reduces the absolute panel sum to `1.5049e13`, but
that remains about nine times the existing `1.6754e12` margin. Fixed-width
panel grouping is therefore not sufficient; the next mechanism must use the
actual oscillation scale and a certified quadrature remainder.

### Record 2322: Fourier-side decomposition is the viable omitted-book interface

The omitted prime-book contribution was re-expressed by integrating the owner
weight against each prime-power cosine before summing. The sampled sum of
absolute Fourier terms is `6.2162e8`, versus `2.2256e16` for the pointwise
product envelope and `1.5546e8` for the signed total. This is below the
existing `1.6754e12` margin by about 2695x, so the next certified mechanism
should bound the Fourier coefficients of the actual selected owner, not the
pointwise omitted kernel. This is still diagnostic and not a producer
certificate.

### Record 2323: Fourier coefficient refinement is stable but must be charged

The same owner was recomputed at `dx=0.02` and `dx=0.01`. The signed omitted
contribution moved by about `607`, while the sum of absolute Fourier terms moved
by about `23986` (relative `3.9e-5`). Both remain far below the current margin,
but refinement agreement is only a control. The certified route must carry the
coefficient-level quadrature remainder explicitly.

### Record 2324: owner-weight forward error fits inside the margin

The 2249 operation-level forward-error shadows were propagated into every
omitted prime-power Fourier coefficient. The accumulated owner-weight error is
`1.179864458159e9`, versus the `1.675396046388e12` margin; the remaining
binding term is the coefficient quadrature/finite-window remainder. This is a
budget diagnostic, not yet a full certificate.

### Record 2325: quadrature trust horizon and aliasing control

Independent composite Gauss-Legendre evaluation shows that GL order alone is
not an accuracy guarantee. `GL16 x 160` is alias-dominated (`3.7439e13`
absolute-term movement when refined to `GL16 x 320`), while `GL16 x 320` to
`GL16 x 640` moves only `1.2537e5`. The current trust horizon is panel width
`0.25`; the next certified remainder must be built at or below that width and
must include finite-window endpoint terms.

### Record 2326: same-panel order control agrees with spatial refinement

At fixed panel width `0.25` and 320 panels, GL16 to GL32 moves the Fourier
absolute-term sum by `1.2542e5` and the signed total by `-1.7521e4`. This agrees
with the independent GL16 x 320 to GL16 x 640 movement. The trust horizon is
now supported by both order and geometry refinement, but the analytic
quadrature remainder is still required for a certificate.

### Record 2327: cosine-only quadrature remainder has large headroom

The GL16 remainder prefactor at panel width `0.25` gives a cosine-only bound
of `3.2513e4`, or `1.94e-8` of the current margin. This does not include the
product derivatives of the selected-owner weight, endpoint correction, or
full-line tail. The next analytic task is an owner-weight derivative majorant;
the cosine-only reading is not a certificate.

### Record 2328: global product-derivative triangle is a scoped no-go

After correcting an initial double-GL-weight implementation error, the global
product-derivative majorant reads `9.2356e23`, or `5.5125e11` times the current
margin. The failure is structural: absolute basis derivative moments are taken
before the selected-owner coefficients are combined, destroying cancellation in
`L_base` and `L_corr`. The Fourier interface is retained, but the global
triangle majorant is frozen as a no-go; only panel-local or interval-jet
cancellation-preserving mechanisms remain admissible.

### Record 2329: panel-local owner-cancelling jets are numerically viable

The panel-local jet probe combines all 30 basis derivatives with the selected
owner coefficients before taking norms, then includes the complete Leibniz
sum for `W * cos(phi xi)`. The corrected proxy is `7.4722e5`, only
`4.46e-7` of margin, versus `9.2356e23` for the global triangle majorant.
Center jets are not yet interval enclosures; the next obligation is to inflate
them over each panel with a certified radius.

### Record 2330: panel radius samples do not consume the budget

Sampling the cancellation-preserving jet at all 320 panel centers and 640
endpoints raises the product proxy from `7.4722e5` to `1.0045e6`, or
`5.996e-7` of margin. This supports the local-jet route, but sampled endpoints
are not a certified interval supremum; local radius inflation remains to be
proved.

### Record 2331: first-order panel-radius inflation remains cheap

Extending the local jet to order 33 and applying a sampled Lipschitz inflation
raises the product proxy to `2.5214e6`, or `1.505e-6` of margin. This supports
the local interval strategy, but the sampled maxima must still be replaced by a
proved local radius before the remainder can be certified.

### Record 2332: local Taylor radius inflation remains inside budget

A panel-local Taylor enclosure probe uses cancellation-preserving center jets
through order 34 and an order-34 absolute tail over radius `0.125`. The full
product remainder proxy is `1.1331e7`, or `6.763e-6` of margin. This is closer
to the required proof shape than endpoint sampling, but still uses stored
floating arithmetic and no directed interval implementation.

### Record 2333: forward-shadow tail budget is stable

A usable directed-tail candidate reuses the 2249 forward shadows for the
positive order-34 basis tail and accumulates with `math.fsum` plus
`SUMCHARGE`. Its Taylor-tail proxy remains `1.1331e7` (`6.763e-6` of margin),
matching 2332. The scalar mpmath interval implementation was an engineering
no-go and produced no artifact; it is not evidence. Center-jet intervalization,
coefficient casts, endpoints, and full-line tail remain open.

### Record 2334: Fourier object-scope correction

Records 2321-2333 used the 2249 `P_from_nodes(counterpart_nodes(rho))^2`
construction. That is the P-only auxiliary functional, not the actual
`selectedOwner.convolutionSquare`. Record 2319 independently shows why this
distinction is binding: the P-only marked-pair readback is zero while the
selected square readback is `-1`.

Therefore 2321-2333 are downgraded to auxiliary P-only cancellation and
quadrature diagnostics. Their numbers are removed from the selected-owner
producer margin. The live numerical obligation is now an object-identity
probe for the actual selected owner: source transform, convolution-square
profile, and support-derived prime set. Fourier/local-Taylor pricing may be
restarted only after that probe passes.

### Record 2335: actual selected-owner transform factorization

The new narrow-import leaf factors the actual source transform as
`H(z) = B(z)^(n+1) C(z)` and the selected square as
`conjugate(H(1-conjugate(z))) H(z)`. Only on `Re(z)=1/2` does this become
`|H(z)|^2`; no extra P-only polynomial is inserted. The iterate index counts
`n+1` copies of base. This resolves the transform-expression ambiguity, not
the owner-instantiation, support/prime-book, or Fourier-inversion obligations.
No numerical repricing, producer GO, or RH claim is made.

### Record 2336: marked-source probe and composed support

The stored coefficients retain the intended marked pair in a three-rule
physical quadrature diagnostic (n=0 square real part -0.9999999998664919,
orbit sum -1.9999999997329838; rule movement 1.1384e-10). This is not exact
interpolation, a source-zero witness, or finite-node completeness. No P factor
is inserted and no coefficients are solved anew.

Four Lean support leaves establish source radius (n+1) R_b + R_c and
square radius 2 ((n+1) R_b + R_c), including the packaged captured family at
the outward pin. At n=0 the support-cover expression is 4R, about 26.2144,
not the 2308 2R = 13.1072 convention. This does not prove a specific omitted
term is nonzero or that the larger bound is minimal. Prime-book transfer
requires a support reduction or signed remaining-book treatment. Eight
negative/edge selftests pass. No gate sign, producer GO, or RH claim.

### Record 2337: marked sign certified; captured exact targets excluded

Arb integration of the exact binary64 physical source plus analytic endpoint
charges certifies Re(marked square) < -0.99 and Re(four-point sum) < -1.9
at n=0. Exact-rational postprocessing independently rechecks those signs.
All eight mandatory target values are excluded by the same source enclosures;
in particular the three nominal zero moments are nonzero. The captured
coefficients cannot instantiate an exact healthy finite-node realization.
Sixteen adversarial/mutation tests pass. No full spectral sign or RH claim.

### Record 2338: actual analytic finite-node repair enclosed

All 900 entries of the actual 30-node analytic moment matrix are enclosed.
A rigorous solve gives the unique ideal coefficient pair, with an independent
Neumann defect check eta ~4.5323e-38 < 1/2. The coefficients are not cast to
float or transferred to the live owner. Certified strip transform-change
pins are 1.26e-7 for base and 1.63e-4 for correction. These are uniform
pointwise bounds, not integrable tails or signed-kernel charges. Finite-node
completeness, the source-zero premise, and the complete-owner signed budget
remain open. Six solve/norm tests pass. No producer GO or RH claim.


### Record 2339: additive norm transfer and integrable repair

The 2338 exact analytic repair now has explicit coefficient, phase, radius
rounding and exact-sigma weight charges. Full published 2303 norms are
retained, without reserve subtraction. The unchanged node pin passes at
100/101 nodes; j=-50 has sufficient upper 2644543.166942142 against
2644542.8515. This is a failed sufficient estimate, not an actual lower
bound or family no-go. Prove any directed baseline reserve reassignment
before retrying; do not loosen the pin.

At n=0 the pure coefficient repair has a two-sided unweighted Fourier
square-change integral upper <3.602. The analytic t^-8 tail beyond
|t|=65536 is positive and <1.425e-19. This removes the non-integrability
obstruction of the 2338 uniform bounds, but not the full kernel charge.
The 2336 composed support/complete-prime-book guard still applies.
Twelve adversarial tests pass and full replay is byte-identical. No
owner transfer, detector instantiation, Lean certificate import, signed
margin, producer GO or RH claim. Evidence: proof record 2339 and paired
transfer/validation artifacts.

### Record 2340: recomposed point-panel transfer

The 2339 pin failure came from adding the exact repair on top of the already
inflated 2303 full norms. Record 2340 recomposes from the certified continuous
`point + panel` base, adds the exact-radius and coefficient-function
differences, and does not reuse the old coefficient inflation. The resulting
upper bound passes all 101 nodes; the maximum is j=-50 at
706456.1761485816... versus pin 2644542.8515. This is a transfer probe, not
a completed proof: the directed point sum, Euler-Maclaurin panel remainder,
and zero-count premises still need an explicit proof bridge. No owner transfer,
signed kernel charge, producer GO, or RH claim. Evidence: proof record 2340,
the recomposed transfer artifact, and its four-test selftest.

### Record 2341: single-sided panel replacement and coordinate charge

The repaired 2340 source now adds stored point/panel operands only after
lifting them separately, and its nine-test replay binds the corrected source.
Record 2341 replaces the unproved absolute modulus-curvature reading with
a vector chord upper: integral |V| <= trapezoid + (h^2/12)(2R) sup|V''|.
This needs no zero-count premise. Directed panel top-ups and exact rational
linspace displacement charges retain the frozen node pin at all 101 nodes;
the maximum j=-50 is 706456.2163439568. Eleven new tests and twelve 2339
tests pass, and full replay is byte-identical. The 2303 nodal-upper theorem
and original coordinate identity remain open; MPFR round-to-nearest plus
slack is not automatically a directed chain. No Lean import, signed kernel
charge, live-owner handoff, producer GO or RH claim.

### Record 2342: independent exact-grid ideal-source strip certificate

The direct Arb/Acb chain evaluates the 2338 ideal coefficient rectangles at
120001 exact rational nodes, with exact width-squared radii, complex sums
before modulus and outward weighted trapezoid accumulation. It does not
use the 2303 point sums or reconstructed linspace. The 2341 chord allowance
and convex endpoint domination cover every sigma in [-1/2,1/2]; the raw
min-product upper is 1852190.2152630097, 0.700382 of the unchanged pin.
Fifteen controls pass, including an independent mpmath evaluation of the
actual 30-family midpoint source at five nodes. Full 192-bit replay is
byte-identical; a full 256-bit run stays under the pin with all 40 control
components overlapping. This replaces two legacy numerical premises for
the captured ideal source only. The analytic source/readback identity and
Lean certificate import, healthy detector and complete signed-kernel
budget remain open. No producer GO or RH claim.

### Record 2343: endpoint strip bridge formalized

The new Lean endpoint theorem reduces the full centered strip norm obligation to
four endpoint inequalities for the same owner: base/correction, function/second
 derivative. Convexity of exp proves the reduction directly under compact support;
no zero-count or modulus differentiation is used. The rounded-up 2342 constants
satisfy the existing frozen arithmetic inequality by exact rational checking.
Focused Lake build completes 3707 jobs and the six audited leaves have exactly
[propext, Classical.choice, Quot.sound]. The numeric endpoint facts and the
external-to-Lean function identity are still open, so no producer GO or RH claim.

Record 2344: symbolic owner identity, with external numeric boundary retained

Lean proves externalPhysical2344 = correctedPhysical for arbitrary coefficient
and modulation vectors at exact storedWidth^2 radii. Six audited leaves pass
with exactly [propext, Classical.choice, Quot.sound]; focused build: 3708 jobs.
The exact checker matches all 30 captured widths and four outward constants;
eight mutation/control selftests pass. The Python evaluator semantics, explicit
derivative formula, repaired coefficient realization and numeric endpoint
integrals remain unimported. Norm supplier only; no producer GO or RH claim.
Evidence: docs/proofs/2344_external_owner_identity.md.

Record 2345: interior derivative formula formalized

Lean proves the explicit first- and second-derivative chain for every strictly interior point of the external owner. The focused build has 3709 jobs and ten audit leaves with exactly [propext, Classical.choice, Quot.sound]. This validates the algebraic derivative factor used by the 2342 evaluator in the interior only. The support-boundary/zero-branch formula, whole-program evaluator semantics, endpoint facts and signed kernel budget remain open. No producer GO or RH claim.
Evidence: docs/proofs/2345_external_owner_derivatives.md.

Record 2346 (2026-10-01): closed the boundary and zero-extension derivative
gap. Local zero on each strict exterior gives zero second derivative; smoothness
makes its zero set closed and extends zero to both boundary points. The resulting
piecewise family formula sums across all 30 exact storedWidth-squared families
and applies directly to correctedPhysical for arbitrary coefficient/modulation
vectors. The Python execution semantics, coefficient realization and endpoint
integral inequalities remain separate obligations. No producer GO or RH claim.
Evidence: docs/proofs/2346_external_owner_zero_extension.md.

Record 2347 (2026-10-01): formalized the one-sided chord-panel inequality.
A norming real functional from Mathlib Hahn-Banach projects the value without
increasing norm; adding M*x^2/2 makes the projection convex. This proves the
pointwise chord bound, exact cell integral M*h^3/12, uniform-grid assembly
M*h^2*(n*h)/12, and a finite-node-upper replacement interface. No modulus
second derivative or zero exclusion is used. Focused Linux build: 3711 jobs,
six audit leaves exactly [propext, Classical.choice, Quot.sound], no new-source
warnings; both Lean files match the mirror. Eleven unchanged 2341 regression
tests pass. Actual weighted-owner curvature, repaired coefficient realization,
program semantics and endpoint numerical facts are not instantiated/imported.
No producer GO or RH claim. Evidence: docs/proofs/2347_chord_panel_integral.md
and results/2347_chord_panel_validation.json.

Record 2348 (2026-10-01): derived the real-exponential weighted first/second
derivatives and the curvature implication exp(|sigma|R)*(m2+2|sigma|m1+sigma^2*m0).
Restricted the whole-line strip norm to exact support and applied the 2347
finite-node quadrature theorem. Specialized both stripNorm and stripSecondNorm
to correctedPhysical at exact storedWidth 4 squared radius; smoothness and
support are discharged for arbitrary coefficient/modulation vectors. Orders
0/1/2 feed the first channel; orders 2/3/4 feed the second. Ten audit leaves
have exactly [propext, Classical.choice, Quot.sound], focused build 3712 jobs.
Actual derivative ladder constants, ideal coefficient realization, program
semantics and finite numeric node facts remain explicit open obligations.
No endpoint import, healthy detector, live handoff, producer GO or RH claim.
Evidence: docs/proofs/2348_weighted_chord_panel.md.

Record 2349 (2026-10-01): exact integer recurrence reduces the bump derivative
ceilings to [1,60,3720,236160,15130080], all below the legacy constants.
The coarser third-order 272160 does not refute legacy 245160: substituting the
actual inverse-deficit relation gives 236160. Three Lean envelope leaves
build in 2943 jobs with exactly the permitted axioms; full derivative
recurrence/owner instantiation remains external. Same-run reproduction of
2342's original panels/totals precedes a same-node-sum reprice to
1808469.1730280858 = 0.6838494494 of the frozen pin, 2.3605% below 2342.
Twelve new controls and fifteen unchanged 2342 regressions pass, with cheap
replay byte-identical. No numeric import, healthy detector, full signed budget,
producer GO or RH claim. Next formalize the actual derivative recurrence and
coefficient realization; do not spend further grid refinement on this margin.
Evidence: docs/proofs/2349_derivative_ladder.md.

Record 2350 (2026-10-01): proved actual widthBump derivatives through order
four, both support edges/exterior, and concrete ceilings
[1,60,3720,236160,15130080] in Lean. Phase derivative/norm transport and
Leibniz now supply the actual 30-family correctedPhysical derivative budget
at exact storedWidth-square radii, for arbitrary coefficient/modulation
vectors. Two strip panel consumers remove the six derivative hypotheses
formerly supplied externally. Positive step, exact grid and finite node
bounds remain explicit; numeric ideal coefficient realization and program
semantics/import remain open. Clean Linux build 3716 jobs, 21 leaves exactly
[propext, Classical.choice, Quot.sound], no new-source warnings, four mirror
files identical; 12 + 15 unchanged numerical regressions pass. No new price,
node replay, healthy detector, signed-kernel closure, producer GO or RH claim.
Evidence: docs/proofs/2350_owner_derivative_budget.md.

Record 2351 (2026-10-01): exported the original 2338 900-entry analytic
matrix and exact candidate inverse with same-run parent reproduction except
elapsed. Independent Fraction-only complex rectangle arithmetic yields
eta = 5.873158307277732e-38 and fixed-box containment of the ORIGINAL
base/correction coefficient rectangles at all 120 components. Tightest ratios
0.9999999438559326/0.999999941431241; no widening. Parent matrix digest,
coefficients, captured nodes/targets, exact width-square radii and modulations
are bound with mutation controls; 17 tests pass and checker replay is exact.
Lean now binds actual correctedPhysicalCompactLogTest Laplace values to the
actual analytic matrix mulVec, and proves unique inverse-defined coefficients
under an explicit actual determinant-unit premise. Numeric integral bounds,
actual invertibility and coefficient-box membership remain external/unimported.
No new norm price, full-grid node computation, health, signed budget GO or RH.
Evidence: docs/proofs/2351_analytic_moment_witness.md.

Record 2352 (2026-10-01): the same-owner audit rules out transferring another
base's T=28,q=2^-14 contraction to the repaired 2338/2351 all-node base.
Exact unit targets within the source slab force T strictly above captured
node 29's height 2791435723263659/35184372088832. Two Lean leaves prove
this necessary condition for actual Laplace values and the actual moment
solution, keeping the determinant premise explicit; focused build 3717 jobs,
permitted axioms only, no new-source warnings. The all-node and mandatory-only
constraints both require at least height-shell N=6 once the consumer's doubled
rho height is retained; dropping extra base constraints therefore does not
buy a first-shell shortcut and would change the owner. T=128 is NOT certified.
Same-run parent witness verification and exact n=0,1,2 support composition
perform no gate scan, node quadrature or prime enumeration. Complete source-zero
prefix semantics, numeric integral import, accepted tail and full signed budget
remain open. No map103 reopening, producer GO or RH claim. Evidence:
docs/proofs/2352_same_owner_premise_audit.md and its validation artifact.

Record 2353 (2026-10-01): same repaired base now has an external conditional
uniform contraction supplier at T=128, q=2^-14; outward upper
1.718203766281698e-16 for all sigma in [0,1], both signs and infinite height
tail. Rectangle deformation charges both connectors and both real-edge
slices, with exact-rational interval-sup cells. Delta=1/8 improves the
same-run delta=1/64 baseline; physical owner and coefficient boxes do not
change. Four Lean contour leaves pass 3716 plan jobs with only permitted
axioms and no new-source warnings. 86 tests pass; the 384-bit control
overlaps all 28 scalar point components and retains the registered q.
Point controls do not establish uniformity. Actual numerical coefficient
membership and aggregate supplier remain unimported. The q/D4/D2 supplier
must still be paired with the same owner's accepted tail inequality and
actual gate coefficient; N>=6 is only a necessary shell floor. Complete
zero prefix, source-zero identity and full signed budget remain open.
No map103 reopening, healthy detector, producer GO or RH claim. Evidence:
docs/proofs/2353_same_owner_tail_supplier.md and its validation artifact.

Record 2354 (2026-10-01): the same 2353 analytic upper contains q=2^-52.
Exact Fraction pricing of the FULL lambda-dependent acceptance formula,
with epsilon^2=(3/2)A and the proven K<=128.65 cap, yields conditional
lanes at N=6: n=2 with lambda>=256 (ratio<=0.7603893268553), or n=3
with lambda>=1e-13 (ratio<=0.2456614834776). These are scalar acceptance
intervals, not gate-selected coefficients or fixed-lambda branches. The
moment witness is rechecked in the same run; no coefficient/owner change
or new gate/prime scan occurs. Five scalar Lean leaves pass 3569 jobs with
permitted axioms and no new-source warnings; 18 new tests and exact replay
pass. The initial FULL consumer dependency probe fails at the unchanged
C1HealthyYoshidaSpectralNegativity sum rewrites (371/385); the successful
minimal scalar build explicitly does not establish consumer integration.
Complete zero prefix, source-zero identity, numerical import and full
signed gate remain open. No healthy detector, map103 reopening, GO or RH.
Evidence: docs/proofs/2354_same_owner_tail_acceptance.md and its validation.

Record 2355 (2026-10-01): HEAD f9809767 applies the intended reverse
`Finset.sum_sdiff` rewrite and unfolds `spectralWeilValue` before the shell
split, addressing the two 2354 consumer-shape failures. A WSL replay found
the pinned Lean toolchain but could not reach a theorem result because the
existing `.lake/packages/mathlib` checkout has local changes; a direct Lean
fallback lacked the cached `C1HealthyYoshidaClosedPrefix.olean`. This is an
environmental verification boundary, not a pass and not a new source failure.
The consumer remains UNVERIFIED; the scalar-only 2354 scope and the selected
physical-kernel gate remain binding. Evidence: docs/proofs/2355_same_owner_consumer_integration_audit.md
and results/2355_same_owner_consumer_integration_audit.json.

Record 2356 (2026-10-01): replaying 2337/2339 with the available Arb
environment confirms that the marked-square sign remains numerical only: all
eight mandatory source values miss their nominal targets by imaginary residuals
of roughly 3e-9 to 7e-9. More importantly, the 2339 replay fails the old pin
at node j=-50: the maximum upper bound is 2644543.1669421422 versus the old
2644542.8515 pin. The old owner margin is therefore not transferable to the
live producer. The next admissible target is a same-run certified budget
reconstruction before complete-prime-book signed readback. Evidence:
docs/proofs/2356_actual_owner_replay_budget_boundary.md and
results/2356_actual_owner_replay_budget_boundary.json.

Record 2357 (2026-10-01): direction correction. The 2339 pin failure is an
overcharged additive ledger: it retains old coefficient inflation while adding
the repair cost. The same-owner recomposed transfer in 2340 removes that
double charge and replays 101/101 nodes under the unchanged pin, with maximum
706456.1761485816 at j=-50; 2340 and 2341 selftests pass 9/9 and 11/11.
This makes 2340, not a raised pin, the valid next object. Its directed nodal
upper theorem and coordinate identity remain open before Lean/producer import.
Evidence: docs/proofs/2357_recomposed_transfer_direction_correction.md and
results/2357_recomposed_transfer_direction_correction.json.

Record 2358 (2026-10-01): a directed MPFR interval smoke on zero-width boxes
at the binding sigma=-0.5, using 1001 points, remains finite and gives
channel integrals 2.69063823185, 8606.22586174, 90.7869637295, and
125446.9641178. The interval min-product is 337532.3977. This rejects an
immediate natural-interval explosion and supports pursuing the full nodal-upper
bridge. It is explicitly not a certificate: the 240001-node order, directed
accumulation/remainder, coordinate identity, and Lean import remain open.
Evidence: docs/proofs/2358_directed_nodal_interval_smoke.md and
results/2358_nodal_interval_smoke.json.

Record 2359 (2026-10-01): the 2242 directed MPFR point-box evaluator completed
the full 240001-node producer grid at sigma=-0.5, with fixed 20001-node spans
and ordered parent accumulation. It gives min-product 337039.47691483924,
matching the stored 2303 point row 337039.47691484215 at displayed precision.
A 1001-node sequential/12-worker control is equal in all four integrals and
the min-product. The actual `np.linspace` array differs from the exact
arithmetic grid at 239923/240001 nodes, with maximum exact-fraction gap
4757/2814749767106560000; this is the 2341 coordinate-charge obligation, not
an identity claim. This is a strong evaluator control, not yet a theorem:
directed accumulation, trapezoid remainder, coordinate charge, and Lean import
remain open. Evidence: scripts/routea_nodal_interval_fullgrid_2359.py,
docs/proofs/2359_fullgrid_nodal_interval_replay.md, and
results/2359_nodal_interval_fullgrid.json.

Record 2360 (2026-10-01): the coordinate mismatch is now isolated in a Lean
interface. `nodeUpper_of_coordinate_charge2359` composes actual-grid node
uppers, an analytic transfer charge, and final charged uppers; its Lipschitz
specialization takes the coordinate displacement and nonnegative Lipschitz
constant explicitly. This is only the theorem-shaped bridge needed before
feeding the exact-grid hypothesis to the existing weighted chord-panel bound.
The 2359 evaluator remains numerical-only: no Lipschitz estimate, directed
accumulation bound, or producer import is asserted. Evidence:
ConnesWeilRH/Dev/C1RouteACoordinateCharge.lean and its audit module.

Record 2361 (2026-10-01): the coordinate-charge file now also contains a
generic segment theorem, `norm_value_le_of_deriv_bound2359`, turning a
derivative-norm bound into the one-sided value transfer needed by the 2359
stored-grid replay. The Lean audit passes. Its application to the weighted
corrected physical function, orientation split, and directed accumulation
remain open; no numerical value or producer premise is imported.
Evidence: docs/proofs/2361_segment_derivative_coordinate_charge.md and
results/2361_segment_derivative_coordinate_charge.json.

Record 2362 (2026-10-01): the coordinate bridge reaches the weighted owner.
`weightedFunction2348_norm_le_of_coordinate_segment2359` derives the transfer
charge `exp(|sigma| radius) (|sigma| zeroBound + firstBound)` from a first
derivative bound on an ordered coordinate segment. The corrected-physical
specialization, mixed coordinate orientation, directed accumulation, and
trapezoid remainder remain open. Evidence: docs/proofs/2362_weighted_coordinate_transfer.md
and results/2362_weighted_coordinate_transfer.json.

Record 2363 (2026-10-02): the weighted transfer is instantiated for the live
`correctedPhysical` owner using the existing `ownerDerivativeBudget2350`.
Nonnegativity of the owner budgets is proved from their defining positive
sums, and the segment theorem passes Lean audit. The all-node coordinate
orientation split, directed accumulation, and trapezoid remainder remain
open; no producer GO is claimed. Evidence: docs/proofs/2363_owner_weighted_coordinate_charge.md
and results/2363_owner_weighted_coordinate_charge.json.

Record 2364 (2026-10-02): the owner coordinate bridge now handles both
coordinate orientations. `correctedPhysical_weighted_coordinate_transfer2359`
returns a single absolute-displacement charge after splitting on the order of
the stored and affine coordinates; it only assumes the connecting interval is
inside the owner window. The full coordinate-pair data, directed accumulation,
and trapezoid remainder remain open. Evidence: docs/proofs/2364_symmetric_coordinate_charge.md
and results/2364_symmetric_coordinate_charge.json.

Record 2365 (2026-10-02): endpoint reduction. A new owner wrapper derives
the mixed-orientation coordinate charge from endpoint membership alone; the
closed interval containment is proved in Lean by order convexity. This leaves
only the actual/ideal endpoint facts and the numeric displacement/accumulation
certificates to be supplied. Evidence: docs/proofs/2365_endpoint_window_reduction.md
and results/2365_endpoint_window_reduction.json.

Record 2366/2367 (2026-10-02): the coordinate replay exposed a real radius
rounding boundary. Actual binary64 `linspace` endpoints do not lie in the
exact `storedWidth 4²` window, while the ideal affine endpoints do; all actual
points lie in the existing outer `stripRadius2303 = 6.5536001` pin. The owner
coordinate bridge is generalized to arbitrary radius and now consumes this
outer pin with global derivative budgets. This correction is binding; no exact
owner-window identity is claimed. Evidence: docs/proofs/2366_coordinate_pair_endpoint_certificate.md,
docs/proofs/2367_outer_pin_radius_correction.md, and the associated results.

Record 2368 (2026-10-02): the 2359 full-grid run now carries exact
`Fraction.from_float` sums of the generated binary64 terms. The NumPy-versus-
exact-term maximum gap is `3.058588208835539e-10` on channel 3. This quantifies
the ordered accumulation gap but is not a directed MPFR theorem; pointwise
interval conversion and trapezoid remainder remain open. Evidence:
docs/proofs/2368_exact_binary64_accumulation_audit.md and
results/2368_exact_binary64_accumulation_audit.json.

Record 2369 (2026-10-02): the full grid now has a 256-bit MPFR `RNDU` upper
accumulation for the generated binary64 point terms, with per-span reset and
ordered parent reduction. This closes only the term-accumulation layer;
pointwise interval construction and trapezoid remainder remain open. Evidence:
docs/proofs/2369_directed_binary64_term_accumulation.md and
results/2369_directed_binary64_term_accumulation.json.

Record 2370 (2026-10-02): the directed path is upgraded to construct each
pointwise rectangle norm, exponential weight, endpoint half-weight, and span
sum directly with 256-bit MPFR `RNDU`. The full-grid readings remain stable
to displayed precision. This is conditional on the 2242 rectangle bounds;
the point-box function identity and trapezoid remainder remain open. Evidence:
docs/proofs/2370_directed_pointwise_norm_exp_accumulation.md and
results/2370_directed_pointwise_norm_exp_accumulation.json.

Record 2371 (2026-10-02): the existing 2348 panel remainder and the outer-pin
coordinate charge are now priced together at the binding sigma. This is a
stored-operand planning price only; it does not certify the pointwise bounds
or import the producer. Evidence: docs/proofs/2371_coordinate_panel_price.md,
scripts/routea_coordinate_panel_price_2371.py, and its result.

Record 2372 (2026-10-02): the four-channel price identifies `corr_D2` as the
binding obstruction at 240001 nodes: the simple panel remainder is
`1.0470852x` its directed pointwise reading. A refinement to roughly 776610
nodes would only target a 0.1 ratio under the same crude curvature bound;
this is a planning no-close, not a producer-family impossibility result.
Evidence: docs/proofs/2372_corr_d2_panel_binding_price.md and
results/2372_corr_d2_panel_binding_price.json.

Record 2373 (2026-10-02): same-owner refinement at 347311 nodes completed
with the unchanged evaluator and directed pointwise path. Readings remain
stable, while the priced `corr_D2` panel remainder falls to half the directed
reading as predicted by the `h²` law. This is controlled refinement evidence,
not a trapezoid theorem or producer GO. Evidence: docs/proofs/2373_same_owner_refinement_347311.md
and results/2373_same_owner_refinement_347311.json.

Record 2374 (2026-10-02): same-owner refinement at 776611 nodes reaches the
pre-registered `corr_D2` panel ratio target: approximately `0.0999996666` of
the directed reading, with stable four-channel values. This is controlled
price evidence, not yet a Lean node import or producer GO. Evidence:
docs/proofs/2374_same_owner_refinement_776611.md and
results/2374_same_owner_refinement_776611.json.

Record 2375 (2026-10-02): the Lean finite-sum bridge
`compositeNodeUpper_le_of_nodewise_coordinate_charge2359` and its interface
ledger assemble the 2374 node reading with the coordinate and panel prices.
This is not yet a numerical certificate: nodewise import, directed
accumulation, and trapezoid remainder proof remain open. Evidence:
docs/proofs/2375_composite_charge_bridge.md and
results/2375_composite_charge_bridge.json.

Record 2376 (2026-10-02): the evaluator now emits explicit span and final
directed-rounding dominance controls. They are all true on the 1001-node
sequential regression, but the bounded 776611-node replay timed out without
an artifact. This is therefore a control improvement, not a full-grid
certificate or producer GO. Evidence:
docs/proofs/2376_directed_accumulation_controls.md and
results/2376_directed_accumulation_control_1001.json.

Record 2377 (2026-10-02): exact binary64 `Fraction` auditing is now an
explicit optional mode. The 1001-node full-audit and skip-audit paths agree
on all evaluator fields, while the 776611-node replay still exceeds the
bounded 180-second run even with the audit disabled. This isolates, but does
not solve, the remaining runtime bottleneck. Evidence:
docs/proofs/2377_exact_audit_mode_split.md and
results/2377_exact_audit_mode_split.json.

Record 2378 (2026-10-02): the delayed 776611-node replay artifact shows the
new span dominance test fails for `base_M0` and `corr_D2`, while a final
global comparison passes all four channels. This is diagnosed as a
cross-expression comparison between nearest-float terms and a separately
recomputed MPFR directed path; global dominance is not accepted as a repair.
The directed certificate path remains open. Evidence:
docs/proofs/2378_fullgrid_span_control_failure.md and
results/2378_fullgrid_span_control_failure.json.

Record 2380 (2026-10-02): the owner-level Lean bridge now consumes actual
coordinate node upper bounds plus a transfer charge and feeds them directly
into the existing corrected-physical stripNorm/curvature theorem. The
analytic interface is audited, but no numerical node import is claimed.
Evidence: docs/proofs/2380_owner_coordinate_charge_strip_bridge.md and
results/2380_owner_coordinate_charge_strip_bridge.json.

Record 2381 (2026-10-02): after the 2378 expression mismatch, the evaluator
adds an RNDU binary64 roundup of each already-directed MPFR term and sums it
through an independent directed accumulator. All four channels pass this
same-expression control at 1001 nodes and preserve the prior directed values;
the 776611-node bounded 300-second replay produced no artifact. Evidence:
docs/proofs/2381_same_expression_directed_roundup.md and
results/2381_same_expression_directed_roundup.json.

Record 2382 (2026-10-02): a 5001-node, 16-worker benchmark of the corrected
same-expression path completes in 38.24 seconds with the directed controls
preserved. WSL exposes 16 CPUs and ample memory; the remaining full-grid
obstacle is per-node evaluator cost. Evidence:
docs/proofs/2382_evaluator_runtime_benchmark.md and
results/2382_evaluator_runtime_benchmark.json.

Record 2383 (2026-10-02): the evaluator now shares per-family outward
geometry bounds across the four channels. The 1001-node exact-audit control
passes, and the 5001-node/16-worker benchmark improves from 38.24 s to
32.74 s without tightening the enclosure. The full-grid certificate remains
open. Evidence: docs/proofs/2383_shared_geometry_cache.md and
results/2383_shared_geometry_cache.json.

Record 2384 (2026-10-02): the shared cache now fails closed unless all four
channel `Kernel.recs` `(a, theta)` signatures are identical. The current
owner passes with 30 aligned records per channel. Evidence:
docs/proofs/2384_shared_geometry_alignment_guard.md and
results/2384_shared_geometry_alignment_guard.json.

Record 2385 (2026-10-02): the shared outward-geometry evaluator completed the
776611-node/16-worker replay. Same-expression RNDU roundup dominates the MPFR
term accumulator in all four channels. The updated `corr_D2` panel/readout
ratio is `0.09999966654156531`, below the registered 0.1 target, but the
analytic/numerical import obligations remain open. Evidence:
docs/proofs/2385_shared_geometry_fullgrid.md and
results/2385_shared_geometry_fullgrid.json.

Record 2386 (2026-10-02): the composite-charge ledger is parameterized and
re-read against the 2385 full-grid artifact. The resulting `corr_D2` assembled
upper is `137991.3586630174`; this is connected to the audited Lean bridge but
not imported as a Lean numerical certificate. Evidence:
docs/proofs/2386_fullgrid_composite_charge_bridge.md and
results/2386_fullgrid_composite_charge_bridge.json.

Record 2387 (2026-10-02): the Lean composite layer now has an explicit
per-cell identity and pointwise node-upper monotonicity theorem. These are
the formal consumers needed before importing the 2385 directed node values;
the independent Lean audit passes. Evidence:
docs/proofs/2387_composite_node_monotonicity.md and
results/2387_composite_node_monotonicity.json.
