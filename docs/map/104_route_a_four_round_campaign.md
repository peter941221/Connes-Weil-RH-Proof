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
