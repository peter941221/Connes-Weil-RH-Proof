# 104 — Route A: selected-owner signed physical-kernel campaign

Date: 2026-09-24.

Status: active campaign. Round 1 is FORMAL. Round 2 is a scoped NO-GO for the
current correction-selector API: its residual sign cannot be derived from the
fields currently exposed. This is not a no-go for a strengthened selector.
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

### Round 2 — signed residual budget (SCOPED NO-GO: current selector API)

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

The round-2 audit found a named underdetermination in the current owner API.
`ResidualCorrectionFamily` in
`C1HealthyYoshidaCorrectionFamily.lean` exposes only:

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

Scope: this rules out closing Round 2 by the current selector fields alone; it
does not rule out a new correction selector with proved physical-kernel control.
The evidence and dependency audit are recorded in
[1923](../proofs/1923_route_a_round2_current_api_underdetermination.md).

### Round 3 — parameter and margin closure (OPEN)

Prove that the correction, finite zero prefix, orbit index, support radius,
visible-prime cutoff, and `epsilon` satisfy the selected-owner quantifiers in
the correct order for every hypothetical right off-line zero. Preserve triple
vanishing and off-line detection.

### Round 4 — consumer assembly and audit (OPEN)

Feed the strict budget through `081`/`082`, prove the same-owner gate and
`qw >= 0`, then invoke the existing contradiction and RH bridge. No new
generic exit wrapper is permitted.

## Round-1 ledger and stop rule

Known: selected-owner construction, support-derived finite owner, triple
vanishing, strict spectral negativity, and the generic residual identity.

Removed in this round: `finitePrimeSum` as an opaque selected-owner input; it
is now exactly the finite weighted profile attached to the actual owner.

Remaining after Round 2: a new owner/selector theorem must provide physical
derivative control before a signed residual inequality can be attempted. The
old residual-budget field is not accepted as progress.

Round 1 failure would be an owner mismatch or an inability to express the
finite sum using the selected owner's exact visible set. Such a failure would
stop this lane and be recorded as a named no-go; merely adding another wrapper
would not count as progress.

Evidence level: FORMAL for Round 1; SCOPED API NO-GO for Round 2; PROJECT
CANDIDATE/OPEN for Rounds 3–4, which cannot start on the current owner without
first removing this no-go.
