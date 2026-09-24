# 104 — Route A: selected-owner signed physical-kernel campaign

Date: 2026-09-24.

Status: active campaign. Round 1 is FORMAL; the residual sign is OPEN. This
record is subordinate to [003](003_b1_b5_minimal_exit_route_selection.md),
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

### Round 2 — signed residual budget (OPEN)

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

Remaining: the signed residual inequality and a strict quantitative margin.

Round 1 failure would be an owner mismatch or an inability to express the
finite sum using the selected owner's exact visible set. Such a failure would
stop this lane and be recorded as a named no-go; merely adding another wrapper
would not count as progress.

Evidence level: FORMAL for Round 1; PROJECT CANDIDATE/OPEN for Rounds 2–4.
