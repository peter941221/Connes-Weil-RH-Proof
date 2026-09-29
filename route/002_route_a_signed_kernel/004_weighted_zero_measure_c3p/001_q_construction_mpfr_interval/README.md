# 001 — q-construction MPFR interval

Status: `MPFR-Q-INTERVAL-THREE-NODE-CORRECTED`; complete-owner certificate
OPEN. This is a terminal subroute of the weighted-zero-measure C3′ candidate,
not a separate producer route and not an RH claim.

## Consumer and owner

The consumer remains the same-owner selected-detector inequality

```text
qw(g) >= 0 -> SourceRH -> Mathlib RH.
```

The owner remains the exact closed-ball source-zero owner with its actual
support-derived visible-prime set. No ROOT-only model, fixed-prime model,
known-zero prefix, or auxiliary span is admissible as a replacement.

## Current certificate

Proof record [2228](../../../../docs/proofs/2228_routea_q_mpfr_complex_weight_fix.md)
corrected the complex-weight implementation used by records 2225--2227. The
corrected directed-MPFR runs cover all 30 families and the complete GL/Simpson
rule at nodes 2, 3, and 29:

```text
node 2    8.792971355816332e-09   zero interval failures
node 3    8.063938632912915e-09   zero interval failures
node 29   6.475830084303228e-09   zero interval failures
```

Only the corrected readings are authoritative. They are stability evidence,
not a universal 30-node bound and not the signed producer inequality.

## Acceptance ladder

1. Extend the corrected evaluator to every one of the 30 owner nodes.
2. Enclose the binary64 input construction and finite-sum accumulation.
3. Check one uniform charge against the candidate error budget.
4. Transfer the enclosure to the complete actual owner.
5. Prove the remaining strict signed margin

   ```text
   Arch + C3'_aggregate <= -epsilon(rho, N) + B_zm(rho, N)
   B_zm(rho, N) < epsilon(rho, N).
   ```

Failure at any step is a scoped numerical or owner-transfer obstruction; it
does not license a global no-go. A successful interval run still does not by
itself prove `qw(g) >= 0`.

## Evidence

- [2228](../../../../docs/proofs/2228_routea_q_mpfr_complex_weight_fix.md)
- [104 Route A campaign](../../../../docs/map/104_route_a_four_round_campaign.md)
- `scripts/routea_weighted_zero_q_mpfr_interval_binding_2225.py`
