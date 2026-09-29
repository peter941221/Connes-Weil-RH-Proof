# 001 — q-construction MPFR interval

Status: `MPFR-Q-INTERVAL-ALL-NODE-OUTWARD`; complete-owner certificate
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

Proof record [2229](../../../../docs/proofs/2229_routea_weighted_zero_all_node_outward_envelope.md)
executes the full 30-node envelope with directed MPFR charge accumulation
(`mpfr_exp`/`mpfr_mul`/`mpfr_add` RNDU at 256-bit):

```text
binding node 2   8.792971355816406e-09   zero interval failures
minimum node 1   4.441432860466601e-09   max/min 1.9797600531312878
all 30 nodes     zero interval failures  1,944,360 terms per node
```

The binary64 operands are exact under the discrete-defined convention fixed
by [2230](../../../../docs/proofs/2230_routea_weighted_zero_operand_provenance_and_owner_transfer_preflight.md).
The 2228 three-node readings are superseded by the 2229 envelope and remain
valid as drift controls (outward at the binary64 rounding level).

## Acceptance ladder

1. Extend the corrected evaluator to every one of the 30 owner nodes.
   **done (2229).**
2. Enclose the binary64 input construction and finite-sum accumulation.
   **open** (per-term chain and family stitch are outward; the operand
   construction ledger of 2230 item 2a remains unpaid).
3. Check one uniform charge against the candidate error budget.
   **done (2231):** uniform charge / target `1.4068690278731986e-04`,
   `2.7956x` below the parameterized 2224 assembly.
4. Transfer the enclosure to the complete actual owner. **open** (2119
   cardinality `48.43x`, 2157 near-pin floor, 2134 horizon, 2197 low-shell
   side).
5. Prove the remaining strict signed margin

   ```text
   Arch + C3'_aggregate <= -epsilon(rho, N) + B_zm(rho, N)
   B_zm(rho, N) < epsilon(rho, N).
   ```

Failure at any step is a scoped numerical or owner-transfer obstruction; it
does not license a global no-go. A successful interval run still does not by
itself prove `qw(g) >= 0`.

## Evidence

- [2229](../../../../docs/proofs/2229_routea_weighted_zero_all_node_outward_envelope.md)
- [2230](../../../../docs/proofs/2230_routea_weighted_zero_operand_provenance_and_owner_transfer_preflight.md)
- [2231](../../../../docs/proofs/2231_routea_weighted_zero_uniform_charge_vs_budget.md)
- [2228](../../../../docs/proofs/2228_routea_q_mpfr_complex_weight_fix.md)
- [104 Route A campaign](../../../../docs/map/104_route_a_four_round_campaign.md)
- `scripts/routea_weighted_zero_q_mpfr_all_nodes_2229.py`
- `scripts/routea_weighted_zero_uniform_charge_budget_2231.py`
