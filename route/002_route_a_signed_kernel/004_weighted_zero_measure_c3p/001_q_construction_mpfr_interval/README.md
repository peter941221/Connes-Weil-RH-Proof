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
   **closed (2232, 2233):** per-term chain and family stitch are outward
   (2232: no deficits at all 30 nodes, slacks 2.5e-15 to 4.7e-15); the
   operand ledger is priced (2233: c-radius channel 1.12e-05 relative,
   w channel screened at 9.2e-14, x channel +15.2% per ulp on the binding
   node, about 2.1e-05 of the target).
3. Check one uniform charge against the candidate error budget.
   **done (2231):** uniform charge / target `1.4068690278731986e-04`,
   `2.7956x` below the parameterized 2224 assembly.
4. Transfer the enclosure to the complete actual owner. **open; first gap
   opened (2234-2236):** the low-shell/`B_zm` side now carries a viable
   outward envelope (`C_upper = 2721865.34164875`, `tail/margin =
   0.07743395177596035`, `12.9x` headroom; 2234 measured the too-loose
   first brick at `70.74x`, 2235 separated the channels, 2236 charged the
   solve floor). Remaining: 2119 cardinality `48.43x`, 2157 near-pin
   floor, 2134 horizon, the 2236 generation channel (screened `1e-12`),
   the panel allowance and the multiplicity proxy.
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
- [2232](../../../../docs/proofs/2232_routea_weighted_zero_family_stitch_closure.md)
- [2233](../../../../docs/proofs/2233_routea_weighted_zero_operand_ledger.md)
- [2234](../../../../docs/proofs/2234_routea_weighted_zero_direct_product_outward_envelope.md)
- [2235](../../../../docs/proofs/2235_routea_weighted_zero_direct_product_reprice.md)
- [2236](../../../../docs/proofs/2236_routea_weighted_zero_direct_product_solve_floor.md)
- [2228](../../../../docs/proofs/2228_routea_q_mpfr_complex_weight_fix.md)
- [104 Route A campaign](../../../../docs/map/104_route_a_four_round_campaign.md)
- `scripts/routea_weighted_zero_q_mpfr_all_nodes_2229.py`
- `scripts/routea_weighted_zero_uniform_charge_budget_2231.py`
- `scripts/routea_weighted_zero_family_stitch_2232.py`
- `scripts/routea_weighted_zero_operand_ledger_2233.py`
- `scripts/routea_weighted_zero_xwidth_charge_2233.py`
- `scripts/routea_weighted_zero_direct_product_outward_2234.py`
- `scripts/routea_weighted_zero_direct_product_reprice_2235.py`
- `scripts/routea_weighted_zero_direct_product_solve_floor_2236.py`
