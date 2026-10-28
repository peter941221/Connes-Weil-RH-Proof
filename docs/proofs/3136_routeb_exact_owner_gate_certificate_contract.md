# Record 3136: Route-B exact-owner gate certificate contract

Date: 2026-10-27.

Status: fail-closed certificate contract; no owner manifest or gate proof is
created by this record.

The 3131 screen checked whether required fields existed. Record 3136 checks
their semantic shape before any future numerical evaluator is allowed to run:

```text
exact owner identity + rho + lambda
        |
        +-- N, n, route-node digest
        +-- sorted unique positive global prime indices
        +-- certified positive-frequency interval
        +-- certified negative-frequency interval
        +-- certified signed residual interval
        +-- certified nonnegative rounding interval
        +-- certified nonnegative adaptive-tail interval
        +-- certified gate-margin interval
        v
certificate-ready structure only
        |
        v
independent Lean readback still required
```

The script deliberately does not compute or infer a gate margin. A structural
pass is not `fullWeilPositivity`, not `qw >= 0`, not Producer GO, and not RH.
The exact owner, prime-power completeness, signed residual theorem, continuum
readback, and Lean-side consumption remain separate obligations.

Record 3137 is now the required owner-side prerequisite: it identifies the
3117 powered owner and fixes the exact `globalPrimeIndexSet` membership rule.
The 3136 screen must not consume a manifest produced from a support cutoff,
model owner, or larger prime-power closure.

Evidence:

- `scripts/routeb_exact_owner_gate_certificate_contract_3136.py`
- `results/3136_routeb_exact_owner_gate_certificate_contract.json`
- `scripts/routeb_adaptive_owner_gate_screen_3131.py`
- `ConnesWeilRH/Dev/C1RouteBAdaptiveOwnerReadback3137.lean`
- `results/3137_routeb_adaptive_owner_readback_audit.json`
