# Record 3131: Route-B adaptive same-owner gate screen

Date: 2026-10-27.

Status: fail-closed evidence screen implemented; no actual adaptive owner
manifest was supplied, so the control result is `CONTROL-FAIL / OWNER-DATA-MISSING`.

The screen requires the exact adaptive owner identity and all premises needed
before a signed gate can be considered:

```text
actual owner + rho + lambda
          |
          +-- complete globalPrimeIndexSet
          +-- both frequency signs
          +-- signed prime-power residual bound
          +-- rounding allowance
          +-- adaptive tail budget
          v
    candidate gate may be evaluated
```

The screen does not calculate a gate margin, infer omitted prime-power terms,
replace the owner with a model owner, or connect a candidate to the negative
`qw` theorem. A structurally complete manifest would still require an
independent continuum certificate and a same-owner signed inequality.

Evidence:

- `scripts/routeb_adaptive_owner_gate_screen_3131.py`
- `results/3131_routeb_adaptive_owner_gate_screen.json`
- `docs/proofs/3130_routeb_variable_lambda_gate_bridge.md`
- Project records 3116, 3117, and 3130
