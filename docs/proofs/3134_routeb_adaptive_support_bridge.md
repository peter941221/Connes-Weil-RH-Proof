# Record 3134: Route-B adaptive powered-owner support bridge

Date: 2026-10-27.

Status: Lean-verified logical bridge; no numerical gate certificate and no RH claim.

The 3117 powered owner is the exact owner used by the adaptive negative-span
theorem. Its base and correction each have support in `[-10, 10]`. The existing
convolution support theorem expands this to the sum of the `n + 1` base copies
and the correction, and the half-density shift preserves support. Record 3134
exports that actual owner support as an open interval with a one-unit margin.

The 3130 gate equivalence is now also available in a generic form that accepts
an explicit support witness. Applying it to the 3117 owner proves:

```text
actual 3117 owner support
        |
        v
variable-lambda gate predicate <=> same-span orbitWindowSemiLocalGate
        |
        +-- triple vanishing + qw < 0
        v
gate predicate is impossible
```

The proof does not instantiate the support bound numerically for a selected
zero, does not prove a signed continuum margin, does not certify prime-power
coverage or tail remainders, and does not establish Producer GO, SourceRH, or
RH. It closes only the interface gap identified in record 3133.

The same module also exports `exists_eventual_powered_owner_rejects_gate3135`.
It composes the 3117 eventual existence theorem with the support bridge and
the full annihilator triple-vanishing lemma. Its conclusion is still logical:
for the constructed family and every `lambda >= ell`, the span has negative
`qw` and the corresponding gate predicate is impossible.

Evidence:

- `ConnesWeilRH/Dev/C1RouteBAdaptiveSupportBridge3134.lean`
- `ConnesWeilRH/Dev/C1RouteBVariableLambdaGate3130.lean`
- `results/3134_routeb_adaptive_support_bridge_audit.json`
