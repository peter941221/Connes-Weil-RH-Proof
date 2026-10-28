# Record 3132: Route-B adaptive variable-lambda contradiction adapter

Date: 2026-10-27.

Status: FORMAL-PASS. The exact same-owner contradiction adapter is compiled and
axiom-audited. Numerical gate construction and RH remain open.

For a `RhoOwnerPackage3106 rho`, the theorem
`negative_owner_rejects_variable_lambda_gate3132` proves:

```text
same owner span v(lambda)
        |
        +-- triple vanishing
        +-- qw(v(lambda)) < 0
        v
        not variableLambdaGatePredicate3130 rho g lambda
```

The proof first transports the 3130 variable-lambda predicate to the
owner-local `orbitWindowSemiLocalGate`. The existing gate bridge then gives
`0 <= qw(v(lambda))`, contradicting the supplied strict negative value.

This is a contradiction adapter, not a producer result. It does not construct
the actual adaptive owner manifest, prove a signed residual bound, certify a
continuum margin, or instantiate the 3117 existential choices with numerical
values. The owner, span, `lambda`, and triple-vanishing premise remain the same
object throughout the theorem.

Evidence:

- `ConnesWeilRH/Dev/C1RouteBAdaptiveVariableLambdaContradiction3132.lean`
- `ConnesWeilRH/Dev/C1RouteBAdaptiveVariableLambdaContradiction3132Audit.lean`
- `scripts/routeb_adaptive_variable_lambda_contradiction_audit_3132.py`
- `results/3132_routeb_adaptive_variable_lambda_contradiction_audit.json`
- `ConnesWeilRH/Dev/C1RouteBVariableLambdaGate3130.lean`
- `ConnesWeilRH/Dev/C1RouteBAdaptivePoweredTail3117.lean`