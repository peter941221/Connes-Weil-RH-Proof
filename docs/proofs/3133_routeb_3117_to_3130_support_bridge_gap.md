# Record 3133: Route-B 3117-to-3130 support bridge gap

Date: 2026-10-27.

Status: interface audit only; no new producer premise or RH claim.

The source review compared the two live interfaces:

```text
3117 exists_eventual_powered_span_qw_neg3117
        |
        +-- same powered span has qw < 0
        +-- same powered span has triple vanishing
        +-- no exported support witness in the conclusion
        v
3130 variableLambdaGatePredicate3130
        |
        +-- owner gate equivalence currently consumes RhoOwnerPackage3106
        +-- package supplies geometry.support_bound
        v
orbitWindowSemiLocalGate
```

The missing bridge is not an owner-name equality. It is an explicit support
certificate for the powered owner and its annihilator, strong enough to replay
the 3130 `orbitWindowSemiLocalGate` equivalence on the exact powered span.
The local support proof inside 3117 is consumed while constructing the tail
argument and is not exported as a theorem in
`exists_eventual_powered_span_qw_neg3117`.

Therefore no new theorem is added here. Replacing the missing support witness
with the model window, a package field from another owner, or a support cutoff
would be unsound. The next admissible implementation is to export and audit a
support theorem from the 3117 powered-family construction, then consume that
witness in a generic 3130 gate-equivalence theorem.

Evidence:

- `ConnesWeilRH/Dev/C1RouteBAdaptivePoweredTail3117.lean`
- `ConnesWeilRH/Dev/C1RouteBVariableLambdaGate3130.lean`
- `ConnesWeilRH/Dev/C1RouteBAdaptiveVariableLambdaContradiction3132.lean`
- `ConnesWeilRH/Dev/C1RouteBRhoOwnerPackage3106.lean`
- `docs/proofs/3117_routeb_adaptive_powered_tail.md`