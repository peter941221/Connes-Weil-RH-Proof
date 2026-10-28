# Record 3130: Route-B variable-lambda same-owner gate bridge

Date: 2026-10-27.

Status: formal interface added and audited PASS on the Linux ext4 checkout
(3830 build jobs; exact standard axiom trio). No numerical gate margin,
Producer GO, SourceRH, or RH claim.

## Purpose

The adaptive Route-B campaign cannot rely on the fixed coefficient `lambda = 24`.
Record 3116 rules out a universal fixed quadratic pin near the critical line, and
record 3117 allows the tail constants to depend on `rho`. This module therefore
keeps `lambda` as an explicit real parameter while preserving the exact owner.

## Formalized interfaces

```text
variableLambdaGatePredicate3130 rho g lambda
        <-> gate matrix quadratic form at [1, -lambda]

variableLambdaGatePredicate3130 rho g lambda
        <-> signed ICgate margin

variableLambdaGatePredicate3130 rho pkg.g lambda
        <-> orbitWindowSemiLocalGate on the same owner
```

The source is:

```text
ConnesWeilRH/Dev/C1RouteBVariableLambdaGate3130.lean
```

The paired kernel audit is:

```text
ConnesWeilRH/Dev/C1RouteBVariableLambdaGate3130Audit.lean
```

The reproducible checker is:

```text
scripts/routeb_variable_lambda_gate_audit_3130.py
```

## Boundary

This record does not prove that any candidate `lambda` has the required sign.
The next numerical artifact must use the actual adaptive owner, the complete
prime-power set, both frequency signs, and an independently controlled margin.
Only a surviving candidate may be connected to the negative `qw` theorem from
record 3117.
