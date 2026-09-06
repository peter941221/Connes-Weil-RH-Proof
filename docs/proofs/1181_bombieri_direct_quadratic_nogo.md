# 1181 — No-go for the direct Bombieri quadratic P2 socket

Date: 2026-09-06

## Formal contradiction

For a healthy detector `HealthyYoshidaDetectorData rho g`, the existing
spectral branch proves `qw g < 0`.  Record 1178 proves the finite weighted
Hermitian `H` quadratic form is nonnegative for positive `t`.  Therefore an
instance of `BombieriQuadraticP2BridgeData g`, whose defining field is

```text
qw g = Re (star w ⬝ᵥ (H(Γ;t) *ᵥ w)),
```

would yield an immediate contradiction.  The guard is formalized by
`not_bombieriQuadraticP2BridgeData_of_healthyDetectorData` and its `Nonempty`
variant.

## Route consequence

The direct matrix equality is not a viable P2 producer for the healthy owner.
The conditional SourceRH adapters are retained as audit interfaces, but are
provably vacuous on healthy detectors.  Active P2 work must use a signed
semi-local/profile comparison or a genuinely renormalized trace readback that
does not identify `qw` with this nonnegative finite form.

## Evidence

The focused bridge/audit build completed in 3665 jobs with no `error:` lines or
`sorryAx`; the new guards audit to
`[propext, Classical.choice, Quot.sound]`.
