# 2273 - Multiplicity proxy diagnostic (withdrawn interpretation)

Date: 2026-09-30
Correction: record 2274

## Current status

Record 2274 withdraws the claim that the former proxy under-rounds the
Lean-defined constant. The 2273 diagnostic used the standard xi value
pi/6, while the project defines doubled xi and Lean proves its value at
two is pi/3. The diagnostic therefore evaluated the wrong normalization.

Lean now proves both of the following without numeric input hypotheses:

```text
spectralMultiplicityConstant <= 128.65
spectralMultiplicityConstant < 128.70692502980964
```

The former proxy was safe. The 2273 increase to 128.70692502981 and the
associated tail increase to 4894093747.7643 remain conservative, but the
claimed need for those increases was incorrect.

## Historical diagnostic

The original diagnostic reported the following values for the
half-normalized expression, not the project's multiplicity constant:

```text
half-normalized expression   128.706925029809646157520238638184...
former proxy                 128.706925029809640000000000000000...
former proxy - expression    -6.157520238638...e-15
```

The original artifact is preserved byte-for-byte in
`results/2273_multiplicity_proxy_audit_superseded.json`. Its
OLD-PROXY-UNDER-ROUNDS status belongs to the incorrect convention and
licenses no statement about the Lean-defined constant. The original five
regression tests reproduced the same wrong convention; they did not
independently check normalization.

## Corrected diagnostic and formal proof

The existing script and primary artifact now use pi/3, record correction
2274, and retain the half-normalized expression as a historical comparison.
The regression suite checks that these are distinct and that both proxies
cover the project expression at 60, 100, and 140 digits. These evaluations
remain diagnostics.

`ConnesWeilRH/Dev/C1RouteAMultiplicityBound.lean` supplies the analytic
proof. Record [2274](2274_routea_multiplicity_bound.md) gives the component
bounds and producer consumer without hmult. The strip, signed margin,
non-tail charge, and gap obligations remain open. No producer GO, no gate
sign change, and no RH claim.
