# 021 — R3 leakage defect telescoping

**Date:** 2026-09-14.

**Status:** formal structural brick; supporting route record, not an RH
claim.

**Consumer:** the healthy-`CompactLog`, B5-shaped statement
`0 <= C1SameOwnerWeil.qw g` for the same tower-selected detector.

## 1. Exact result

Let `p_b` be the doubled-shift radial projection and
`T_b = p_b * q_1 * p_b` the alternating product.  The new audited leaf
`ConnesWeilRH/Dev/C1G8R3LeakageDefectTelescoping.lean` proves the two
projection absorptions for every first positive power:

```text
p_b * T_b^(n+1) = T_b^(n+1)
T_b^(n+1) * p_b = T_b^(n+1).
```

Therefore the static leakage defect is exactly the adjacent power difference
on either side:

```text
(p_b - T_b) * T_b^(n+1) = T_b^(n+1) - T_b^(n+2)
T_b^(n+1) * (p_b - T_b) = T_b^(n+1) - T_b^(n+2).
```

The corresponding applied-vector identity is also audited.  This is a
machine-checked bridge from the normal-form defect to the already available
alternating-power step estimates.

## 2. Boundary

The result is an operator telescoping identity only.  It does not prove that
the selected root times the defect is Hilbert--Schmidt, and it does not make
the conjugated source leakage leg trace class.  The next analytic consumer
must still control the root applied to these step differences (or prove an
equivalent commutator/kernel estimate) on the same basis.  The common-right
finite-Euler leg and the G8 same-owner readback remain open.

## 3. Acceptance

Focused acceptance is `build-logs/1454_leakage_defect_telescoping_try3.log`:
`Build completed successfully (3283 jobs)`, zero `error:` lines, zero
`sorryAx`, and five audited declarations with only
`[propext, Classical.choice, Quot.sound]`.  The unified 16-target R3 batch
`build-logs/1454_r1_unified_batch.log` also passed with
`Build completed successfully (3291 jobs)`, zero `error:` lines, zero
`sorryAx`, and 98 `Quot.sound]` audit terminators.
