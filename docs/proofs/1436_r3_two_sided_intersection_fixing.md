# 1436 — R3 two-sided intersection fixing

Date: 2026-09-14.

Status: FORMAL / GREEN. This is a lower-data R3 reduction, not a trace estimate, same-owner readback, positivity theorem, or RH result.

Consumer: the healthy-`CompactLog`, B5-shaped conclusion `0 <= C1SameOwnerWeil.qw g` for the tower-selected detector.

## Result

Let `T_b` be the doubled-shift alternating product and `r_b` the orthogonal projection onto its Sonin intersection. Record 1435 had formally proved:

```text
T_b r_b = r_b.
```

The new theorem `intersectionProjection_comp_doubledShiftAlternatingProduct` proves the opposite identity:

```text
r_b T_b = r_b.
```

It is the adjoint of the existing right-fixing identity. The proof uses the already formal self-adjointness of `T_b` and star-projection property of `r_b`; it introduces no spectral gap, sign premise, detector-health field, `SourceRH`, universal gate, or external dictionary.

Consequently the public power-limit bridge now requires only its genuinely analytic hypothesis:

```text
exists rho < 1, ||T_b - r_b|| < rho.
```

The formerly explicit `r_b T_b = r_b` argument is discharged internally. This does not make the gap true; if it fails, the angle-free weighted endpoint estimate of map 015 remains the required route.

## Acceptance

The grouped batch `build-logs/016_r3_endpoint_batch.log` built the finite stage, strong-to-Hilbert--Schmidt transfer, power bridge, and their paired audits:

```text
Build completed successfully (3182 jobs)
error: 0
sorryAx: 0
Quot.sound] audit terminators: 26
```

Every printed declaration, including the new theorem, has only `[propext, Classical.choice, Quot.sound]`.

## Boundary

The remaining R3 content is unchanged: a detector-weighted endpoint estimate or another source-owned trace-ideal theorem, a same-global-basis witness, and the G8 cutoff/source readback. RH is not claimed.
