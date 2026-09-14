# 1430 — R3 doubled-shift Sonin transport: T1 formal result

**Date:** 2026-09-14
**Status:** GREEN for the closed-subspace transport; projection transport and
trace-class analysis remain open.  No RH claim.

## 1. Result

The opposite translation laws can be combined without asserting a false common
unitary conjugacy.  With `b = log lambda`, define

```text
Rspace(b) = U_(-2*b) Ran(E_1) intersect Ran(Q_1).
```

The new Dev leaf proves the exact closed-subspace identity

```text
map U_b (Rspace(b)) = Ran(E_lambda) intersect Ran(Q_lambda).
```

The formal declaration is
`doubledShiftSoninClosedSubspace_map_eq_source` in
[`C1G8R3DoubledShiftSoninTransport.lean`](../../ConnesWeilRH/Dev/C1G8R3DoubledShiftSoninTransport.lean).

The proof uses only the committed scale laws, the zero-defect Hardy transport,
the global translation group law, and the fixed half-line range criterion.  It
does not use `qw`, detector health, `SourceRH`, or a universal positivity
statement.

## 2. Verification

The paired Audit leaf is
[`C1G8R3DoubledShiftSoninTransportAudit.lean`](../../ConnesWeilRH/Dev/C1G8R3DoubledShiftSoninTransportAudit.lean).

The focused build completed successfully.  The acceptance readback gave:

```text
error:     0
sorryAx:   0
Audit Quot.sound] count: 4
Audit axiom sets: [propext, Classical.choice, Quot.sound]
```

The four audited declarations are the two closed-subspace constructors, the
linear-isometry inverse-translation lemma, and the T1 map identity.

## 3. What was actually proved

The proof explicitly handles the coercion distinction between
`LinearIsometryEquiv` and `ContinuousLinearEquiv`.  The radial component is
transported through

```text
U_(-2*b) Ran(E_1),
```

so membership of `U_(-b) u` is pulled back by `U_(2*b)`.  The group law gives
`U_(2*b) U_(-b) u = U_b u`, exactly matching the radial scale law.  The Fourier
component is transported in the opposite direction and matches the Hardy scale
law directly.

This is a closed-subspace statement.  It is not yet the operator identity

```text
P_lambda = U_b starProjection(Rspace(b)) U_(-b).
```

That projection identity is a short but separate API/uniqueness obligation;
the trace-class estimate is a genuinely separate analytic obligation.

## 4. Remaining R3 obligation

The next target is not a uniform angle estimate assumed by fiat.  A direct
two-projection analysis must control the intersection projection together with
the detector's smoothing.  The proposed next screen is recorded in
[`015_r3_weighted_two_projection_trace_bridge.md`](../map/015_r3_weighted_two_projection_trace_bridge.md).

Current route status:

```text
T1 closed-subspace transport       GREEN / FORMAL
T1 projection transport            OPEN
T2 moving-scale trace estimate     OPEN
T3 basis-compatible trace witness  OPEN
T4 G8 readback reconnection        OPEN
R3                                OPEN
RH                                not claimed
```
