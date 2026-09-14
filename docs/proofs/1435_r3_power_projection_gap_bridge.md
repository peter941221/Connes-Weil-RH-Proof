# 1435 — R3 power-to-projection gap bridge

## Status

This record is a formal lower-data brick, not an R3 or RH result. It turns
“alternating projections converge” into a precise conditional operator theorem
and attaches that theorem to the actual doubled-shift Sonin intersection.

## Formal content

`C1G8R3PowerProjectionBridge.lean` proves:

1. If `T P = P`, every power of `T` acts as the identity on the range of `P`.
2. If also `P T = P` and `P^2 = P`, then

   ```text
   T^(n+1) - P = (T - P)^(n+1).
   ```

3. If `||T-P|| < rho < 1`, then `T^(n+1)` tends to `P` in operator norm.
4. For the doubled-shift Sonin space, the intersection projection is defined
   and `T_b r_b = r_b` is formally proved from the committed fixed-vector
   theorem.

The paired audit prints the axioms of every declaration. The intended
consumer is the detector-column Hilbert–Schmidt transfer already landed in
1434, followed by the signed G8 same-owner readback.

## Exact remaining obligation

The missing input is not silently assumed:

```text
||p_b q_1 p_b - r_b|| < 1
and
r_b (p_b q_1 p_b) = r_b.
```

If a genuine moving-scale gap cannot hold, this bridge localizes the failure
and forces the next proof to use an angle-free weighted spectral estimate. In
either case, the route remains below the sign gate and uses no RH premise.

## Acceptance

Acceptance is the grouped 1435 build log and the paired audit: zero `error:`
lines, zero `sorryAx`, and standard axioms only. The analytic gap and the
trace/readback obligations remain open after this brick.
