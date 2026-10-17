# 2772 - Representative phase exponential-tail bound

Status: Lean-verified analytic remainder input.

For the representative cell phase interval, the normalized lower-phase argument `y = -P.lo / 4` is proved to lie in `[0,1]`, and the existing Taylor remainder theorem yields `expTail y <= y`.

Verification: Linux-native audit build 3664/3664, zero errors; standard axiom trio only.

This is an analytic input to endpoint box propagation, not yet a child endpoint max pin.
