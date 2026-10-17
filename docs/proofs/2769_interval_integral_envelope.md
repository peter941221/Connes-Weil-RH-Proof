# 2769 - Generic real interval integral envelope

Status: Lean-verified reusable enclosure lemma.

`intervalIntegral_norm_le_endpointAbsMax2769` proves: if a continuous real function maps every point of `[a,b]` into a `RealInterval2429` box, then its norm integral is bounded by `(b-a) * max(abs lo, abs hi)`.

Verification: Linux-native audit build 2625/2625, zero errors; standard axiom trio only.

This helper is intended for the closed left/right D4/D7 child consumers.
