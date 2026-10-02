# 2447 - Route A interval algebra build boundary

Date: 2026-10-02.

The formal Lake build was run against the current Lean 4.30 and Mathlib
environment. The Route A interval algebra module does not currently compile.
The failure is concentrated in the proof of real interval multiplication and
then propagates to complex rectangle multiplication and finite-sum readback.

The root issue is semantic: mem_uIcc is an unordered-interval membership
statement and returns the two possible endpoint orientations. The existing
proof treats the returned pair as if the endpoints were always ordered. The
same module also lacks the Complex big-operator import needed for real and
imaginary parts of finite sums, and its scalar-complex statement relies on an
unavailable real scalar action in the current environment.

The source was restored unchanged after the diagnostic build; no partial fix
is retained. This is a blocking prerequisite for Lean numeric endpoint
instantiation, not a failure of the 2445 or 2446 numerical controls.

Evidence: the Lake build of
ConnesWeilRH.Dev.C1RouteAIntervalAlgebra reached 912/912 and reported errors
at the interval multiplication proof, complex scaling, and finite-sum
readback. No producer GO or RH conclusion follows.
