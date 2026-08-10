# 939 - finite-S sign: algebraic cone tail closed (A1/A2), analytic Gamma bound open

Date: 2026-08-10 (rev 2). Status: Step-3 (finite-S Weil sign) - algebraic tail A1/A2/A3 DONE, axiom-clean ([propext, Classical.choice, Quot.sound], 0 sorry); analytic Gamma-phase term OPEN. RH NOT claimed.

## 1. What is now closed (axiom-clean)

`Dev/Finite3SignReduction.lean` (WSL green 1830 jobs; #print axioms [propext,
Classical.choice, Quot.sound] for all four, 0 sorry):

  * `re_fourth_poly`: Re[w^4] = (Re w)^4 - 6(Re w)^2(Im w)^2 + (Im w)^4.
  * `sqrt2m1_sq`:    (sqrt 2 - 1)^2 = 3 - 2 sqrt 2.
  * `cone_nonneg`:   1 - 6u + u^2 >= 0 on 0 <= u <= (sqrt2-1)^2.
  * `reFourth_nonneg_of_cone`: (0 < Re w) + (|Im w| <= (sqrt2-1) Re w) ==> 0 <= Re (w^4).

Together they give the algebraic statement

    (0 < Re w) and (|Im w| <= (sqrt2 - 1) Re w)  ==>  Re w^4 >= 0,

i.e. the fourth-power sign is nonnegative on the |arg| <= pi/4 cone - the
algebraic tail every finite-S sign closure must apply (no Complex.Gamma, no
Complex.arg, no Stirling needed here).

## 2. The remaining open (the actual analytic wall)

For the band `w = Complex.Gamma(a + I/2)` the finite-S sign reduces (with the
lemma above) to the REAL analytic bound

    |Im Gamma(a + I/2)| <= (sqrt 2 - 1) * Re Gamma(a + I/2)   on a band,

or, with the phase, |arg Gamma(a+I/2)| <= pi/4.  That is the Gamma/Stirling-type
content (docs/869/888) that mathlib does not provide; it is the live Step-3
target.  The naive "arg(Entity) -> 0" band was already refuted (docs/937): the
sign is not eventually positive, so one must pick a genuinely-positive band and
prove the cone on it.

## 3. Route note
- The algebraic tail (A1+A2) is now independent of Gamma and reusable by ANY
  closure of the sign.
- Next: supply the real analytic Gamma argument/Im bound for a selected band;
  that is self-contained new analysis (Stirling/Weierstrass log-Gamma on a strip),
  which remains open.
