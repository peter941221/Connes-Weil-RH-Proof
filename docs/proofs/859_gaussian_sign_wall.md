# 859 - Line-1 verdict: Gaussian Mellin diverges at the critical line; the sign slot is ill-defined / non-uniform

Date: 2026-08-07 . Status: numeric-model verdict on the sign-slot floor; no RH claim, no Lean producer claimed here.

Follows 858/858c. 858c reduced the whole faithful half-density sign slot to the single real
statement `Re[(M g (i/2))^4] >= 0` for a real-valued test `g`. "一号线路" (Line 1) was to make
that concrete by picking a transparent test (Gaussian) whose Mellin one "knows". This round
attacks that line and finds the sign slot is not well-defined at most concrete tests and, where
defined, it is not uniform: the natural smooth non-vanishing tests have a DIVERGENT Mellin at
s = i/2 (kernel t^(-1+i/2) not locally integrable at 0), and the tests that ARE well-defined
(vanishing at 0) give BOTH signs.

This is an A0-class "empty / zero-only satisfiability" pattern in concrete clothing, not a bare
analytic-hardness issue. The Gaussian shortcut to a *uniform* sign is closed; the sign is a
genuinely model-dependent functional, not a single number.

## 1. Why the critical-line Mellin is generically not well-defined at i/2

The repo Mellin (MellinProductCarrier.mellin / MellinTransform.mellin) is

    mellin f s = ∫ t in Ioi 0, (t : C)^(s-1) • f t.

At s = i/2 (critical line) the weight is t^(-1+i/2), modulus t^(-1) — a t^(-1) blowup right at
0. So the integral is finite only when f vanishes fast enough at 0 (like t^a, a>0). Any natural
test with f(0) != 0 (Gaussian e^-t^2, exponential e^-t, sech) makes the integrand t^(-1) f(t)
non-integrable at 0. The Mellin DIVERGES there.

## 2. Divergence numerically visible

Integrating t^(i/2-1) f(t) over [eps,∞) and shrinking eps→0, partial integrals do NOT stabilize:

    test        eps=1e-2          eps=1e-5           eps=1e-9
    e^(-t^2)    +1.226 - 3.220 i  -1.267 - 0.155 i   -1.873 - 3.068 i
    e^(-t)      +1.080 - 2.943 i  -1.405 + 0.126 i   -2.011 - 2.788 i
    sech(pi t)  +0.654 - 3.005 i  -1.839 + 0.060 i   -2.445 - 2.853 i

No stabilization: the cutoff changes the value wholesale, so M g (i/2) is not well-defined.

## 3. Where it IS defined, the sign is not uniform

Restrict to tests vanishing at 0 (f = t^a e^(-t)); Mellin converges and Re[w^4], w = M f (i/2),
splits sign as a moves:

    f             Re[w^4]
    t^0.4 e^(-t)  -1.9853  (negative)
    t^0.55 e^(-t) -1.2107  (negative)
    t^0.9  e^(-t) +0.1563  (positive)
    t^1.0  e^(-t) +0.2610  (positive)

So no uniform sign even among well-defined tests. Universal Re[(M g i/2)^4] >= 0 is false;
a positive instance needs a special vanishing-at-0 band test, and proving it needs a concrete
integral bound, not algebra.

## 4. What this says about the route

- The 858c reduction itself is fine (it is guarded by `Integrable (logWeight (i/2) g)`, which
  is exactly the well-defined-ness condition above). Not the bug.
- The bug: the concrete model has no non-vanishing real test for which (M g i/2) is defined,
  and the defined band splits sign. Treating "Re[w^4] >= 0" with the Gaussian is not a
  Lean-proving gap but a model-domain wall: the quantity is ill-defined there.
- This is the L^1-near-0 / band-vanishing boundary that Proof-844 / AGENTS §11 (empty,
  zero-only producer) warns about. A "Gaussian shortcut" cannot exist.

## 5. Honest surviving step (no fake closure)

- Encode that the domain of definition of `mellin g (i/2)` is precisely
  `Integrable (logWeight (i/2) g)` — a real, nontrivial boundary-carrier condition. That is
  Def-able and Lean-statable and IS the real constraint (matches A0).
- For the sign, the only non-empty path is pick a vanishing-at-0 band test with Re[w^4] > 0
  AND prove the concrete integral bound in Lean (real integral of t^(-1+i/2)f(t) over the
  halfline). That is heavy, separate analytic work, not a one-line closure.

"一号" therefore cannot nail RH; it can (a) make the well-formedness boundary explicit and
(b) open a concrete band estimate to try. Both recorded here.

Repro (read-only numeric): mpmath quad [eps,∞] of t^(i/2-1)·exp(-t^2) etc.; see tables above.

## 6. Concrete forward: the band test reduces to a clean Gamma-phase inequality

The well-defined band test `f(t) = t^a e^(-t)` (a > 0) has EXACT closed Mellin:

    M f (i/2) = ∫ t^(i/2-1) t^a e^(-t) dt = ∫ t^(a+i/2-1) e^(-t) dt = Gamma(a + i/2).

So the sign `Re[(M f i/2)^4] >= 0` is exactly `Re[(Gamma(a + i/2))^4] >= 0` for real a > 0.
This is the single concrete Gamma-phase inequality the band route needs. Numerically it is
NOT uniform, but has two clean positivity regions (mpmath, 40 digits):

    a       Re[Gamma(a+i/2)]^4
    0.10    +6.15   (positive)
    0.20    +2.27   (positive)
    0.40    -1.99   (negative)
    0.60    -0.88   (negative)
    0.85    ~0      (crossing)
    0.90    +0.16   (positive)
    1.00    +0.26   (positive)
    1.20    +0.35   (positive)
    2.00    +0.46   (positive)

So the cleanest, provable-in-principle target is the LARGE-band edge:

    Conjecture: exists a0 > 0, forall a >= a0, Re[(Gamma(a + i/2))^4] > 0.

Heuristic: for large real a, Gamma(a+i/2) tends to a real-positive asymptotic, so its
argument → 0 and the 4th power phase stays in (-pi/2, +pi/2). A rigorous Lean proof needs a
Gamma lower/asymptotic bound (not in mathlib today), so this is a real analysis subgoal,
not a current Lean lemma. It is the honest "next stone" if the route is pursued: it no longer
depends on a choice of concrete test gap, only on one analytic estimate on the Gamma function.

[added 2026-08-07; same verdict — no closure, but the wall is now a single concrete
Gamma-phase statement]
