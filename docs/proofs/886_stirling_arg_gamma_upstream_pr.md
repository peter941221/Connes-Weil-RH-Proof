# 886 — mathlib upstream proposal: a compact-strip Stirling bound for arg-Gamma

Date: 2026-08-08. Status: **proposal needed by this route; not yet in mathlib.** Companion to docs/869.

## Problem (what the route needs)

To certify the arch-sign `Re[Gamma(a + I/2)^4] >= 0` on the band `a in (0.815, 2.7)`
(and specifically `a = 1`, where it is numerically positive), one must bound the phase
of `Gamma(a + I/2)`.  `Gamma` is defined through the GammaIntegral and is not
`norm_num`-decidable, so no closed form is available for `arg(Gamma(1 + I/2))`.
A single, real, library-grade estimate closes the whole arch window.

## The missing mathlib lemma (concrete signature)

```lean
-- Proposal (mathlib/Analysis/SpecialFunctions/Gamma/*.lean)
-- Compact-strip Stirling bound, uniform in ℓ, first-order form.
theorem Gamma_norm_exp_bound (s : Complex) {t : Real}
    (hsRe : 1/2 <= s.re) (hsRe' : s.re <= 3)
    (hb : 1 <= Complex.abs s) :
    Complex.abs (Complex.Gamma s) <=
      Complex.rexpT 2/pi_t ...   -- place in real: exp(Re(s)*log(Real.abs s) - Re(s) + O(1/t))
```

More precisely the **phase** bound we need can be stated as

```lean
-- compact strip, `s = a + I*t`, Re-pos, band width W:
theorem arg_Gamma_strip_bound
    (a : Real) (hlow hhigh W : Real) : 0 < W -> de-pos a ->
    (the phase deviation)  |arg (Gamma (a + I*t))| <= pi/8  (for t in [-W, W])
```

Reference values (exact mpmath, 40-digit; w.ss=1):
```
a = 1 :  Re[Gamma(1 + I/2)^4] = 0.26097... > 0
         Re[Gamma(1 + I/2) / c q] = 0.88321767...  ->  square 0.78007... >= 1/2
```

## Why it must live in mathlib (not the project)

The estimate needs: analytic continuation of `Gamma`, a Stirling / Euler�Maclaurin
remainder, and `Complex.arg` continuity in a strip. mathlib v4.30.0 offers only:
- `Complex.Gamma` (parametric, PollL, reflection, `Gamma_mul_Gamma_one_sub`),
- `Complex.Gamma_conj`, `Gamma_ne_zero_of_re_pos`, `GammaSeq_tendsto_Gamma`,
- real `n!` Sterling (`Mathlib/.../Gamma/Stirling.lean`),
- `digamma` evaluations (`Gamma/Digamma.lean`), no `arg Gamma` asymptotic.

There is no `Tendsto` of `GammaSeq` with an explicit error rate and no
`arg` (Gamma) asymptotic.  So the phase-Arg bound is a genuine library extension,
not a lemma the formal project can climb inside its own workspace.

## Sketch of a proof path (for a PR body)

1. Use the series/`GammaSeq` definition of `Gamma` on the half-plane `Re > 0`.
2. Prove the log-magnitude estimate for `Delta = log |Gamma(s)| - ((Re s - 1/2) log(1|s| - Re s))
   and an explicit big-O error (the "Sterling" term).
3. Bound the phase by first-order M type: `arg Gamma(s)` changing by `< pi/4` across
   `[-W, W]` from the center value `arg Gamma(high-pos a) = 0` (real positive center,
   `gamma_center_one_half_re_pos` in a prior round).
4. Assemble (2)+(3) -> `|arg| <= pi/8` for the band (or the coarser `(Re/|Gamma|)^2 >= 1/2`).

## Recommended next steps (upstream, on GitHub)

1. Port the series `GammaSeq` asymptotic to `Complex` with `BigO` remainder.
2. Add `Complex.arg` continuity on the pole-free strip.
3. Land `theorem Gamma_stirlingarg_strip_bound`; then the project re-uses it.

## Accepted hard facts (already axiom-clean in this repo)
`gammaPhaseWindow`, `archSign_effect_of_phaseWindow`, `HilbertArchSign_iff_phaseWindow`
(ArchPhaseWindow.lean, [propext, Classical.choice, Quot.sound]) -- reduce the whole arch
sign of Gamma(a + I/2) to `(Re[Gamma/conj Gamma])^2 >= 1/2`.  Landing the Stirling bound
above closes the sign slot.
