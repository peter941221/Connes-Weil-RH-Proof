# 904 - Re[Gamma(1+i/2)^4]>=0: the sector-reduction sub-lemma (Lean in progress)

Date: 2026-08-08. Status: analytic+numeric DONE, Lean polar/DeMoivre sub-lemma IN PROGRESS.
After docs/903 closed the bridge `S = tsum S2 + atan(1/2)`, the arch-phase real-nonneg gate
reduces to ONE generic Lean lemma.  This file records exactly that lemma and what mathlib
offers, so the next session can close it quickly (no re-probing).

## Goal

Closed facts (docs/890):
- `PhaseGateSandwich.D := S - gamma/2 - atan(1/2)`;  `D_abs_lt_pi_eighth : |D| < pi/8`
- bridge `SSeriesSandwich.S_eq_S2_add_atan_half : S = tsum S2 + atan (1/2)`
- Euler identity (open analytic, docs/902/903): `arg Gamma(1+i/2) = -gamma/2 + tsum S2`

Then `arg Gamma(1+i/2) = D` and `|arg Gamma(1+i/2)| < pi/8`.  What is left to make the
arch-phase leaf is the generic sector lemma

    lemma re_pow4_nonneg_of_abs_arg_lt_pi_eighth {z : C} (hz : z != 0)
        (h : |z.arg| < pi/8) : 0 <= (z^4).re

numerically TRUE: Re[Gamma(1+i/2)^4] = +0.2609730354..., |arg|=0.24405..,
|4*arg Gamma(1+i/2)|=0.9762.. < pi/2.

## How to prove it (verified preamble)

- `Complex.norm_mul_exp_arg_mul_I z : z = ||z|| * exp (z.arg * I)`
- `rw [this.symm, mul_pow]`; `norm_cast` -> `(((||z||^4 : C) * exp (z.arg*I)^4)).real = ...`
- `rw [<- Complex.exp_nat_mul]` (i.e. `(exp e)^4 = exp (4*e)`), then `ring_nf`.
- The single remaining lens: real part of `(r : C) * exp ((4a)*I)` = `r * Real.cos (4a)`.
  Exact mathlib lemma TBD (candidates: `Complex.exp_mul_I`, Euler/Moivre in the Complex
  trig package, `Complex.ofReal_re`, `Complex.ofReal_cos`).  Rewrite alternatives:
  apply `Complex.norm_mul_cos_arg (z^4)`: `||z^4||*Real.cos ((z^4).arg) = (z^4).real`,
  then `||z^4||=||z||^4` and `Real.cos((z^4).arg)=Real.cos(4*z.arg)` (mod-2pi, no wrap
  because |4*arg|<pi/2<pi).

## Guards

- The assertion is TRUE (mpmath 60 digits: Re=+0.26097 > 0).
- No sorry/axiom inserted; the working tree keeps only the closed bridge (903).
- RH is not claimed; this closes only the arch-phase real-nonneg leaf.
