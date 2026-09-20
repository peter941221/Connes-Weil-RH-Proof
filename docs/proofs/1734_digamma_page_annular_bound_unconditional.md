# 1734 — The digamma page: the S3 uniform annular bound is unconditional; Door 1's mass face is closed

Date: 2026-09-20. Classification: PAPER PROOF (complete and UNCONDITIONAL).
This record discharges the single analytic remainder ("hypothesis (M)") of
record 1733, so the uniform annular kernel-diagonal bound `hdiag` consumed by
`sourceCompressedRoot_squareSum_of_kernelDiagonal_lintegral_bound`
(`ConnesWeilRH/Dev/C1G8R3AnnularKernelDiagonalMass.lean:97-99`) is now supplied
by a complete derivation from committed definitions. Door 1's mass face is
CLOSED on paper. RH is not claimed: the gate's sign face lives on the map-047
two-premise exit (records 1694/1695), untouched here.

## 0. The simplification that makes this a two-line page

Record 1733 §5 priced the remainder as the classical digamma growth bounds
`Re psi(z) = O(log|z|)`, `psi'(z) = O(1/|z|)` (DLMF 5.15.1). That is more
than is needed. The committed phase is only ever evaluated on the VERTICAL
LINE `w = 1/4 + pi i xi`, and on a vertical line every digamma series bound
collapses to a REAL sum at `sigma = 1/4`:

```text
  the argument of every series term depends on w only through Re w.
```

So no Stirling machine is required: the elementary reciprocal series gives
LINEAR growth for psi and a UNIFORM CONSTANT for psi', and linear growth is
already sufficient because the other factor `Fh` is Schwartz — it decays
faster than any inverse polynomial. The "one classical moment" of 1733's
title is hence a two-line series estimate.

## 1. Committed inputs (all verified in source this session)

* `h` = the committed Schwartz test
  (`owner.sourceTest.involution.test : SchwartzMap R C`,
  `GlobalLogConvolution.lean:43`); `k_0 = conj h(-.)` is therefore Schwartz.
* The scattering phase (record 1683, FD-verified 1e-13, and re-derived
  term-by-term below): with
  `m(-xi) = G_R(1/2 + 2 pi i xi)/G_R(1/2 - 2 pi i xi)`,
  `G_R(z) = pi^{-z/2} Gamma(z/2)` (1626 pin), and the continuous argument
  `gamma = Im log Theta`, `Theta(xi) = e^{4 pi i (log lambda) xi} m(-xi)`:

```text
  gamma'(xi) = 4 pi log lambda - 2 pi log pi
               + 2 pi Re psi(1/4 + pi i xi),
```

  where `psi` is the complex digamma function. (Re-derivation:
  `d/dz log G_R(z) = -(1/2) log pi + (1/2) psi(z/2)`; differentiate
  `log m(-xi) = log G_R(1/2+2 pi i xi) - log G_R(1/2-2 pi i xi)`, use
  `psi(conj z) = conj psi(z)`, divide the pure-imaginary result by `i`. The
  two `log pi` prefactors do NOT cancel because the argument enters the
  Gamma at half the argument of `G_R`.)
* The in-repo formal bridge for the digamma series already exists:
  `Complex.digamma` is defined in this Mathlib (v4.30) and the repo proves
  the reciprocal-series identity
  (`ConnesWeilRH/Dev/C1XiCenterTwoGamma.lean:486-490`,
  `halfAnchorGaussReciprocalSeries_eq_digamma_sub_half`), so the series
  manipulated below has a formal anchor for later wiring.

## 2. Lemma A/B/C: three elementary digamma bounds on the line

LEMMA A (absolute convergence on the line). For `Re w = 1/4 >= 0`,

```text
  psi(w) = -gamma_E + sum_{n>=0} (1/(n+1) - 1/(n+w))
```

with the series ABSOLUTELY convergent, since

```text
  |1/(n+1) - 1/(n+w)| = |w-1| / ((n+1)|n+w|)
                      <= |w-1| / ((n+1)(n+1/4)),
```

using `|n+w| >= Re(n+w) = n+1/4`.

LEMMA B (linear growth). With `|n+1/4| >= (n+1)/4`,

```text
  |1/(n+1) - 1/(n+w)| <= 4|w-1|/(n+1)^2,
  |psi(w) + gamma_E|  <= 4 (pi^2/6) |w-1| = (2 pi^2/3) |w-1|.
```

On the line `w = 1/4 + pi i xi`: `|w-1| <= 3/4 + pi|xi|`, so

```text
  |psi(1/4 + pi i xi)| <= gamma_E + (2 pi^2/3)(3/4 + pi|xi|)
                       <= 4.24 + 15.3 |xi|.
```

LEMMA C (uniform first-derivative bound). Termwise differentiation is
legitimate on the half-plane `Re w >= 1/4` by the Weierstrass M-test
(`sum_n (n+1/4)^{-2} < infinity` uniformly there), giving the classical

```text
  psi'(w) = sum_{n>=0} 1/(n+w)^2,
  |psi'(w)| <= sum_{n>=0} 1/(n+1/4)^2 <= 16 + integral_0^inf (x+1/4)^{-2} dx
            = 16 + 4 = 20        (uniform on the whole line),
```

by the integral comparison for the decreasing real series.

## 3. Polynomial derivative bounds of the symbol; theta is W^{2,1} cap C_0

From Lemmas B/C and the committed gamma' formula:

```text
  gamma''(xi) = d/dxi [2 pi Re psi(1/4 + pi i xi)]
              = 2 pi^2 Re(i psi') = -2 pi^2 Im psi'(1/4 + pi i xi),
  |gamma''(xi)| <= 2 pi^2 * 20 = 40 pi^2                    (CONSTANT),
  |gamma'(xi)|  <= 4 pi|log lambda| + 2 pi log pi
                   + 2 pi (gamma_E + (2 pi^2/3)(3/4 + pi|xi|))
                <= C_lambda (1 + |xi|)                      (LINEAR),
```

with `C_lambda = 4 pi|log lambda| + 2 pi log pi + 2 pi gamma_E
+ (4 pi^3/3)(3/4 + pi)` a finite committed constant (lambda is a fixed
Sonin scale).

`psi` is holomorphic on `Re w > 0`, so `gamma`, `gamma'`, `gamma''` are
continuous on the line; `m = e^{i gamma}` is C^2 with

```text
  m'  = i gamma' m,                       |m'|  = |gamma'|,
  m'' = (i gamma'' - (gamma')^2) m,       |m''| <= 40 pi^2 + gamma'(xi)^2
                                              <= C'_lambda (1 + xi^2).
```

Now `theta(xi) = m(xi) * conj(Fh)(xi)`. Both factors are C^2, `theta` is
continuous with `|theta| <= |Fh| -> 0` (theta in C_0), and

```text
  theta'' = m'' conj(Fh) + 2 m' conj(Fh)' + m conj(Fh)'',
  ||theta''||_1 <= integral C'_lambda (1+xi^2) |Fh(xi)| dxi
                 + 2 integral C_lambda (1+|xi|) |Fh'(xi)| dxi
                 + integral |Fh''(xi)| dxi  <  infinity,
```

because `Fh`, `Fh'`, `Fh''` are Schwartz (every polynomial weight is
integrable against them). Likewise `theta' in L^1` and
`|theta'(xi)| <= C_lambda(1+|xi|)|Fh(xi)| + |Fh'(xi)| -> 0`. Hence

```text
  theta in W^{2,1}(R) cap C_0  with  theta' in C_0,
```

which is exactly the hypothesis class of the two integrations by parts.

## 4. Two IBPs and the one moment (with a corrected constant)

`v = F^{-1} theta` and `theta in L^1`, so `v` is the integral
`v(s) = integral theta(xi) e^{-2 pi i xi s} dxi`. Two integrations by parts
on `[-R, R]`, the boundary terms vanishing because `theta, theta' in C_0`,
then `R -> infinity` by dominated convergence:

```text
  |v(s)| <= ||theta''||_1 / (2 pi s)^2 = ||theta''||_1 / (4 pi^2 s^2).
```

Therefore, for `X > 0`,

```text
  integral_X^inf s |v(s)|^2 ds <= ||theta''||_1^2/(16 pi^4) integral_X^inf s^{-3} ds
                               = ||theta''||_1^2 / (32 pi^4 X^2).
```

CORRECTION to record 1733 section 5: the constant printed there was
`||theta''||_1^2/(8 pi^4 X^2)`; the correct value is
`1/(32 pi^4 X^2)` (the (2 pi s)^2 square is 16 pi^4 s^4 and
`integral_X^inf s^{-3} ds = 1/(2 X^2)`). The closure is unaffected — any
finite constant decays.

## 5. Assembly: the explicit uniform bound B(N) -> 0

By 1733 sections 3-4 (kernel readback, Bessel, cosine rule, translation
reversal `Ht T_t = T_{-t} Ht` — the last already formal, consumed by
`C1G8R3HardyTranslatedTail.lean:251-278`), the annular diagonal is priced by
the two fixed tails with

```text
  B(N) = integral_{a+N}^inf s (|k_0(s)|^2 + |v(s)|^2) ds,   a = log lambda,
```

n-independent. `k_0` is Schwartz, so with `|k_0(s)| <= C_k (1+|s|)^{-3}`
(some `C_k < infinity`, from the committed test's seminorms) and `X = a+N >= 1`:

```text
  integral_X^inf s |k_0|^2 <= C_k^2 integral_X^inf s^{-5} ds = C_k^2/(4 X^4),
  integral_X^inf s |v|^2   <= ||theta''||_1^2/(32 pi^4 X^2)          (section 4),

  ==>  B(N) <= C_k^2/(4 (a+N)^4) + ||theta''||_1^2/(32 pi^4 (a+N)^2)  -->  0.
```

Take `N_0 >= max(1 - a, support radius)` and `B := B(N_0) < infinity`.
Since `B(N)` is n-independent, `B` prices EVERY annulus
`n >= N_0` at once — precisely the uniform `hdiag` shape
`forall n, N <= n -> lintegral ... <= ofReal B` of the committed consumer
(`C1G8R3AnnularKernelDiagonalMass.lean:97-99`).

## 6. Consequence: Door 1's mass face is closed (unconditionally)

Chaining the committed, machine-checked interfaces:

```text
  hdiag (this record + 1733 sections 3-4, unconditional)
    --> survivor-core square-sum   (1723 consumer, formal)
    --> endpoint-gate mass face    (1680 iff chain, formal)
```

The S3 producer is closed on paper. What is NOT closed here, unchanged from
1733: the gate's sign face (`heq` sign + index), relocated to the map-047
two-premise exit (`healthy_spectral_nonneg_sourceRH_of_yoshida_detector`).
`0 <= qw` is not touched and RH is not claimed.

## 7. Formal status and remaining work

* Formal skeleton LANDED (1733 wave, `cc55855a`):
  `norm_starProjection_le_of_submodule_le`,
  `tsum_norm_inner_sq_eq_starProjection_normSq`,
  `annular_lintegral_le_of_pointwise` — standard axioms only.
* Formal decay leaf LANDED (this wave, `C1G8R3AnnularTailDecay.lean`): the
  abstract weighted-tail bounds of sections 4-5 —
  `lintegral_sq_moment_le_of_quadratic_decay` (the `1/(2X^2)` moment),
  `lintegral_sq_tail_le_of_cubic_decay` (Schwartz-type `s^{-3}` tail), and
  `annular_weighted_tail_tendsto_zero` (B(N) -> 0) — paired Audit, standard
  axioms only (`[propext, Classical.choice, Quot.sound]`; build log
  `build-logs/taildecay-round6.log`, 2700 jobs, zero errors).
* Still owed for the FULL formal wiring (unchanged): the kernel readback
  `(C u)(t) = <u, k_t>` in L2 (density argument), the translation-tail
  integral identities instantiating the wing integrals, the theta-W^{2,1}
  estimate in Lean (Lemmas A/B/C are formally anchored in-repo but the
  growth bounds are not yet stated), and the 1723-consumer wiring.
* No numerical claim; no sorry; RH not claimed.
