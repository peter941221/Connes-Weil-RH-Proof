# 1429 — R3 SC1: the half-line commutator model passes

**Date:** 2026-09-14
**Evidence class:** PAPER DERIVATION / PROJECT CANDIDATE.
**Consumer:** the healthy-`CompactLog` B5 detector-specific readback
`0 <= C1SameOwnerWeil.qw g`.

This record executes the first falsifier required by
[map 013](../map/013_r3_sonin_detector_commutator_cancellation.md). It does
not prove the actual Sonin commutator estimate and does not claim RH.

## 1. Model

Let `E` be multiplication by the indicator of `[0,infinity)` on `L2(R)` and
let `D_h` be convolution by a compactly supported smooth kernel `h`:

```text
(D_h f)(x) = integral h(x-y) f(y) dy.
```

Relative to `L2(R) = L2((-infinity,0)) plus L2([0,infinity))`, the diagonal
blocks of `[E,D_h]` vanish. For `x >= 0` and `y < 0`, put `u = -y`; the
off-diagonal kernel is

```text
h(x-y) = h(x+u),       x >= 0, u >= 0.
```

The other off-diagonal block has kernel `-h(-(x+u))`. Thus the model reduces
to two Hankel operators with kernels `h(x+u)` and `h(-(x+u))` on the positive
quadrant.

## 2. Smooth-kernel nuclear lemma

### Lemma

If `k` is smooth on the closed quadrant `[0,infinity)^2` and is supported in
`{(x,u) : x+u <= L}` for some finite `L`, then the integral operator

```text
(H_k v)(x) = integral k(x,u) v(u) du,       x >= 0,
```

is trace class.

### Proof mechanism

The function `k` is smooth up to both boundary faces and has compact support.
The smooth extension theorem for a quadrant gives a compactly supported
smooth extension `k_tilde` to `R^2`. Let `T` be the full-line integral
operator with kernel `k_tilde`.

Choose an integer `m > 1`. With `A = 1 - d^2/dx^2 + x^2`, the harmonic
oscillator has discrete eigenvalues growing linearly, so `A^(-m)` is trace
class. Integration by parts gives that

```text
A_x^m A_u^m k_tilde(x,u)
```

is still a compactly supported square-integrable kernel. The corresponding
operator `B = A^m T A^m` is therefore Hilbert--Schmidt, hence bounded. On the
Schwartz core,

```text
T = A^(-m) B A^(-m).
```

Closure gives the same identity on `L2(R)`. Trace-class operators form a two-
sided ideal, so `T` is trace class. Restriction to the positive quadrant and
extension by zero are bounded maps; compressing `T` therefore gives `H_k`
trace class.

This proof also yields a finite-seminorm bound of the form

```text
||H_k||_1 <= C_m * sum_{a+b <= 4m} ||partial_x^a partial_u^b k||_L2,
```

where `C_m` depends only on the chosen harmonic-oscillator factorization and
the support box. The exact value of `C_m` is not needed for the SC1 screen;
the important point is that it is independent of the basis and of any finite
window cutoff.

## 3. SC1 conclusion

Apply the lemma to `k_+(x,u) = h(x+u)` and
`k_-(x,u) = h(-(x+u))`. Both kernels are smooth on the closed quadrant and
supported in a finite triangle whenever `h` is compactly supported. Hence

```text
[E,D_h] is trace class.
```

If `h(-t) = conjugate(h(t))`, the two blocks are adjoints up to the sign in
the commutator, but the trace-class conclusion does not require that symmetry.
The Hermitian case only supplies the expected skew-adjoint block structure.

This is a genuine analytic pass, not a finite-dimensional or numerical
observation. It also shows why the raw half-line crossing itself was never
the likely obstruction: compact support turns the crossing into a compact
corner Hankel kernel, and smoothness upgrades compactness to S1.

## 4. Instantiation for the committed detector

The source API gives the required hypotheses without importing a new sign
assumption:

1. `CompactLogTest.test` is a compactly supported smooth Schwartz function.
2. `convolutionSquare.test` is again compactly supported and smooth, with
   support controlled by `convolutionSquare_support_subset`.
3. `globalConvolutionPositive_eq_convolutionSquare` identifies the positive
   detector with convolution by that square kernel.
4. `convolutionSquare_neg` gives the Hermitian relation
   `h(-t) = conjugate(h(t))`.

Therefore the detector's **half-line commutator model** passes SC1 for every
selected owner. This uses only support and smoothness, not `qw`, detector
health, `SourceRH`, or a universal positivity statement.

## 5. What this does not prove

The actual R3 object is

```text
[sourceSoninProjection lambda, detectorOperator owner].
```

`sourceSoninProjection` is the orthogonal projection onto the intersection of
the radial support and Hardy--Titchmarsh Fourier-support subspaces. It is not
the half-line multiplier `E`; its kernel is not supplied by the model lemma.
Consequently SC1 does **not** imply the actual Sonin commutator is trace class.

The exact remaining problem is now narrower:

```text
half-line boundary        : S1, passed
Hardy-transport boundary  : formal involution/scale identities, no S1 estimate
Sonin interior/prolate    : open
cutoff-to-qw readback     : open
```

Any next proof must either:

- express the actual Sonin commutator as half-line Hankel pieces plus a
  trace-class Hardy-transport correction; or
- prove a direct S1 estimate for the interior/prolate correction using the
  antiresonant source geometry.

## 6. Updated verdict

```text
SC1 half-line kernel falsifier : PASS (paper theorem-shaped derivation)
SC2 Sonin lift                  : OPEN
SC3 signed source remainder     : OPEN
SC4 cutoff/source transport    : OPEN
SC5 G8 readback/RH composition : OPEN
```

The candidate survives its first hard gate. This raises its status from
`PROMISING-BUT-UNSCREENED` to `SC1-PASS / SC2-OPEN`; it does not raise the
status of R3 or of RH.
