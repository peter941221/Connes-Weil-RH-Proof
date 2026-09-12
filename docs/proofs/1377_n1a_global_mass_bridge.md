# 1377 — N1a: the global mass bridge lemma (paper beat)

Date: 2026-09-13. Consumes [1376](1376_n0p_closure_and_n1_recon.md) §2
(recon: pointwise dead, mass form deliverable), [1371]
(1371_hbridge_sampling_residual_and_scale_paper.md) convention block
(:210-229), and the register definitions cited in §1.
Evidence class: PAPER ONLY. Every constant displayed; no digits; no Lean
build in this record. RH NOT claimed.

## 1. Setup and conventions

Register transform. For a compactly supported smooth test `g`, the
selected positive-variable Mellin transform is the bilateral Laplace
evaluation of its compact log pullback, with POSITIVE character
`e^{+s x}`:

```text
G(z) := laplaceAt g z = Integral[x: Real] exp(z*x) * g(x).
```

Source: `ConnesWeilRH/Source/CC20YoshidaConvolution.lean:35-56`
(`exponentialWeight` multiplies by `Complex.exp (s * x)` per
`exponentialWeight_apply` at :48-52; `laplaceAt` integrates the weighted
test at :55-56). The positive-character/angular-frequency Plancherel
convention (transform-side factor `2*pi`) is fixed by [1371] :210-229;
the identity used below,

```text
Integral[t: Real] |G(i*t)|^2 dt = 2*pi*||g||_2^2,          (P0)
```

is the `d = 0` instance of the same cross-Plancherel machinery (weights
`e^(+dx)`, `e^(-dx)` both replaced by `1` in [1371] R6 :210-229).

Window. The F3 producer delivers detectors supported in the
`(n+1)`-window

```text
supp g  subset  ( a_n , b_n ),
a_n := (n+1)*baseLower + lower,   b_n := (n+1)*baseUpper + upper,
```

with `baseLower < 0 < baseUpper` and `lower < 0 < upper`
(`ConnesWeilRH/Dev/C1SelectedSquareHeightTail.lean:968-979`). The window
is NOT symmetric in general. Write

```text
m := (a_n + b_n)/2        (window center),
W := b_n - a_n            (window width).
```

Under the window hypotheses alone the sign of `m` is undetermined; the
symmetric normalization `(a, b) = (-R, R)` used in [1376] section 2b is
the special case `m = 0, W = 2R`.

## 2. Lemma A (point-evaluation bound, general window)

```text
Lemma A.  g smooth, compactly supported in (a, b), b > a;  d > 0;
t0 in Real.  Then

  |G(d + i*t0)|^2
      <=  e^(2*d*m) * sinh(d*W)/d * ||g||_2^2
      =   ( e^(2*d*b) - e^(2*d*a) ) / (2*d) * ||g||_2^2.
```

Proof. Cauchy–Schwarz pairs the UNWEIGHTED `|g|^2` against the modulus
squared of the character (this pairing is what makes the constant an
exact antiderivative rather than a slack bound):

```text
|G(d + i*t0)|^2
  = | Integral[a..b] g(x) * exp((d + i*t0)*x) dx |^2
  <= ( Integral[a..b] |g(x)|^2 dx ) * ( Integral[a..b] e^(2dx) dx )
  <= ||g||_2^2 * ( e^(2db) - e^(2da) ) / (2*d).
```

The center/width form follows from

```text
e^(2db) - e^(2da) = e^(d(a+b)) * ( e^(d(b-a)) - e^(-d(b-a)) )
                  = 2 * e^(2dm) * sinh(d*W).
```

Symmetric special case `(a, b) = (-R, R)`: `m = 0, W = 2R`, giving
`|G(d + i*t0)|^2 <= sinh(2dR)/d * ||g||^2` — the constant announced in
[1376] section 2b. Note the naive pairing `2R * e^(2dR) * ||g||^2` is
strictly worse; the exact antiderivative removes both the width slack
and the ceiling exponent simultaneously.

## 3. Lemma A-prime (sharpness: the constant is an operator norm)

```text
Lemma A'.  For d > 0 and t0 in Real,

  sup { |G(d + i*t0)|^2 / ||g||_2^2 :
        g in L^2(a, b), g != 0 }
      =  e^(2dm) * sinh(d*W)/d,

  and the supremum over the ADMISSIBLE class (smooth g, compactly
  supported inside (a, b)) has the same value.
```

Proof, upper half: Lemma A. Lower half: the extremal direction is the
conjugate of the kernel `v(x) := e^((d - i*t0)*x)`. For
`g = c * conj(v) * 1_(a,b)` (in `L^2`),

```text
G(d + i*t0) = c * Integral[a..b] e^(2dx) dx,
||g||_2^2   = |c|^2 * Integral[a..b] e^(2dx) dx,
```

so the ratio equals `Integral[a..b] e^(2dx) dx = e^(2dm) sinh(dW)/d`
exactly. For the admissible class, take `g_eps = eta_eps * conj(v)` with
`eta_eps` in `C_c^oo((a,b))`, `0 <= eta_eps <= 1`, `eta_eps -> 1`
pointwise (smooth taper of width `eps` at the ends); dominated
convergence gives `||g_eps||^2 -> Integral e^(2dx)` and
`|G_eps(d + i*t0)|^2 -> (Integral e^(2dx))^2`, so the ratio converges to
the same constant from below. QED.

Consequence (load-bearing). `e^(2dm) sinh(dW)/d` is the operator norm of
the point-evaluation functional `g -> G(d + i*t0)` on `L^2` of the
window. Therefore NO argument that uses only the support window can
improve the global constant — not by subharmonic methods, not by
re-pairing, not by monotonicity. Every future gain must come from
exactly one of:

```text
(i)  band information   — localize the line mass near t0 (N1b kernel),
(ii) construction input — the spline subfamily's evaluation norm may be
                          strictly smaller than the L^2-window norm;
                          how much smaller is OPEN and is a real lever.
```

This converts "improve the constant" from a goal into an impossibility
statement on the global form, and it prices the two remaining doors.

## 4. Corollary B (the mass form S5 consumes)

Joining Lemma A with (P0):

```text
Corollary B.  Under the hypotheses of Lemma A,

  |G(d + i*t0)|^2
      <=  C_bridge(d; a, b) * Integral[t] |G(i*t)|^2 dt,
  C_bridge(d; a, b) := e^(2dm) * sinh(d*W) / (2*pi*d).
```

Properties:

```text
d -> 0+ :  sinh(dW)/d -> W,  e^(2dm) -> 1,
           C_bridge -> W / (2*pi).
```

The limit is exactly the sigma-line evaluation constant for a window of
width `W` (`|G(i*t0)|^2 <= W * ||g||^2 = (W/(2*pi)) * Integral|G(i t)|^2`
by Cauchy–Schwarz and (P0)): the two ends of the vertical chain agree at
`d = 0`, as recorded in [1376] section 2b. For the symmetric window the
limit is `R/pi`.

Two honest notes the general form adds over [1376]:

```text
(a) center factor:  C_bridge carries e^(2*d*m).  Under the F3 window
    hypotheses the sign of m is undetermined; m > 0 is a real cost,
    m < 0 a bonus.  Window CENTERING is a design lever available to the
    construction (N1b/N1c), not a fixed penalty.
(b) rho_b dissolution: Corollary B holds with NO bridge coefficient at
    all — it is universal in the sense of [1376] section 2b.  The 1372
    S5 MODEL question "which fixed rho_b > 0 works" is answered
    vacuously: every positive-coefficient request is dominated.
```

The MODEL-quadratic comparison table (`e^(2d(1+(n+1)R))` vs the linear
constant) stays in [1376] section 2b and remains MODEL-lane material.

## 5. The N1c interface (what Lemma A cannot do)

1. Pointwise form impossible — [1376] section 2a (damping reweights
   phase; no pointwise inequality between Fourier values at a fixed
   frequency).
2. Global constant unimprovable — Lemma A-prime. Gains only through
   band localization (N1b) or subfamily restriction (open spline
   evaluation norm).
3. Norm coupling — Lemma A controls the off-line value THROUGH
   `||g||^2`. On the killed prefix, [1371] forces the sharp floor
   `||g||^2 >= 4 / B_R(d)` (the anchor lives in the invisible
   complement). The joint deliverable N1c therefore has the shape
   announced in [1376] section 2c:

```text
local band mass >= |G(d + i*t0)|^2 / B(d, delta, W)
                  - K_loc * (off-band coupling) * ||g||^2,
```

to be read together with the floor. Falsifier (unchanged): if the
coupling term always dominates, the bridge is real only in cells where
the constructed norm is controlled, and that condition becomes an
explicit hypothesis of the closure theorem.

## 6. Honesty ledger

- PAPER ONLY: no Lean statement in this record. N1d (formal leaf) is
  pending an L^2-norm interface export — the register family is
  currently value-based (`HealthyYoshidaDetectorData` pins VALUES at
  nodes; `CompactLogTest` carries smoothness + compact support, and no
  `||.||_2` accessor is exposed in the B5 path).
- No digits: nothing here requires a preregistered run (law 42
  untouched); the [1376] section 2b comparison table stays MODEL.
- Lemma A-prime's subfamily clause ("how much smaller is the spline
  evaluation norm") is OPEN and is called a lever, not a result.
- RH NOT claimed; stop word unchanged (gate Lean certificate, 1358).
