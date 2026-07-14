# Proof 218: archimedean relative-form collapse

Date: 2026-07-13

Status: accepted mathematical ownership verdict.  After the genuine Q-root
relation is restored, the `delta_hat` part of the CC20 positive multiplier is
exactly the Fourier image of the post-Q remainder `-2 Id+K_I`.  Subtracting
that remainder cancels `delta_hat` and returns the original archimedean Weil
multiplier `2 theta'`.  The archimedean relative-form branch therefore does
not create a new positive budget below Weil positivity.  RH remains unproved.

## 1. Three exact identities

The CC20 positive trace has multiplier

```text
ell_CC20(t)=2 theta'(t)+delta_hat(t).                   (R.1)
```

Proof 214 certifies the additional true inequality

```text
ell_CC20(t)>1/50.                                      (R.2)
```

The Q-root owner is

```text
L=d/dx+1/2,
g=L xi,
g* * g=Q(xi* * xi),
Q=-d^2/dx^2+1/4.                                      (R.3)
```

Finally, CC20's archimedean post-Q remainder is

```text
D_infinity(Q(xi* * xi))
 = <xi,(-2 Id+K_I)xi>
 = <xi,Q(delta)xi>.                                   (R.4)
```

The ordinary kernel `K_I` is the regular part of `Q(delta)`; the diagonal
distribution contributes `-2 Id`.  The project definitions make this split
explicit: `RegularKernel.lean:12-13` excludes the Dirac mass, while
`RegularKernelCandidate.lean:91-96` defines the ordinary `Q(delta)` profile.

## 2. Fourier cancellation

For a compact smooth pre-root,

```text
g_hat(t)=(1/2+it) xi_hat(t),
|g_hat(t)|^2=(t^2+1/4)|xi_hat(t)|^2.                  (R.5)
```

The `delta_hat` contribution to the positive trace is therefore

```text
integral delta_hat(t)|g_hat(t)|^2 dt/(2pi)
 = integral (t^2+1/4)delta_hat(t)|xi_hat(t)|^2 dt/(2pi)
 = D_infinity(Q(xi* * xi)).                           (R.6)
```

Combining (R.1) and (R.6) gives the exact cancellation

```text
PositiveTrace_infinity(g)-D_infinity(g* * g)
 = integral 2 theta'(t)|g_hat(t)|^2 dt/(2pi)
 = W_infinity(g* * g).                                (R.7)
```

This is also forced abstractly by the source identity

```text
PositiveTrace_infinity(F)=W_infinity(F)+D_infinity(F),
```

recorded in Proof 016, equation (7) and its archimedean specialization.

## 3. Full relative form

When the pole rows vanish, the corrected QW form is

```text
QW(g,g)
 = PositiveTrace_infinity(g)
     -D_infinity(g* * g)
     -<g,K_c g>

 = <g,(2 theta'(D)-K_c)g>.                            (R.8)
```

Thus the apparent decomposition

```text
positive trace
  + 2 Id
  - K_I
  - finite primes
```

is not four independent budgets.  The middle three archimedean pieces in
the first line of (R.8) recombine to the original Gamma-place Weil term.

Replacing `ell_CC20` by `1/50` before subtracting the exact remainder breaks
this cancellation and produces the wrong-object form rejected in Proof 217.

## 4. Numerical consistency check

The corrected FFT probe first omits `K_I` and screens

```text
<g,ell_CC20(D)g>+2||L^-1g||^2-<g,K_cg>.
```

At size 300 it has minima near `-0.07` to `-0.08`:

```text
+----------+-------------------------+
| cutoff   | without K_I             |
+----------+-------------------------+
| 16       | -0.069993109109         |
| 64       | -0.078517725610         |
| 256      | -0.081219786021         |
| 1024     | -0.080946337620         |
+----------+-------------------------+
```

After applying the exact cancellation and screening
`2 theta'(D)-K_c`, the values fall to the discretization-sensitive scale:

```text
+----------+-------------------------+
| cutoff   | with full remainder     |
+----------+-------------------------+
| 16       | -0.000027209191         |
| 64       | -0.001650622680         |
| 256      | -0.002816970411         |
| 1024     | -0.013639666194         |
+----------+-------------------------+
```

At `c=256`, sizes 200, 400, 600, and 800 give nonmonotone values between
about `-0.0393` and `-0.00118`.  These are not evidence against RH; linear
translation interpolation and FFT periodization do not preserve exact Weil
positivity.  Their only use is checking that the implementation exhibits the
algebraic cancellation.

## 5. Route consequence

The following route is rejected as a lower producer:

```text
strict lower bound for ell_CC20
  -> add opposite of -2 Id+K_I
  -> obtain new unconditional surplus over finite primes.
```

There is no such surplus on the same Q-root.  It cancels to `2 theta'`.

Two routes remain logically distinct:

```text
1. construct the genuine finite-S positive owner and prove a new sign for its
   semilocal post-Q remainder before it collapses to the global Weil form;

2. prove a detector-specific inequality using structure beyond the three
   Mellin rows, without asserting the full restricted Weil sign as a premise.
```

The first is still Plan 032's same-object finite-S bottom.  The second needs a
new property of the canonical off-line detector; generic PNT-main or global
multiplier bounds do not provide it.

A fresh primary-source screen does not supply that property.  The
Gaussian--Perron defect of arXiv:2607.04316 gives an exact smoothed prime/zero
formula and a selected-zero local profile, but its full localization theorem
uses explicit damping, pole, and shifted-contour hypotheses; its critical-line
full-profile theorem assumes RH.  The paper defines a useful diagnostic, not
an unconditional sign for the prime defect or a finite-S remainder producer:

```text
https://arxiv.org/abs/2607.04316
Theorem 7.4: conditional nonlocal-remainder localization
Theorem 7.6: RH-conditional full local profile
```

## 6. Reproduction

```text
python3 -B docs/proofs/218_qroot_full_multiplier_probe.py \
  --cutoff 16 64 256 1024 --size 300 \
  --padding-half-length 64 --dct-intervals 65536
```

## 7. Route judgment

```text
Q-root/source-root ownership:            corrected
delta_hat versus Q(delta):               exact cancellation
Proof 214 strict multiplier theorem:     survives independently
archimedean relative-form surplus:       rejected
finite-S post-Q remainder sign:          still open
detector-specific full-prime inequality: still open
Gaussian--Perron source shortcut:        conditional / rejected as producer
Lean owner:                              none
RH:                                      unproved
```
