# Proof 217: Q-root same-object correction

Date: 2026-07-13

Status: accepted ownership correction and numerical death test.  Proof 213's
claimed `p=2` relative-form pass compares the finite-prime term and the CC20
coercive term on different convolution squares.  With the genuine Q-root
relation restored, the `1/50` coarse form is strongly negative already for the
single `p=2` channel at `c=256`.  Proof 214's standalone multiplier bound
remains valid.  Proofs 213 and 215 are not route evidence.  RH remains
unproved.

## 1. Exact same-object relation

CC20's post-Q remainder theorem has the form

```text
D_infinity(Q(xi* * xi))
  = <xi,(-2 Id+K_I)xi>.                               (Q.1)
```

The convolution square in the Weil formula must therefore be produced by

```text
L=d/dx+1/2,
g=L xi.
```

The additive involution reverses the derivative, so

```text
(L xi)* * (L xi)
 = (-d/dx+1/2)(d/dx+1/2)(xi* * xi)
 = Q(xi* * xi).                                       (Q.2)
```

This is the exact algebra recorded in Proof 071.  Proof 070 separately rejects
identifying a raw convolution square with this Q-image.

Combining (Q.1)-(Q.2) with the finite-prime read-off fixes the carriers:

```text
+--------------------------------------------------------------+
| source root g=L xi                                           |
|                                                              |
| PositiveTrace(g)             finite primes <g,K_c g>         |
+-----------------------+----------------------+---------------+
                        | same square g* * g   |
                        v                      v
                 D_infinity(g* * g)
                   = <xi,(-2 Id+K_I)xi>
+--------------------------------------------------------------+
```

Thus the corrected relative form is

```text
PositiveTrace(g)
  +2||xi||^2-<xi,K_I xi>-<g,K_c g>.                  (Q.3)
```

The prime form acts on `g`; the scalar and compact terms act on `xi`.

## 2. What Proof 213 actually bounded

Proof 213 proves an inequality of the shape

```text
PositiveTrace(Q(g* * g))+2||g||^2-<g,K_c g> >= 0.    (Q.4)
```

Its Plancherel term is

```text
(1/50)(||g'||^2+(1/4)||g||^2).
```

But if `g` in (Q.4) is the pre-root `xi`, then the finite-prime term for the
same Q-image is

```text
<L xi,K_c L xi>,                                      (Q.5)
```

not `<xi,K_c xi>`.  If `g` is instead the source root, then the positive trace
has only the multiplier `ell_CC20(t)|g_hat(t)|^2`; it does not gain another
factor `t^2+1/4`.

The extra derivative in (Q.4), without the matching derivative in (Q.5), is
the entire source of the reported positive margin.

## 3. Corrected coarse form

On the range condition

```text
integral exp(x/2)g(x)dx=0,
```

the pre-root is explicitly

```text
xi(x)
 = exp(-x/2) integral_(-a)^x exp(t/2)g(t)dt
 = L^(-1)g.                                           (Q.6)
```

Using only Proof 214's global minimum gives the correctly owned coarse form

```text
(1/50)||g||^2+2||L^(-1)g||^2-<g,K_c g>.              (Q.7)
```

The ordinary compact term is deliberately omitted in this first death test.

## 4. Numerical death test

The probe discretizes (Q.6) by its lower-triangular Volterra matrix, imposes
the range and pole rows, and evaluates (Q.7).  For the exact visible
prime-power shifts aggregated by linear interpolation, the constrained minima
at grid size 500 are

```text
+----------+--------------------------+
| cutoff   | corrected minimum        |
+----------+--------------------------+
| 16       | -2.474958135458          |
| 64       | -2.910103048509          |
| 256      | -2.970256798073          |
| 1024     | -3.062081532301          |
| 10000    | -2.959992859637          |
+----------+--------------------------+
```

For the single `p=2` channel at `c=256`, refinement gives

```text
+-------+--------------------------+
| size  | corrected minimum        |
+-------+--------------------------+
| 250   | -1.997516715716          |
| 500   | -2.016823870003          |
| 1000  | -2.025782312339          |
+-------+--------------------------+
```

These values are numerical death evidence, not continuum certificates.  The
ownership mismatch itself is exact and already invalidates the old pass.

## 5. Consequences

The following claims are withdrawn:

```text
Proof 213 passes the same-object p=2 gate;
Proof 214 plus Proof 213 gives a finite-Euler theorem;
Proof 215 identifies the next same-object all-prime bottom;
the 1/50 derivative budget can be spent against K_c on the pre-root.
```

The following results survive:

```text
Proof 214: ell_CC20(t)>1/50 for every real t;
Proof 215: exact sign of the continuous PNT main kernel in its raw model;
Proof 216: exact no-go for a constant raw-model S-procedure;
SelectedPrimeTranslationQuadratic: finite-prime read-off on the source root.
```

The active noncompact comparison must retain the full source-root multiplier:

```text
<g,(ell_CC20(D)-K_c)g>
  +2||L^(-1)g||^2-<L^(-1)g,K_I L^(-1)g>.             (Q.8)
```

Replacing `ell_CC20` by its minimum `1/50` is already numerically dead.

## 6. Reproduction

```text
python3 -B docs/proofs/217_qroot_same_object_relative_probe.py \
  --cutoff 16 64 256 1024 10000 --size 500

python3 -B docs/proofs/217_qroot_same_object_relative_probe.py \
  --cutoff 256 --size 1000 --single-prime 2
```

## 7. Route judgment

```text
Q-root ownership audit:                 failed old Proof 213 object
correct source/pre-root relation:       g=(d/dx+1/2)xi
single-p=2 corrected coarse screen:     strongly negative
global 1/50 replacement:                rejected for the route
full ell_CC20 multiplier comparison:    open
ordinary K_I same-object reinsertion:   open
Lean owner:                              none
RH:                                      unproved
```
