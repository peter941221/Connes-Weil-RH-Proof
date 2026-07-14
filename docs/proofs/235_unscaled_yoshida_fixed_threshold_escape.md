# Proof 235: unscaled Yoshida fixed-threshold escape

Date: 2026-07-14

Status: axiom-clean Lean closure of the radius--convolution-count feedback
identified in Proof 041.  Each convolution power uses the original base
factor.  The support grows linearly with the number of copies, while the
far-strip contraction uses the original spectral point.  The vertical
threshold precedes both the nearby-zero radius and the convolution count.  The
semilocal sign, finite-S positive owner, route rewire, and RH remain open.

## 1. Failure mechanism of the rescaled construction

Let `Phi` be the bilateral Laplace transform of a compact log test.  The old
support-preserving power used

```text
f_n(x)=(n+1) f((n+1)x),
G_n=f_n^(convolution n+1) * correction.
```

Its transform is

```text
Laplace(G_n)(s)
  =Phi(s/(n+1))^(n+1) Laplace(correction)(s).
```

If `Phi(s)` is contractive only for `|Im(s)|>=T`, the rescaled power is
contractive only for

```text
|Im(s)| >= (n+1)T.
```

Choosing the nearby-zero radius determines the finite correction constant.
The proof then chooses `n` from that constant, while the same radius must cover
`(n+1)T`.  These dependencies form a cycle:

```text
radius R
   |
   v
correction constant C(R)
   |
   v
power count n(C)
   |
   v
required radius >= (n+1)T
   +-------------------------> back to R
```

## 2. Unscaled construction

Keep the base test fixed and set

```text
G_n=f^(convolution n+1) * correction.
```

The source convolution law gives

```text
Laplace(G_n)(s)
  =Phi(s)^(n+1) Laplace(correction)(s).               (U.1)
```

Assume on the closed critical strip that

```text
|Phi(sigma+it)| <= 1/2                  for |t|>=T,
|t/(2pi)|^2 |Laplace(correction)(sigma+it)| <= C.
```

Then the new theorem
`convolutionIterate_convolution_vertical_quadratic_bound` proves

```text
|t/(2pi)|^2 |Laplace(G_n)(sigma+it)|
  <= (1/2)^(n+1) C                     for |t|>=T.     (U.2)
```

Equation `(U.2)` retains `T` as its threshold for every `n`.

The unscaled factors expand the support.  If

```text
support(f)          subset (a_0,b_0),
support(correction) subset (c_0,d_0),
```

then

```text
support(G_n)
  subset ((n+1)a_0+c_0, (n+1)b_0+d_0).               (U.3)
```

The semilocal route permits finite primes to enter this growing window.

## 3. Distance-weighted far tail

The existing strip geometry converts `(U.2)` into

```text
|z-rho|^2 |Laplace(G_n)(z)|
  <= (6pi)^2 (1/2)^(n+1) C,                           (U.4)
```

provided

```text
Re(z) in [0,1],
T <= |Im(z)|,
1 <= |Im(z)|,
2|Im(rho)| <= |Im(z)|.
```

After the correction and `C` are fixed, geometric decay chooses `n` so that
the right side of `(U.4)` is below any prescribed `epsilon>0`.  This is Lean
theorem `exists_convolutionIterate_convolution_distance_bound_lt`.

The dependency order is now acyclic:

```text
base f
   |
   +--> fixed threshold T
           |
           v
       choose radius R
           |
           v
       one correction and C(R)
           |
           v
       choose n after C
           |
           v
       epsilon-small far tail at the same T
```

## 4. Same-witness normalized assembly

Lean theorem
`exists_fixedThreshold_nearbyZero_unscaled_normalized_assembly` binds the
construction to one explicit assembled test.  Given a base normalized by

```text
Laplace(f)(rho)=1,
```

it chooses a single correction whose values are

```text
Laplace(correction)(rho)=1,
Laplace(correction)(z)=0
  for every other nearby source zero or route node.
```

The returned convolution product satisfies all four properties:

```text
Laplace(G_n)(rho)=1;
Laplace(G_n)(z)=0 at every other selected finite node;
the growing support law (U.3);
the fixed-threshold epsilon tail (U.4).
```

The printed type orders the witnesses as follows:

```text
exists T, 0 <= T and
  forall R, 0 <= R ->
    exists correction C n, ...
```

The theorem chooses `T` before `R` and chooses `n` after the correction
constant.
The normalization, finite-node cancellation, support, and tail are all facts
about the same expression

```text
(convolutionIterate f n).convolution correction.
```

One `hvalues` witness supplies both the target value and the zero values.

## 5. Lean evidence

The production declarations are in
`ConnesWeilRH/Source/CC20YoshidaConvolution.lean`:

```text
line 781  convolutionIterate_convolution_vertical_quadratic_bound
line 816  convolutionIterate_convolution_quadratic_bound_at_complex
line 834  convolutionIterate_convolution_distance_quadratic_bound
line 860  exists_convolutionIterate_convolution_distance_bound_lt
line 909  exists_residualWindow_nearbyZero_unscaled_assembled_distance_bound_lt
line 966  exists_fixedThreshold_nearbyZero_unscaled_normalized_assembly
```

The import-facing audit is
`ConnesWeilRH/Dev/UnifiedRemainingGapsYoshidaConvolutionAudit.lean`.  The WSL
verification sequence was:

```text
lake env lean ConnesWeilRH/Source/CC20YoshidaConvolution.lean
lake build ConnesWeilRH.Source.CC20YoshidaConvolution
lake env lean ConnesWeilRH/Dev/UnifiedRemainingGapsYoshidaConvolutionAudit.lean
```

The owning build completed 3474 jobs.  Each new declaration
reported only:

```text
propext
Classical.choice
Quot.sound
```

The implementation contains no `sorryAx`, new project axiom, stored tail
conclusion, or call to the rejected normalized CC20 toy convolution.

## 6. Route judgment

```text
unscaled convolution transform law:                 exact
far-strip threshold:                                fixed T
quadratic correction constant:                      same correction witness
epsilon-small distance tail:                        proved in Lean
support accounting:                                 linear growth, explicit
target normalization and finite-node cancellation: same assembled test
radius--count fixed point:                          removed
prime-free fixed-window detector:                   replaced by growing support
finite-S same-object remainder sign:                open
semilocal positive owner:                           open
Lean RH route rewire:                               none
RH:                                                  unproved
```

The next valid use is detector-specific: combine this growing-support test
with the named finite-prime owner and prove the complete finite-S
post-`Q` sign on the same three-row kernel.  Reimposing a fixed prime-free
support window would restore the rejected radius cycle.
