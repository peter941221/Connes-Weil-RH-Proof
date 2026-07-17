# Proof 324: compact-root radial boundary transport

## Result

The result is positive but does not close Gate 3U.

This batch proves that the compact continuous-kernel Hilbert--Schmidt pair is
the actual oriented crossing of the selected positive convolution detector,
transports that trace-class owner to the genuine CCM24 radial boundary, and
identifies the source second-support projection through the actual
Hardy--Titchmarsh involution. It also proves that conjugating the detector by
that involution reflects its Fourier multiplier and cancels the scattering
phase exactly.

The remaining fixed-source bottom is the coupled second-support/prolate
remainder. The reflected spectral detector has not yet been reconstructed as
the positive convolution square of an explicit reflected compact test, and no
uniform-in-`S` signed estimate is proved.

## 1. Proof flow

```text
compact root g, supp(g) subset [a,c]
              |
              v
finite continuous kernels K_- and K_+
              |
              v
        K_-^dagger K_+
              |
              v
(I-E_0) (C_g^dagger C_g) E_0
              |
       logarithmic translation
              v
(I-E_lambda) W E_lambda
              |
       Q_0=H_infinity E_lambda H_infinity
              v
outer pair + [second support - K_prol] remainder
```

The compact carriers are not surrogate windows. Their zero extensions are
proved equal to the genuine whole-line crossing before any trace statement is
used.

## 2. Named-basis Hilbert--Schmidt ideal

`HilbertSchmidtIdeal.lean` proves that named-basis square summability survives
bounded precomposition and postcomposition. It lifts that calculus to the
project's complete pair owner:

```text
traceProduct(A,B)=A^dagger B.
```

The pair can now be swapped, added, subtracted, scaled on the right, and
sandwiched by arbitrary bounded operators while retaining an explicit
`IsTraceClassAlong` witness. These are legality theorems only; they introduce
no Schatten-norm estimate.

## 3. Compact-root Fubini identity

For a compact root supported in `[a,c]`, the negative and positive input legs
live on the finite intervals `[a-c,0]` and `[0,c-a]`. The common output leg
lives on `[-c,-a]`.

`CompactRootHalfLinePair.lean` constructs the two continuous-kernel factors.
`CompactConvolutionSupport.lean` then proves, by two legal Fubini exchanges on
finite-measure compact spaces,

```text
finiteNegativeBoundaryRootOperator^dagger
  * finitePositiveBoundaryRootOperator
    = squareBoundaryKernelOperator.
```

The equality is first proved on continuous representatives and then extended
to all of `L2` through the dense range of `ContinuousMap.toLp`. No pointwise
choice of an arbitrary `L2` representative is used.

## 4. Genuine detector crossing

The finite square kernel is identified with the restriction of the actual
whole-line convolution square. Its zero extension therefore satisfies

```text
pairData.traceProduct
  =(I-E_0) (C_g^dagger C_g) E_0.
```

The signed compact owner is consequently the genuine commutator

```text
[E_0,C_g^dagger C_g]
  =pairData.traceProduct^dagger-pairData.traceProduct.
```

This removes the earlier gap where `windowedBoundaryDetector` was only a
finite-window object with no equality to the selected global detector.

## 5. Actual CCM24 support projections

`CCM24RadialHalfLineAlignment.lean` proves on the common logarithmic carrier

```text
E_lambda=U_(log lambda) E_0 U_(-log lambda).
```

The equality is obtained from literal almost-everywhere indicator formulas
and equality of orthogonal-projection ranges.

For the source second support, the same module proves

```text
Q_0=H_infinity^dagger E_lambda H_infinity
   =H_infinity E_lambda H_infinity.
```

Its fixed space is exactly the archimedean Fourier-support closed subspace.
At a moving finite-S time, the corresponding projection is instead the
canonical Gram-corrected projection onto the bounded-invertible image:

```text
Q_alpha=starProjection(T_alpha(Q_0-space)).
```

It is not replaced by the oblique similarity `T_alpha Q_0 T_alpha^-1`.

## 6. Radial trace transport

The selected positive convolution detector commutes with logarithmic
translations. Transporting both compact factors gives an exact pair owner for

```text
(I-E_lambda) W E_lambda.
```

The ordinary named-basis trace is invariant because both factors are cycled
onto their common compact output carrier, where the inverse translations
cancel. This yields trace-class legality for the radial commutator and for any
bounded left/right sandwich of it.

The two source outer branches are therefore trace class. Their relation is

```text
reflectedOuter=-outer^dagger,
```

because `[E_lambda,W]` is skew-adjoint.

## 7. Second-support scattering owner

With `H=H_infinity`, define

```text
W_H=H W H.
```

The genuine source second-support crossing and commutator satisfy

```text
(I-Q_0)WQ_0=H(I-E_lambda)W_H E_lambda H,
[Q_0,W]=H[E_lambda,W_H]H.
```

The detector must not be silently commuted through `H`. The new spectral
calculation instead proves

```text
H W H=F^-1 R M_w R F,
```

where `R` is frequency reflection. The scalar archimedean scattering
multipliers commute with `M_w`, and the two involution identities cancel both
phases exactly.

## 8. Coupled source remainder

The exact source remainder is

```text
sourceSecondSupportProlateRemainder
  =E H [E,HWH] H E-[K_0,W].
```

It is skew-adjoint and the full source three-branch commutator is

```text
outerPair+sourceSecondSupportProlateRemainder.
```

The existing theorem derives trace legality of the full owner from an
explicit trace-class witness for this coupled remainder. It does not assume or
prove that witness. The second-support and prolate terms must remain together;
Proof 258's cancellation guard forbids estimating them separately.

## 9. Verification

The WSL2 verification commands are:

```text
lake env lean ConnesWeilRH/Source/CC20Concrete/CompactConvolutionSupport.lean
lake env lean ConnesWeilRH/Source/CCM25Concrete/CCM24RadialBoundaryPairTransport.lean
lake build ConnesWeilRH.Source.CCM25Concrete
lake build
lake env lean ConnesWeilRH/Dev/CCM24RadialBoundaryPairAudit.lean
```

Results:

```text
CCM25 aggregate: 3642 jobs
full build:       3726 jobs
focused audit:    passed
audited axioms:   [propext, Classical.choice, Quot.sound]
```

The touched proof modules contain no `sorry`, `admit`, `sorryAx`, stored route
premise, or new axiom.

## 10. Remaining bottom

Proof 324 does not prove any of the following:

```text
an explicit compact reflected root whose square realizes F^-1 R M_w R F;
trace-class legality of the coupled second-support/prolate remainder;
trace-norm continuity for the complete moving owner;
the compact-support signed scalar estimate uniformly in S;
Gate 3U, the finite-S sign, Burnol's identity, or RH.
```

The immediate successor is to reflect `CompactLogTest` itself, prove its
Fourier multiplier is `w(-xi)`, reuse the compact pair for `W_H`, and then
recombine that crossing with `[K_0,W]` before taking one absolute value.
