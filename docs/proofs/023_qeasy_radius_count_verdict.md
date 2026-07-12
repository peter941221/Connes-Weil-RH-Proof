# 023 Qeasy Radius--Count Verdict

## Result

The highest-risk and currently blocking gate in Plan 023 is the simultaneous
nearby-radius and convolution-count choice. This is not an endpoint estimate.
It is the condition required to turn a finite-node interpolation result into
one detector that controls every other source zero.

```text
choose R
  -> interpolate all source zeros with distance < R
  -> obtain test-dependent constants C_R and T_R
  -> choose convolution count n_R
  -> tail estimate begins only at (n_R + 1) * T_R

required: R >= (n_R + 1) * T_R.
```

The existing construction proves the arrows in the first four lines but has no
bound proving the final inequality. It therefore does not construct the test
required by CC20 Appendix C.

## Primary Sources

Connes--Consani, `weil-compo.tex`, Corollary `qeasy`, lines 832--840 of the
arXiv source archive:

```text
D o Q has the local sign in the interval [u^-1,u], u = 1.10246.
The proof uses positive-definiteness through |f(x)| <= f(0).
```

<https://arxiv.org/abs/2006.13771>

Appendix C, lines 2075--2085, requires a single `g0` with value one at the
selected zero and a distance-squared smallness bound at every other zero. A
local remainder sign does not create this global detector.

Yoshida, Lemma 1, pp. 285--286, constructs finitely many correction factors
and convolves the base factor `N` times. Its support is not held in a fixed
narrow interval. The proof can therefore increase `N` without introducing the
rescaled threshold `(N+1) * T`.

<https://projecteuclid.org/ebooks/advanced-studies-in-pure-mathematics/Zeta-Functions-in-Geometry/chapter/On-Hermitian-Forms-attached-to-Zeta-Functions/10.2969/aspm/02110281.pdf>

## Consequence

The normalized scaling used to fit `qeasy` is structurally different from
Yoshida's Lemma 1:

```text
unscaled Yoshida product: support grows with N; far threshold stays fixed
normalized qeasy product: support stays fixed; far threshold grows with N
```

The current source and Lean APIs supply no control of `C_R` or `T_R` that could
produce a fixed point `R >= (n_R + 1) * T_R`. This rejects the present P2
assembly as a detector producer. It does not prove that every possible Connes
or narrow-support strategy is impossible.

## Rejected Escape: Infinite Interpolation

One cannot remove the radius/count cycle by asking one fixed narrow-support
test to vanish at every source zero other than the marked zero. In logarithmic
coordinates, the Mellin transform of a nonzero compactly supported test is an
entire function of finite exponential type. Its zero count in disks is
`O(R)`. The distinct nontrivial zeta zeros are not `O(R)`. Therefore a test
whose transform vanished at all of them would be identically zero, contradicting
the required value one at the marked zero.

This is not a new claim: Yoshida uses exactly this finite-exponential-type
versus zeta-zero-density contradiction on p. 321 of the 1992 paper cited
above. It proves that P2 must retain a finite nearby set and a genuine far-tail
estimate; an infinite zero-interpolation replacement is unavailable.

The finite correction obstruction is now separate from this verdict. The
compiled theorem `exists_convolutionSquare_base_fullProduct_indicator` gives a
positive-definite finite 0/1 pattern under an explicit Hermitian-reflection
separation condition. It removes arbitrary correction factors from the finite
layer, but it supplies no bound on the test-dependent constants entering the
radius/count cycle.

The source-zero specialization is also now compiled. The theorem
`exists_sourceZero_nearby_convolutionSquare_indicator` applies the same
construction to

```text
sourceNontrivialZerosInClosedBallFinset rho R union routeNodes
```

when `rho` is a source nontrivial zero, `R >= 0`, and the finite route-node set
lies in the closed right half-plane. The source open-strip bound supplies the
strict positive real part needed for the marked zero; hence the finite
Hermitian-collision side condition is discharged on the same object. This is
finite-neighborhood progress only. It neither controls the convolution count
nor establishes the required `R >= (n + 1) * T` fixed point.

## Deterministic Route Verdict

Plan 023 is dead as an independent RH route. This is not an assertion that its
fixed-point inequality is mathematically false.

The completed P2 contract asks for one compact positive-definite test with
finite detection and an all-other-source-zero estimate. After the planned
`qeasy` transfer, that is exactly the concrete detector-existence input in the
formal CC20 exit:

```text
CC20YoshidaDetectorExists C F
  + CC20FiniteVanishingWeilCriterion C F
  -> RHDefinitionBridge.standard.SourceRH.
```

This implication is proved by `cc20_proposition_c1_from_yoshida_detector` in
`ConnesWeilRH/Source/CC20YoshidaCriterion.lean:219-243`. Therefore P2--P3 is
RH-level: proving it would prove the source RH statement, not lower an active
root below RH.

```text
P2 as a non-circular route to RH: dead.
P2 as an abstract quantitative fixed-point assertion: unresolved.
All Connes strategies: not ruled out.
```

## Required Reopening Contract

No extension of this P2-to-P3 detector route can reopen Plan 023 as a lower RH
route. A future narrow-support lane needs an analytic theorem with a consumer
strictly weaker than source RH, rather than another construction of
`CC20YoshidaDetectorExists`.

For the standalone fixed-point question, only one of these would settle its
truth value:

```text
1. A one-object quantitative theorem simultaneously producing R, n, T, and a
   positive-definite test with R >= (n+1)T.

2. A different positive-definite tail construction whose far estimate begins
   at a threshold independent of its support-preserving convolution count.
```

Neither contract may assume SourceRH, no-off-line-source-zero, detector
coverage, or a source zero-sum sign equivalent to RH.
