# Proof 602: Old-Carrier Coframe Range Factorization

## Result

The generic old-carrier boundary channel now has an exact factorization
interface. For a frame `N`, an invertible transport pair `U, V`, and a row `B`,
the source obligations are:

```text
N^* N = I
U V = I
B V^* N = 0
```

With `Q = I - N N^*` and `F = B V^* Q`, Lean proves:

```text
F Q U^* = B
||F|| <= ||B|| ||V||.
```

This is the required shape for feeding a physical coframe row into the moving
boundary component of the old-carrier analysis. It is a factorization result,
not an estimate obtained by bounding the target row after the fact.

## Source Alignment Guard

The actual finite-S Euler data does not have a literal identity right inverse.
The existing theorem is:

```text
normalizedPrimeEulerFrameTransport p * normalizedPrimeEulerInverse p
  = primeSchurMarkovScalar p * I.
```

The scalar is positive and bounded away from zero, but it is not `1`. A source
adapter must therefore use
`primeSchurMarkovScalar p ^ (-1) * normalizedPrimeEulerInverse p`, or preserve
the scalar explicitly. The current module deliberately stays generic and does
not hide this correction.

The remaining source obligation is the exact annihilation of the relevant
orientation/residual row against the new-frame range. Proof 600 only proves
the weaker source-compressed commutator identity
`J^* [P_0, D] J = 0`; it does not prove `J^* D J = 0` and cannot discharge this
range condition.

## Verification

The source, audit, aggregate, and full repository builds passed in the
Ubuntu-24.04 ext4 verification mirror. The audited declarations use only
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, or user axiom
was added.

This proof does not close Bone 1 or Gate 3U.
