# Proof 480: compact physical boundary energy

## Result

The result is good: all three compact physical boundary branches now have an
explicit common support-polynomial Hilbert--Schmidt energy bound. It does not
yet close Gate 3U or RH.

For a pair `D=(D_left,D_right)`, the signed boundary constructor keeps the
adjoint and forward orientations in orthogonal `L2` coordinates. If its two
outer sandwiches are contractions, Lean proves

```text
energy(boundedAdjointSub(D).left)
  <= energy(D.right) + energy(D.left),

energy(boundedAdjointSub(D).right)
  <= energy(D.left) + energy(D.right).
```

Proofs 478 and 479 bound each primitive energy by

```text
P = (c-a)^2 * seminorm_0,0(g)^2.
```

The radial support, Fourier support, identity, and Hardy--Titchmarsh maps are
all contractions. Consequently each leg of

```text
outerCommutatorPairData,
reflectedOuterCommutatorPairData,
secondSupportCommutatorPairData
```

has energy at most `2P`, independently of the finite visible prime family.

## Boundary

Proof 480 controls every compact boundary branch, but the fixed prolate
commutator remains. The next producer must bound its two pair energies in
terms of the fixed prolate factor energy and the detector operator norm, then
sum the orthogonal physical coordinates and feed the result into Proof 477.

No renewal/basis sum exchange, canonical Gate 3U polynomial, finite-S sign,
negative-owner integration, Burnol identity, or
`_root_.RiemannHypothesis` is proved here.
