# Proof 471: Detector primitive outer pairing

## Result

Proof 470 exposed outer, reflected-outer, and coupled
second-support/prolate pairings at each global-basis diagonal.  Proof 471
reduces the first two coordinates to the single primitive
`translatedCompactRootPairData`.

For a generic pair `D` and bounded prefix `L`, the signed
`boundedAdjointSub` owner has forward and reverse pairings

```text
forward = <D.right(L^dagger x),D.left y>
        - <D.left(L^dagger x),D.right y>,

reverse = <D.left x,D.right(L^dagger y)>
        - <D.right x,D.left(L^dagger y)>.
```

The reflected outer owner is the negative swapped outer owner.  Consequently
the completed outer contribution is the four-term antisymmetrization

```text
forward - reverse.
```

Lean proves that the full physical pairing and atom trace are

```text
physicalPairing(x,y)
  = primitiveOuterReflectedPairing(x,y)
    + coupledSecondSupportProlatePairing(x,y),

trace(atom_z)
  = sum'_i -physicalPairing(B e_i,U_(-z)B e_i).
```

No absolute value, branchwise trace, or independent remainder estimate is
introduced.

## Boundary

The outer/reflected term now reaches the existing primitive compact-root pair,
but its `Lp` kernels have not yet been substituted into the four-term scalar.
The second-support/prolate remainder remains bundled.  Compact support,
renewal trace exchange, the uniform Gate 3U bound, the finite-S sign, Burnol's
identity, and `_root_.RiemannHypothesis` remain open.
