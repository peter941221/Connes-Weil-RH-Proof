# Proof 470: Detector complete physical diagonal

## Result

Proof 469 moved the displacement trace to the complete physical boundary
carrier.  Proof 470 instead reads the same Hilbert--Schmidt product along the
named global basis and expands only the nested `L2` coordinates of
`sourceThreeBranchPairData`.

For left and right inputs `x,y`, the complete boundary pairing is

```text
<outer.left x, outer.right y>
  + <reflected.left x, reflected.right y>
  + <remainder.left x, remainder.right y>,
```

where `remainder` still couples the second-support and prolate contributions.
For a global basis vector `e_i`, set

```text
x_i = B e_i,
y_i = U_(-z) B e_i.
```

Lean proves the exact signed trace formula

```text
rootCompletedDetectorSoninTranslationTrace(z)
  = sum'_i -physicalPairing(x_i,y_i).
```

No componentwise ordinary trace, trace norm, or absolute value occurs.  The
formula exposes the compact-root outer coordinates and retains the required
second-support/prolate cancellation inside every summand.

## Boundary

The three physical pairings are still bundled operators rather than explicit
continuous-kernel integrals.  Compact root support has not yet been applied,
and renewal trace exchange, the uniform Gate 3U bound, the finite-S sign,
Burnol's identity, and `_root_.RiemannHypothesis` remain open.
