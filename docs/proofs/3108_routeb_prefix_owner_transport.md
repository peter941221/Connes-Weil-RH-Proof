# Route-B conditional prefix transport on the rho-owner (3108)

Date: 2026-10-25.

The row-B prefix requires square zeros for every source zero in the height
prefix `|Im z| < 64` outside the four-point functional-equation orbit. The
rho-dependent G8 geometry already supplies square-zero control in the ball

```text
radius = 2^(tailStart + 1) + 2 + dist(2, rho)
```

3108 proves the exact same-owner bridge under the explicit premise
`5 <= tailStart`:

```text
package_hzero_prefix3108
  shell prefix 6 + 5 <= tailStart
    -> package.g convolution square vanishes outside the orbit

package_rowBSpanPrefix3108
  package target identity + package_hzero_prefix3108 + row-B Im cap
    -> the wired shell-prefix bound at lambda = 24
```

The proof handles both cases that the geometry distinguishes:

- a controlled zero at a healthy target node uses the existing target-zero
  theorem;
- every other controlled zero uses `OrbitG8Geometry.square_zero_control`.

The attempted unconditional `tailStart >= 5` derivation was rejected. The
geometry only provides

```text
4 * tailAccuracy^2 * spectralMultiplicityConstant * (3/4)^tailStart
  < xiMultiplicity rho
```

and the right side is a variable multiplicity, potentially larger than one.
The Lean source therefore keeps `5 <= tailStart` as an explicit premise.
This is a formal residual, not an omitted simplification.

Verification in the Linux ext4 mirror:

```text
lake build ConnesWeilRH.Dev.C1RouteBPrefixOwnerTransport3108Audit
```

The build completed successfully with 3886 jobs. Both declarations have no
errors or `sorryAx` and exactly the standard axiom trio:

```text
[propext, Classical.choice, Quot.sound]
```

This brick removes the owner mismatch and closed-ball mapping work once the
tail-index lower bound is supplied. It does not prove `hgate24`, the three
cardinal pins, or RH.
