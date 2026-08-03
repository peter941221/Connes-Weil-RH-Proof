# Proof 774: Real Directed Full-Kernel Crossing

## Result

Proof 774 identifies one exact cancellation in the real Gate 3U scalar.  It
does not prove its support-polynomial bound.

Write

```text
P = sourceSoninProjection,
K = [P,W],
J = sourceInclusion,
U = sourceEndpointCancellationResidual,
F = sourceActualBandForwardCoframe.
```

The complete physical kernel is the one operator `K`, including its outer,
reflected second-support, and prolate branches.  It is skew-adjoint:

```text
K^dagger = -K.
```

For every source vector `x`, Lean now proves

```text
Re(<Jx, K Ux> - <Fx, K Jx>)
  = Re <Jx, K (Ux + Fx)>.                         (774.1)
```

The corresponding ordered-prefix identity is

```text
Re sum_(i<N) FullKernel_S(e_i)
  = sum_(i<N) Re <J e_i, K (U_S + F_S)e_i>.       (774.2)
```

The source declarations are in
`CCM24FiniteSGatePhysicalRealDirectedCrossing.lean`:

```text
sourceGatePhysicalFullKernelScalar_re_eq_realDirectedKernelScalar
sourceGatePhysicalPrefixFullKernelPairing_re_eq_realDirectedKernelPairing
```

## Why This Is the Correct Compression

The two coframe terms in the old scalar are not independent once the real
part is taken:

```text
<J, K F> = -conj(<F, K J>).
```

Therefore the second orientation contributes `+F` to the real directed
crossing.  It does not cancel `U`.

```text
two oriented terms
        |
        v
Re[Omega(J,U) - Omega(F,J)]
        |
        | K^dagger = -K
        v
Re Omega(J,U+F)
        |
        v
one completed outer/reflected-second-support/prolate crossing
```

This keeps compact-root support in the completed commutator.  Replacing `K`
by a bare detector `W`, or estimating the `U` and `F` pieces separately,
would discard exactly the boundary cancellation that makes the fixed-`S`
trace legal.

## No Generic Bound

Equation `(774.1)` is an algebraic normal form, not a uniform estimate.  The
following two-dimensional model satisfies the available abstract facts for
arbitrary `t > 0`:

```text
P = [[1,0],[0,0]],        J(1) = e_1,
F(1) = 0,                U(1) = t e_2,
W = [[0,1],[1,0]],       K = [P,W] = [[0,1],[-1,0]].
```

It has

```text
P U = 0,
J^dagger U = 0,
P F = 0,
norm(F) <= 1,
U = F + U,
K^dagger = -K,
```

but its complete scalar is

```text
Re(<J, K U> - <F, K J>) = t.
```

So the already known projection orthogonality, forward contraction, and
skew-adjointness cannot bound Gate 3U.  The missing source theorem must bound
the complete, compact-root-relative crossing in `(774.2)` using the genuine
real-line outer/reflected-second-support/prolate geometry.

## Scope

```text
+----------------------------------------------------------+----------------+
| claim                                                    | status         |
+----------------------------------------------------------+----------------+
| exact real directed full-kernel normal form             | Lean proved    |
| ordered-prefix real normal form                          | Lean proved    |
| generic bound from U orthogonality and F contraction    | disproved      |
| compact-root support-polynomial estimate                | open           |
| Gate 3U / finite-S sign / Burnol identity / RH          | open           |
+----------------------------------------------------------+----------------+
```

The finite certificate is
`docs/proofs/774_real_directed_full_kernel_crossing_probe.py`.
