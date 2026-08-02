# Proof 746: Gate Physical Oblique-Shear Kernel Reduction

## Result

The result is structurally useful but does not close Gate 3U.  Proof 746
identifies Proof 745's square-zero shear with the adjoint of the already named
complete physical coframe leakage.  The active ordinary trace is consequently
one physical-kernel orientation, not Proof 741's centered difference of two
coframe orientations.

Write

```text
J   = sourceInclusion,
R   = sourceSoninProjection=J J^dagger,
H_S = finiteEulerAmbientGram=T_S^dagger T_S,
G_S = J^dagger H_S J,
D_S = H_S J G_S^(-1),
L_S = (I-R)D_S
    = sourceSoninCoframeLeakage_S
    = sourcePhysicalCoframeLeakage_S.
```

The pulled target projection has the exact Gram form

```text
Q_S=J G_S^(-1)J^dagger H_S=J D_S^dagger.             (OK.1)
```

Since `D_S-J=L_S`, Proof 746 proves

```text
N_S=Q_S-R=J(D_S^dagger-J^dagger)=J L_S^dagger.       (OK.2)
```

The proof also records both leakage orientations

```text
R L_S=0,
L_S^dagger R=0.                                      (OK.3)
```

These are exact range identities.  They do not bound `L_S`.

## Single Physical Orientation

Proof 745's target was `J^dagger N_S W J`.  Substituting `(OK.2)` and using
`J^dagger J=I` gives

```text
Target_S=L_S^dagger W J.                             (OK.4)
```

The fixed source boundary commutator is `[W,R]=W R-R W`.  Equations `(OK.3)`
and `R J=J` imply

```text
L_S^dagger[W,R]J=L_S^dagger WJ.                      (OK.5)
```

The repository's physical three-branch orientation is the opposite
commutator `[R,W]`.  Therefore, pointwise,

```text
<x,Target_S x>
  =<L_S x,WJx>
  =-PhysicalPair(L_S x,Jx).                          (OK.6)
```

The minus sign in `(OK.6)` comes from the proved identity
`[W,R]=-[R,W]`; it is not a trace-cycle convention.

## Full-Kernel Scalar

Proof 746 defines the single complete scalar

```text
Kernel_S(x)
  =-[OuterSigned(L_S x,Jx)
      +SecondSupportProlateFull(L_S x,Jx)].           (OK.7)
```

`OuterSigned` is the actual translated compact-root signed kernel.
`SecondSupportProlateFull` retains the reflected Hardy--Titchmarsh root legs
and the genuine prolate Hilbert--Schmidt square root in one signed bracket.
No primitive term is estimated separately.

For every named source Hilbert basis, Lean proves directly from the definition
of `ordinaryTraceAlong`

```text
Tr(Target_S)=sum'_i Kernel_S(e_i).                    (OK.8)
```

There is no infinite-dimensional trace cycle, diagonal rearrangement, or
finite-prefix limit in `(OK.8)`.

At the family quantifier level, the route now has the exact reduction

```text
(exists C, forall S, |Tr(Gate_S)| <= C)
  <->
(exists C, forall S, |sum'_i Kernel_S(e_i)| <= C).    (OK.9)
```

## What Changed

```text
+----------------------+-----------------------------------------------+
| previous owner       | exact readout                                 |
+----------------------+-----------------------------------------------+
| Proof 741 prefix     | Pair(Jx,U_S x)-Pair(F_S x,Jx)                 |
| Proof 745 shear      | J^dagger N_S WJ                               |
| Proof 746 kernel     | -Pair(L_S x,Jx), summed as one ordinary trace |
+----------------------+-----------------------------------------------+
```

Proof 746 is narrower at the ordinary-trace level because it removes the
centered two-coframe presentation.  It does not replace Proof 741's stronger
ordered-prefix sufficient route: ordinary-trace boundedness does not imply a
bound uniform in the prefix cutoff.

## Guard

Do not estimate `L_S`, `D_S`, `G_S^(-1)`, or `N_S` separately.  Such a bound
can recover the rejected finite-Euler condition number.  Do not infer that
`N_S^2=0` makes `(OK.7)` vanish.  The detector crosses from the source Sonin
range into its complement before `L_S^dagger` reads that component back.

Compact-root support must act on the complete signed scalar in `(OK.7)`
before any absolute value.  Proof 746 proves neither the uniform bound in
`(OK.9)` nor the finite-S sign, arithmetic same-object identity, Burnol
identity, or RH.

## Verification

The Windows source of truth was copied one way to the Ubuntu-24.04 WSL2 ext4
verification tree.  The accepted builds were

```text
+----------------------------------+-------+--------+
| target                           | jobs  | result |
+----------------------------------+-------+--------+
| focused source + axiom audit     |  3390 | PASS   |
| CCM25Concrete aggregate          |  4014 | PASS   |
| full repository                  |  4095 | PASS   |
+----------------------------------+-------+--------+
```

All fifteen audited theorems use exactly
`[propext, Classical.choice, Quot.sound]`.  The new source and audit contain
no `sorry`, `admit`, user axiom, heartbeat increase, recursion-limit increase,
unsafe declaration, new linter warning, or line over 100 characters.

Gate 3U, the finite-S sign, the arithmetic same-object identity, Burnol's
identity, and `_root_.RiemannHypothesis` remain open.
