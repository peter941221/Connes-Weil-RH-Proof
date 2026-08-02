# Proof 741: Gate Physical Prefix Full Kernel Pairing

## Result

Proof 741 opens Proof 740's remaining coupled second-support/prolate
coefficient to its primitive reflected compact-root legs and the genuine
source prolate square root.

Let

```text
R  = radialSupportProjection,
N2 = reflected negative compact-root leg after Hardy--Titchmarsh transport,
P2 = reflected positive compact-root leg after Hardy--Titchmarsh transport,
A  = sourceProlateHilbertSchmidtFactor,
W  = detectorOperator.
```

Lean proves the exact scalar identity

```text
SecondSupportProlate(x,y)
  = <P2(Rx),N2(Ry)> - <N2(Rx),P2(Ry)>
    - [<Ax,A(Wy)> - <A(Wx),Ay>].
```

The full centered scalar is therefore

```text
FullKernel_S(x)
  = [OuterSignedKernel(Jx,U_S x)
      + SecondSupportProlate(Jx,U_S x)]
    - [OuterSignedKernel(F_S x,Jx)
      + SecondSupportProlate(F_S x,Jx)].
```

For every ordered source-basis prefix, the existing boundary trace and the
new primitive scalar agree exactly:

```text
Tr_boundary(CenteredPrefix_(S,N))
  = sum_(i < N) FullKernel_S(e_i).
```

A common bound on the right-hand side feeds the exact ordinary Gate-trace
consumer.

## Structure

```text
Proof 740 coupled remainder
        |
        +-- second support --> reflected N2/P2 signed crossing
        |
        +-- prolate        --> A/W commutator square
        |
        v
one five-term physical scalar
        |
        | subtract the two coframe orientations
        v
ordered full-kernel prefix
        |
        | only here seek one uniform bound
        v
Gate 3U consumer
```

The reflected legs are not abstract witnesses: their definitions use the
existing continuous compact-root kernel factors, the genuine logarithmic
translation, and the archimedean Hardy--Titchmarsh operator.  The prolate
term uses the existing Hilbert--Schmidt square root whose Gram operator is
the source prolate remainder.

## Guard

Keep the entire `FullKernel_S(e_i)` scalar intact.  In particular:

```text
- do not bound outer, second-support, and prolate terms separately;
- do not bound the (J,U_S) and (F_S,J) orientations separately;
- do not move the ordered prefix cutoff through a coframe or boundary leg;
- do not take an absolute value before using compact-root support.
```

Proof 741 supplies a complete concrete kernel normal form only.  The active
analytic target remains a bound independent of both the finite prime family
`S` and the prefix length `N`:

```text
sup_(S,N) norm(sum_(i < N) FullKernel_S(e_i)) < infinity.
```

That bound is not proved.  Gate 3U, the finite-S sign, Burnol's identity, and
`_root_.RiemannHypothesis` remain open.

## Verification

The Windows source of truth was synchronized to the Ubuntu-24.04 WSL2 ext4
mirror.  The focused Proof 741 source and audit passed with `3385/3385` jobs,
the `CCM25Concrete` aggregate with `4009/4009`, and the full repository with
`4090/4090`.

All nine audited Proof 741 theorems use exactly
`[propext, Classical.choice, Quot.sound]`.  Static checks found no `sorry`,
`admit`, user axiom, heartbeat increase, recursion-limit increase, unsafe
declaration, or line over 100 characters in the new source and audit.
