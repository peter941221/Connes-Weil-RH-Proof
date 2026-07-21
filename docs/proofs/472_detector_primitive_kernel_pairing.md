# Proof 472: Detector primitive kernel pairing

## Result

Proof 471 reduced the outer and reflected-outer coordinates to the abstract
legs of one `translatedCompactRootPairData`.  Proof 472 unfolds those legs to
their actual compact `Lp` continuous-kernel operators.

Write `T` for translation by `log(lambda)`.  The two legs are

```text
N = operator(negativeBoundaryRootKernel)
      o negative-window restriction o T,

P = operator(positiveBoundaryRootKernel)
      o positive-window restriction o T.
```

Both land in the same output carrier `L2([-c,-a])`.  For the source prefix
`L=E Q`, Lean proves that the complete outer/reflected scalar is

```text
 <P(L^dagger x),N(y)> - <N(L^dagger x),P(y)>
-<N(x),P(L^dagger y)> + <P(x),N(L^dagger y)>.
```

The atom trace is one global-basis `tsum` of this four-term scalar plus the
still-coupled second-support/prolate remainder.  No abstract pair leg remains
in the primitive outer contribution, and no absolute value or branchwise
trace is introduced.

## Boundary

The inputs of these kernel operators are arbitrary `L2` vectors after
projection and translation.  Existing pointwise set-integral lemmas apply on
the Schwartz core only, so Proof 472 stops at the exact continuous-kernel
operator formula rather than asserting an unsupported pointwise identity.

Compact-support cancellation of the completed four-term scalar, control of
the coupled second-support/prolate kernel, renewal trace exchange, the uniform
Gate 3U bound, the finite-S sign, Burnol's identity, and
`_root_.RiemannHypothesis` remain open.
