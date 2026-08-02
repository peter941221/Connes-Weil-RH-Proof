# Proof 737: Gate Physical Prefix Root Pairing

## Result

Proof 737 opens the genuine positive detector square inside Proof 736's finite
functional.

The repository's selected detector is literally

```text
W = C_h^dagger C_h,

C_h = cc20GlobalLogConvolution
        owner.sourceTest.involution.test.
```

Therefore every ambient matrix coefficient satisfies

```text
<a,W b> = <C_h a,C_h b>.
```

For one ordered source-basis prefix, Lean defines the complete root pairing

```text
R_(S,N)
  = sum_(i < N)
      [<C_h(J e_i),C_h(U_S e_i)>
        + <C_h(F_S e_i),C_h(J e_i)>].
```

It then proves the exact chain

```text
Gate prefix compression trace
  = physical detector functional evaluated at W
  = R_(S,N).
```

The fixed-family consumer now needs only

```text
forall N, norm(R_(S,N)) <= C
```

to bound the ordinary Gate trace; the existing common-boundary
Hilbert--Schmidt pair data supplies trace legality.

## Why This Matters

Compact root support is now present before any absolute value:

```text
         complete family-dependent boundary pair
                         |
                         v
              apply the same root C_h
                         |
                         v
             finite signed root inner products
                         |
                         | only here seek one bound
                         v
                   Gate 3U consumer
```

No detector operator norm, functional norm, or separate root-leg norm appears
in the theorem contract.  This preserves cancellation between endpoint
residual and reverse-forward coordinates.

## Guard

Do not apply Cauchy--Schwarz term by term to the two displayed inner products,
and do not sum their absolute values.  That would recover the direct-sum
Hilbert--Schmidt estimate rejected by the Gate 3U guards.  The next producer
must use compact support and the physical endpoint geometry on the complete
finite root pairing.

Proof 737 does not prove the uniform root-pairing bound.  Gate 3U, the finite-S
sign, Burnol's identity, and `_root_.RiemannHypothesis` remain open.

## Verification

The combined Proof 735--737 source/audit batch passed with `4008/4008` jobs.
The final full-repository acceptance build after Proof 738 passed with
`4087/4087` jobs.  All five audited Proof 737 theorems use exactly
`[propext, Classical.choice, Quot.sound]`.  No `sorry`, `admit`, user axiom,
heartbeat increase, recursion-limit increase, overlong line, or new linter
warning was added.
