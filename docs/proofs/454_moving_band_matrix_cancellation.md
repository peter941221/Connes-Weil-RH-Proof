# Proof 454: Moving-band finite-matrix cancellation

## Result

Proof 454 lifts the actual Hermitian moving-flow identity from individual
diagonal coefficients to the complete `Fin N` compression matrix.  If

```text
C_N(alpha) = M_N(actualCompletedRootCrossing(alpha)),
```

then Lean proves

```text
M_N(actualMovingSoninRootFlow(alpha))
  = -C_N(alpha) - C_N(alpha)^H,

Re Tr(M_N(actualMovingSoninRootFlow(alpha)))
  = -2 Re Tr(C_N(alpha)).
```

The five outer/Sonin/prolate branches stay inside `C_N`.  No branchwise norm,
diagonal absolute value, or infinite-dimensional trace cycle is introduced.

## Integrated endpoint

The total representative `actualCompletedRootCrossingOnUnit` agrees with the
genuine crossing on `[0,1]` and is zero outside its legal parameter interval.
The finite endpoint ledger becomes

```text
Re Tr(M_N(rootSandwichedBandResponse))
  = 2 * integral_0^1 Re Tr(C_N(alpha)) d alpha.
```

Consequently, the canonical ordinary trace consumer now only asks for

```text
abs(integral_0^1 Re Tr(C_N(alpha)) d alpha)
  <= (supportRadius + log 3)
       * (1 + supportRadius + log 3)
```

uniformly in `N`.  The Hermitian factor `2` is then restored exactly.

## Boundary

Proof 454 identifies the correct coherent scalar but does not bound it.  The
remaining analytic producer must estimate the complete crossing matrix trace
uniformly in both `N` and the visible finite prime family, preferably through
Proof 453's explicit prefix-boundary defects.  Gate 3U, the finite-`S` sign,
Burnol's identity, and `_root_.RiemannHypothesis` remain open.
