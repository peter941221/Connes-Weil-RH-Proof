# 112 — Route D universal projection-algebra contraction no-go

Date: 2026-09-27.

Status: scoped no-go. This rejects only the universal finite-dimensional
projection-algebra version of Route D; it does not reject an owner-specific
factorization for the actual selected detector.

## Screened claim

The rejected shortcut was:

```text
for every test vector x,
  Defect(x) = <A x, C A x>
  with 0 <= C <= I,
```

using only the projection and phase algebra

```text
P, H = 2P - I, U, P_hat = U^*(I-P)U,
T = U^* H U - H,
Pos = P P_hat P,
Defect = (T - P T P) / 2.
```

Any such factorization would force `Defect` to vanish on the kernel of
`Pos`, because `A^* C A` vanishes there.

## Exact counterexample

Take the following matrices with integer entries:

```text
P = diag(1,0), H = diag(1,-1), U = [[0,1],[1,0]].
P_hat = U^*(I-P)U = P.
Pos = P P_hat P = diag(1,0).
T = U^* H U - H = diag(-2,2).
Defect = (T - P T P)/2 = diag(0,1).
```

For `e_2 = (0,1)` we have `Pos(e_2) = 0` but
`<e_2,Defect e_2> = 1`. Hence no universal `C` can satisfy
`Defect = A^* C A` with `A^* A = Pos`: the right side must vanish on
`ker(A)` while the left side does not. This is exact arithmetic, not a
floating-point sign inference.

The integer-matrix calculation is the full reproducible counterexample. It
uses no discretization, numerical tolerance, or arithmetic-owner surrogate.

## Route consequence

Route D survives only in the narrower form:

```text
construct C from the actual finite-S arithmetic owner and the actual selected g,
or construct a scalar/vector certificate directly for A_g;
do not claim a universal C for all tests from P/U algebra alone.
```

No Lean consumer, parameter scan, or producer theorem is licensed by this
screen. The counterexample does not address the arithmetic owner's sign.
