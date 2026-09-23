# 1896 - Orientation-independent C3' sign consumer

Date: 2026-09-23.

Status: formally verified in Lean. This extends a conditional same-owner B5
consumer; it proves no detector sign estimate and no RH statement.

The two-span determinant consumer previously required the negative/positive
Archimedean and prime diagonal signs in the order `(u, v)`. The phase-swap
identities from record 1895 now allow the signs in either order while keeping
the optimal q-form pivot fixed on `v`:

```text
(A_u <= 0 <= A_v and P_u <= 0 <= P_v)
  or
(A_v <= 0 <= A_u and P_v <= 0 <= P_u)

and 0 <= A_pair * P_pair

imply the same ordered (u, v) two-span phase budget <= 0.
```

In the reversed branch, apply the existing determinant estimate to `(v, u)`.
The phase-swap identities then return that budget to `(u, v)`. Since the
optimal-qform consumer is applied only after this normalization, its positive
pivot hypothesis remains `0 < ICgate((carrierModulate gamma v).square)`;
there is no implicit pivot exchange.

Verification: focused WSL build `c3-order-1896a.log`; successful footer for
3788 jobs, zero `error:` lines, zero `sorryAx`, and both new Audit declarations
use only `[propext, Classical.choice, Quot.sound]`.

The actual selected detector still has to provide one of the two diagonal sign
patterns and the directed pair-product sign on its own finite visible-prime
owner. The C3' semi-local positivity target and RH remain open.
