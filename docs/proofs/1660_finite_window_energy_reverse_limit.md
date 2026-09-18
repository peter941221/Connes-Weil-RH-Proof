# 1660 — finite-window energy reverse limit

## Result

The new theorem `summable_normSq_of_uniform_finite_window_energy` formalizes
the reverse-limit step needed by the detector-specific S3 route.  Let `T` be
the source-side operator and let `E_n` be expanding output-window operators.
If

1. `E_n (T x)` converges strongly to `T x` for every input `x`, and
2. there is one real constant `B` such that every finite set of basis columns
   satisfies `sum_i ||E_n (T e_i)||^2 <= B`, uniformly in `n`,

then the full column family `||T e_i||^2` is summable.

The proof passes the strong limit through each finite sum and applies
Mathlib's nonnegative finite-sum criterion `summable_of_sum_le`.  The audit
build completed with 3215 jobs, zero errors, zero `sorryAx`, and only the
standard axioms `[propext, Classical.choice, Quot.sound]`.

## Route meaning

This does not prove the missing survivor-core estimate.  It changes its exact
form.  The live producer is now a uniform finite-window bound for the
source-compressed root columns.  The already formal strong convergence of
expanding interval projections supplies the limit hypothesis; the remaining
mathematics is the window-independent bound, including the infinite radial
tail.  No RH conclusion is claimed.
