# Proof 410: continuous weighted-gradient attempt

Date: 2026-07-19

Status: minimal theorem contract and rejection split for the continuous Gate
3U gradient.  The raw linear prime-log Hilbert--Schmidt route is rejected by
the exact coherent-cluster obstruction of Proof 348.  The complete nonlinear
inverse-after-average Burnol owner remains the analytic target, but Proof 411
withdraws the non-periodic numerical screen as under-resolved and its uniform
estimate is not proved.

## 1. Minimal theorem

Let `M(z)=A* U_z A` be the actual Burnol boundary moment and let `nu_S` be the
normalized complete Euler inverse law.  For a compact `Q`-completed detector
`F=Q phi`, define

```text
G_S       = integral M(z) d nu_S(z),
N_S(F)   = integral_z integral_u F(u) M(z+u) du d nu_S(z),
G_0       = M(0),
N_0(F)   = integral_u F(u) M(u) du.
```

The single continuous root-relative theorem needed for the near lane is

```text
abs Tr[G_S^(-1) N_S(F_near) - G_0^(-1) N_0(F_near)]
 <= C (1+B_root)^d ||g||_(H^r)^2,                  (CG.1)
```

with a constant independent of the finite visible prime set.  The full Gate
bound follows by adding Proof 336's far tail before taking the final absolute
value.  Proof 408 verifies the finite weighted determinant derivative that
reads back to the same scalar; Proof 405 supplies the physical two-branch
first-jet form.

## 2. Conditional proof skeleton

The only valid proof order is

```text
weighted relative determinant
  -> exact derivative / Proof 405 first jet
  -> complete nonlinear Euler inverse average
  -> root-supported near/far split
  -> far residue cancellation and Proof 336 remainder
  -> nonlinear near estimate (CG.1)
  -> one final absolute value.                        (CG.2)
```

The near estimate must retain `G_S^(-1)` after the full average.  It cannot be
replaced by an average of pointwise inverses, a norm of `log(tau_S)`, or a sum
of primewise trace norms.

## 3. Rejected proof attempt: linearized Euler log

For a compact root `g` and a half-line crossing `A_z`, the exact Gram identity
is

```text
<C_g A_z,C_g A_w>_(S2)
  = min(z,w) Gamma_g(w-z).
```

A short prime-log cluster therefore has coherent off-diagonal mass.  Proof
348 proves, unconditionally,

```text
||C_g sum_(p in [X,(1+epsilon)X]) p^(-1/2) A_(log p)||_2^2
  >= c X/log X,
```

while the diagonal Proof 344 Szego energy for the same cluster is `O(1)`.
Therefore the following implication is invalid:

```text
atomic diagonal energy
  -> root-smoothed S2 perturbation
  -> Koplienko / Cauchy--Schwarz
  -> Gate 3U.
```

This rejects only the linearized owner.  It does not reject `(CG.1)` because
the complete nonlinear product, quotient inverse, Sonin branch, prolate term,
and half-density cancellation are absent from the linearized crossing.

## 4. Actual Burnol screen

Proof 409 evaluates `(CG.1)` approximately using the non-periodic even cosine
transform on `[0,1]`, direct moment evaluation without displacement
interpolation, and the binned complete geometric-difference law.  For
`B_root=1`, `grid_step=0.2`, and the `size=8,10` cohorts with
`maximum_power=18`, the near response stabilizes as the visible prime set
grows.  The `size=12,14` rows use `maximum_power=12` to avoid overflow in the
far geometric support and are a lower-precision cross-check:

```text
+------+----------------------+----------------+----------------+
| size | visible primes       | near response  | normalized     |
+------+----------------------+----------------+----------------+
|  8   | 2,3,5                | -10.19992      | 0.2465         |
|  8   | 2,...,13             | -23.50182      | 0.5680         |
|  8   | 2,...,43             | -23.50371      | 0.5681         |
| 10   | 2,3,5                | -26.07656      | 0.6303         |
| 10   | 2,...,13             | -28.99543      | 0.7008         |
| 10   | 2,...,43             | -28.99806      | 0.7009         |
| 12   | 2,...,13             | -33.50481      | 0.8098         |
| 12   | 2,...,43             | -33.57667      | 0.8115         |
| 14   | 2,...,13             | -37.35474      | 0.9029         |
| 14   | 2,...,43             | -37.40902      | 0.9042         |
+------+----------------------+----------------+----------------+
```

The response is sensitive to the Burnol Galerkin size because the fixed source
Gram has condition about `7e4`.  Proof 411 later shows that prime-set
stabilization is not meaningful evidence here: every row reuses an
under-resolved far metric which fails the Hermitian/positive-semidefinite
sanity check.  The table is historical output only, not a converged continuum
value.

## 5. Remaining analytic lemma

The next source-specific theorem must prove a nonlinear, detector-first
Carleson/Szego estimate for the exact Burnol moment:

```text
sup_S |Tr[G_S^(-1) N_S(F_near)]|
  <= C (1+B_root)^d ||g||_(H^r)^2,                  (CG.3)
```

with the source inverse controlled only after the complete Euler average.  A
successful proof may use a determinant-line convexity argument, a causal
Schur cocycle, or an equivalent nonlinear orthogonalization.  It must reproduce
the two physical branches of Proof 405 and the residue subtraction of Proofs
334--336.  No generic probability-law bound is sufficient because Proof 254's
two-state guard remains applicable.

## 6. Route judgment

```text
weighted determinant -> Proof 405 first jet       closed finitely;
raw linear S2/Koplienko route                     rejected;
complete nonlinear Burnol near response           unverified finite screen;
uniform nonlinear estimate (CG.1)/(CG.3)          open;
Gate 3U / finite-S sign / Burnol / RH              open / open / open / open.
```

## 7. Numerical-status correction

Proof 411 found that the complete metric used by the Proof 409 numerical
screen is under-resolved in its far cosine tail.  Its finite matrices fail the
Hermitian/positive-semidefinite sanity check, and the displayed response is
not stable under quadrature refinement.  Consequently the phrase
"numerical survivor" in Section 4 is not certified evidence; it must be read
as an unresolved experiment.  The nonlinear estimate `(CG.1)` remains open,
and no continuous obstruction has been established.
