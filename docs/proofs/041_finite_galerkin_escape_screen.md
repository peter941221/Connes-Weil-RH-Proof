# Finite Galerkin And Herglotz Escape Screen

Date: 2026-07-12

Status: the 2026 finite Guinand--Weil dictionary supplies a useful exact
finite-dimensional coordinate system, but neither positivity of all cutoff-free
Galerkin matrices nor the scalar Herglotz condition is a lower producer for RH.
Both retain the full Weil-positivity obstruction. RH remains unproved.

## 1. Result First

```text
finite vector -> exact Weil test: accepted
archimedean cutoff tail is positive: accepted
finite-cutoff negative eigenvalues inside the tail budget: rejected evidence
all cutoff-free finite matrices are positive: RH-level
odd-sector scalar Herglotz inequality for every support: RH-level
new unconditional RH producer: none
```

This screen prevents two numerically attractive finite statements from being
used as if they were independent arithmetic estimates.

## 2. Exact Finite Dictionary

For a prime cutoff `c>1`, frequency band `N`, and real even Galerkin vector
`v`, Groskin constructs an explicit band-limited Guinand--Weil test `g_v` and
proves

```text
<v,Q_infinity v> = sum_(zeta(1/2+i z)=0) g_v(z),
```

with multiplicity and an absolutely convergent zero sum. The construction is
finite and inverse-free. The source dependence factors through exactly
`2N+1` coordinates.

Source: A. Groskin, *A finite Guinand--Weil dictionary and archimedean tail
order for the truncated Weil quadratic form*, arXiv:2607.02828, Theorem 2.5
and Corollary 2.4:

```text
https://arxiv.org/abs/2607.02828
```

This is a legitimate replacement for ad hoc finite matrix interpretations: a
matrix quadratic value is the exact Weil form of one named test. It is not a
positivity theorem.

## 3. Positive Archimedean Tail

The same paper proves that for

```text
T2 > T1 > max(rho*N,7),
```

the omitted archimedean increment has a rank-two Cauchy--Stieltjes Gram
representation and is strictly positive definite. Corollary 3.3 gives

```text
0 <= Q_infinity-Q_T <= B_T Id,
B_T asymptotic to (2N+1)rho(log(T/(2pi))+1)/(pi^2 T).
```

Therefore:

```text
Q_T >= 0                    -> Q_infinity > 0,
lambda_min(Q_T) < -B_T      -> Q_infinity has a negative direction,
-B_T <= lambda_min(Q_T) < 0 -> no sign conclusion.
```

This rejects finite-cutoff negative eigenvalues that lie inside the omitted
tail budget. It does not prove the sign of `Q_infinity`.

## 4. Why Positivity Of Every Finite Matrix Is Circular

The dictionary sends every finite vector to an admissible Weil test. As `c`
and `N` vary, positivity of all matrices asserts Weil positivity on the union
of these finite test cones. To use this as an RH route one must additionally
prove that this union is determining for the full Weil cone. After that density
step, the assertion is precisely a finite-dimensional exhaustion of Weil's RH
criterion, not a lower arithmetic estimate.

The source itself states the boundary: the dictionary is one-way and claims no
inverse map from arbitrary tests; it makes no RH or Weil-positivity claim. See
arXiv:2607.02828, Section 4, "Verification and scope".

No route API may store

```text
forall c N, PositiveSemidefinite(Q_infinity(c,N))
```

as source data. With a determining-family theorem it implies RH; without that
theorem it is too weak to close the route.

## 5. Herglotz Reduction Does Not Lower The Bottom

The localized Weil form splits by parity. In the notation of Andrade's 2026
Herglotz reduction,

```text
A_even = B_even + 2 |C><C|,
A_odd  = B_odd  - 2 |S><S|,
```

where the pole-free odd operator `B_odd` is positive. The unresolved condition
is the rank-one resolvent inequality

```text
<S,(B_odd-lambda_even)^(-1)S> < 1/2.
```

Source:

```text
https://zenodo.org/records/20694588
https://zenodo.org/records/20682834
```

The first source explicitly says that it reduces even-simplicity to this scalar
condition but does not prove it. The second identifies the general-support
nodal/resolvent inequality as open.

More importantly, Yoshida proves that odd positive definiteness of the Weil
distribution is equivalent to RH. Source: H. Yoshida, *On Hermitian Forms
attached to Zeta Functions*, Proposition 1(1), pp. 284--287:

```text
https://projecteuclid.org/ebooks/advanced-studies-in-pure-mathematics/
Zeta-Functions-in-Geometry/chapter/On-Hermitian-Forms-attached-to-Zeta-
Functions/10.2969/aspm/02110281.pdf
```

Thus a uniform proof that the negative odd rank-one pole perturbation remains
positive for every support interval would prove the RH-equivalent odd Weil
criterion itself. The scalar form is useful for locating the obstruction, but
it is not a lower producer.

## 6. Yoshida Quantifier Audit

Yoshida Lemma 1 constructs a detector by:

```text
choose a base test a0 normalized at rho0
choose R from the far decay of a0
interpolate every zero inside R
bound the finite correction product by C on the strip
take an unrestricted convolution power N large enough
```

The support grows with `N`. The proof therefore has no radius/count cycle.
Plan 016 introduced that cycle by rescaling every base factor to keep one fixed
narrow support window. The rescaling moves the far-tail threshold to order
`N*T`, after the nearby interpolation radius was fixed.

Consequently the honest dichotomy is:

```text
fixed narrow support
  -> archimedean CC20 sign is available
  -> Yoshida's unrestricted-power detector proof no longer applies;

growing support
  -> Yoshida's detector proof applies
  -> a genuine finite-S/global positivity theorem is required.
```

The finite Galerkin dictionary does not remove this dichotomy; its bandwidth
grows with `log c`.

## 7. Remaining Honest Bottoms

Only two non-circular mathematical attacks remain visible from the checked
sources:

```text
A. Construct the global fixed-S post-Q trace identity and explicit residual
   kernel on the compact test-root Hilbert space, then prove its sign.

B. Prove the cutoff-free finite Weil matrices positive through a new arithmetic
   inequality that is strictly lower than their zero-sum/RH interpretation.
```

For B, the proof may use explicit prime, pole, and Gamma blocks, but must not
assume zero-side positivity, the determining-family conclusion, the odd Weil
criterion, or the unresolved Herglotz inequality itself.

## 8. Route Judgment

```text
2607.02828 finite dictionary: accepted as exact coordinate evidence
2607.02828 tail order: accepted as a numerical rejection guard
finite matrix positivity as root: forbidden / RH-level
scalar Herglotz condition as root: forbidden / RH-level
Plan 024 metric proxy: remains rejected
RH: unproved
```

The cutoff-free block cancellation experiment in
`docs/proofs/044_cutoff_free_weil_cancellation_verdict.md` further rejects
fixed-margin and separate block-norm proof shapes. Tested positive Rayleigh
margins fall below `10^-53` while the pole, Gamma, and prime contributions
remain of order one.
