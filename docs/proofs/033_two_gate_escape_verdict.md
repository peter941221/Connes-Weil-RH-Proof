# Two-Gate Escape Verdict

Date: 2026-07-12

Status: Gate 1 remains alive and has a finite/infinite prime proof split. The
cross-spectral candidate at Gate 2 is rejected as the active source-backed
object. A different one-sided Sonin/negative-spectrum trace survives. RH
remains unproved.

## 1. Gate Map

```text
Gate 1: fixed-q Schur transfer
  exact owner: SU(1,1) Poisson Gram operator
  missing theorem: B(1/p) != 0

Gate 2: positive trace -> semilocal Weil inequality
  rejected candidate: ||Pi_- C_g Pi_+||_HS^2
  surviving candidate: Tr(C_g* S_S C_g)=||S_S C_g||_HS^2
```

These are different obligations. Gate 1 controls the arithmetic deformation
of the semilocal Jacobi/prolate operator. Gate 2 must identify the positive
functional consumed by the Weil exit on the same test.

## 2. Gate 1 Escape

Plan 032 reduces the Jacobi deformation to

```text
log s_n(q)
  = log sigma(q)
    + n^(-1/2) Re(B(q) exp(i n omega_p))
    + O(n^-1),

omega_p=4 arctan(tanh(log(p)/2)).                         (T.1)
```

The classical squeeze crosses the number-action boundary at

```text
tan(theta)^2=p.                                          (T.2)
```

The crossings are transverse for every finite prime. Thus local stationary
symbols do not vanish; only cancellation between the crossing contributions
can make `B(q)=0`.

The source first variation proves

```text
B'(0)=2 sqrt(2/pi)>0                                     (T.3)
```

after fixing the phase convention in (T.1). Guarded fits through degree 513
give positive real parts for `B(1/p)` at `p=2,3,5,7,11`, and the ratio
`B(q)/q` approaches (T.3).

The viable proof split is:

```text
analytic crossing parametrix
  -> B(q) analytic and an explicit |B(q)-B'(0)q| bound
  -> all sufficiently large primes
  -> finitely many small prime interval certificates.
```

Analyticity without an explicit remainder does not cover the small primes.

Gate 1 verdict: alive.

## 3. Why The Cross-Spectral Gate Is The Wrong Active Object

CCM24 only proposes that positive/negative prolate spectral orthogonality may
provide automatic conditioning. It explicitly leaves self-adjoint domains
formal and supplies no cross-spectral trace formula:

```text
mainc2m24fine.tex:197-205
  states the strategy and calls the domain delicate/formal.

mainc2m24fine.tex:286-290
  defines only a formal prolate operator for a cyclic pair.
```

Source: https://arxiv.org/abs/2310.18423

The natural whole-line prolate extension does not have a finite positive
projection. Connes--Moscovici prove that its spectrum is discrete and
unbounded in both directions:

```text
Draft2.tex:590-632, Theorem thmwsa.
```

They also identify the positive ultraviolet spectrum with the trivial-zero
side and the negative eigenvectors with Sonin space:

```text
Draft2.tex:230-268 and 978-987.
```

Source: https://arxiv.org/abs/2112.05500

The exact-Jacobi finite-section screen confirms the expected infinite channel.
At `lambda=1`, the number of positive finite-section eigenvalues grows

```text
section:       64   96   128   192   256   384   512
positive rank: 26   32    36    44    52    62    72
```

For the bare translation at `r=log 2`, the cross energy grows from about
`4.29` to `18.31`. Therefore the unsmoothed kernel is not a finite positive
trace and cannot itself converge to a finite Weil scalar.

For fixed Schwartz multipliers such as `exp(-tau D^2)`, finite sections show
the opposite danger: after the correct smoothing, the cross energy rapidly
falls toward zero as `lambda` grows. This is not a proof because the infinite
section and large-`lambda` limits do not automatically commute, but it removes
the numerical support for the proposed nonzero cross-to-Weil limit.

The decisive source issue is simpler: neither CC20 nor CCM24 names
`||Pi_- C_g Pi_+||_HS^2` as the Weil-positive trace. The project introduced it
to remove rank bulk. It must not remain the active route merely because it is
positive.

Cross-spectral verdict: rejected as the current source-backed route; no claim
is made that every possible renormalized cross-energy theorem is false.

## 4. Source-Backed Gate 2 Escape

CC20 identifies the positive functional as a one-sided compression to Sonin
space. If `S` is the orthogonal Sonin projection and `f=g*g*`, then

```text
Tr(rho(f) S)
  = Tr(rho(g) rho(g)* S)
  = Tr(rho(g)* S rho(g))
  = ||S rho(g)||_HS^2 >= 0.                              (T.4)
```

This is stated explicitly in `weil-compo.tex:113-114`. More strongly, for the
archimedean support interval and the vanishing conditions, CC20 proves

```text
W_infinity(g*g*)
  >= Tr(rho(g) S rho(g)*).                               (T.5)
```

Source: `weil-compo.tex:124-136`, Theorem `mainthmintro`, and
https://arxiv.org/abs/2006.13771

The exact trace read-off is not equality with the Weil term. CC20 proves

```text
Tr(rho(f) S)=W_infinity(f)+E(f),                         (T.6)
```

where `E` is an explicit prolate/Sonin remainder; see
`weil-compo.tex:1130-1199`. Their Toeplitz conditioning proves the inequality
(T.5), not a false no-remainder identity.

For finite `S`, the surviving candidate is therefore

```text
Pos_S(g)=Tr(C_S(g)* S_S C_S(g)),                         (T.7)
```

where `S_S` must be the orthogonal semilocal Sonin projection or a proved
negative-prolate spectral projection with the same range after explicitly
accounting for its finite-dimensional discrepancy.

Unlike the rejected asymptotic cross object, (T.7) is evaluated at the fixed
support cutoff of the same test. Prime-power atoms may enter through the exact
semilocal trace formula; no continuous-kernel-to-Dirac exhaustion is required.

## 5. The Two New Death Tests

The replacement does not solve Gate 2. It names the right theorem:

```text
G2-A  Same-object spectral/Sonin theorem
      The selected self-adjoint W_(S,lambda) has a negative projection whose
      range is S_S plus an explicitly controlled finite-dimensional space.

G2-B  Semilocal CC20 inequality
      QW_S(g,g) >= Tr(C_S(g)* S_S C_S(g))
      for every route test with the required vanishing and support.
```

The easiest rejection point is G2-B at `S={infinity,2}`. One must derive the
semilocal analogue of the remainder `E` in (T.6) and test whether its
post-`Q` operator has only finitely many bad directions. If the finite Euler
translation block remains noncompact and positive on infinitely many
directions, the Sonin escape is dead and finite-dimensional prolate
conditioning cannot repair it.

This test is strictly lower than assuming the Weil inequality: it computes
the sign and ideal class of one explicit same-object remainder.

## 6. Verdict

```text
Gate 1 Schur--Cayley: alive.
Gate 1 escape: analytic large-prime bound + finite small-prime certificates.

Gate 2 cross-spectral transition: rejected as active route.
Gate 2 Sonin/negative one-sided trace: alive and source-backed.
Gate 2 next bottom: fixed-S semilocal Sonin remainder ideal/sign.

RH: unproved.
```

The next priority is G2-B for one prime. It can kill the replacement quickly,
whereas proving the full self-adjoint semilocal prolate theory before knowing
the remainder sign would be wasted work.

## 7. Post-Verdict Unification

CCM24's bounded nonunitary Sonin isomorphism gives a sharper realization of
the surviving one-sided trace. If `T_S=theta_S`, `H_S=T_S* T_S`, and `R` is
the archimedean Sonin projection, then

```text
R_S=T_S R(R H_S R)^-1 R T_S*
```

is the orthogonal semilocal Sonin projection. Here `H_p=|1-p^-1/2 U_p|^2`, so
the inverse compressed metric is exactly the Wiener--Hopf object exposed by
Gate 1. This bypasses the formal semilocal prolate extension and unifies both
gates. The remaining one-prime remainder test is unchanged. See
`docs/proofs/034_metric_sonin_projection_escape.md`.
