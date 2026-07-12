# 110 Xi-Null Compact-Support Zero-Density Death

Date: 2026-07-12

## Result

The exact compact-support version of Plan 030 is impossible except for the zero
test.  A nonzero compactly supported log test has a finite-exponential-type
bilateral Laplace transform, while a nonzero function divisible by completed Xi
would contain all nontrivial zeta zeros.  The zero densities are incompatible.

This rejects exact compact `Xi * R * A` corrections as a route mechanism.  It
does not reject noncompact analytic deformations, but truncating those
deformations necessarily loses exact zero preservation and returns the problem
to a quantitative prime/tail estimate.

## Proof Skeleton

Let `h` be a nonzero smooth function supported in `[-L,L]` and define

```text
H(s) = integral_R exp(s*x) h(x) dx.
```

Then

```text
|H(s)| <= ||h||_1 exp(L*|Re(s)|) <= ||h||_1 exp(L*|s|).
```

Thus `H` is entire of finite exponential type.  Jensen's formula applied to a
disk of radius `2T` gives an upper bound

```text
number of zeros of H in |s| <= T = O_h,L(T).
```

The same conclusion holds if finitely many zeros at the origin are first
factored out.

If `H=Xi*R*A` with `H` nonzero, every nontrivial zeta zero is a zero of `H`,
with at least its Xi multiplicity.  The Riemann--von Mangoldt count gives

```text
N_zeta(T) = T/(2*pi) * log(T/(2*pi)) - T/(2*pi) + O(log T),
```

so `N_zeta(T)` is not `O(T)`.  This contradicts the finite-type bound.

Sources for the zero-count asymptotic:

```text
NIST DLMF 25.10, Riemann--Siegel and zero-count discussion:
https://dlmf.nist.gov/25.10
Riemann--von Mangoldt formula overview:
https://mathworld.wolfram.com/Riemann-vonMangoldtFormula.html
```

## Consequence For Plan 030

The formal deformation

```text
H_new = H_rho + Xi*R*A
```

can preserve all zero values in a noncompact transform class.  But the source
route requires a compact smooth test for the finite-prime formula and CC20
trace.  A compact cutoff of `H_new` no longer vanishes at all zeta zeros.  The
error is not a harmless API issue: it is the analytic content of the route.

The derivative-row independence in proof 103 remains a valid local fact, but it
cannot be promoted to an exact compact source owner.  Any reopening must prove
a quantitative approximate-zero theorem with a complete prime/tail estimate;
it may not store exact Xi divisibility after cutoff.

## Verdict

```text
exact compact Xi-null correction: rejected
noncompact Xi deformation: mathematically possible, not a source test
compact truncation with exact zero preservation: impossible
Plan 030 as stated: rejected as an executable route
RH: unproved
```

