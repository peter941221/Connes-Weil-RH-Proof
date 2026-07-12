# 109 Burnol Alignment For The Selected Weil Formula

Date: 2026-07-12

## Result

The selected fixed-square arithmetic owner passes the exact classical
normalization audit.  For its additive log square `f`, set

```text
g(u)=u^(-1/2)f(log u).
```

Burnol's explicit formula then reads

```text
SelectedWeilFormulaOwner.weilValue
  = sum_over_nontrivial_zeros Laplace_f(rho-1/2),
```

with the same pole, finite-prime, and archimedean conventions.  This is a
mathematical identification of the intended theorem statement, not a Lean
proof currently present in the repository.

## Exact Terms

The substitution `u=exp(x)` gives

```text
gHat(s)=Laplace_f(s-1/2).
```

Hence the pole side is exactly

```text
gHat(0)+gHat(1)=Laplace_f(-1/2)+Laplace_f(1/2).
```

For `n=p^k`, Burnol's local term is

```text
log(p)[g(p^k)+p^(-k)g(p^(-k))]
  = vonMangoldt(n)n^(-1/2)
      [f(log n)+f(-log n)],
```

after summing over prime powers.  This is exactly `finitePrimeTerm`.

At infinity, rewriting Burnol's geometric series produces the repository
integrand except for

```text
-2f(0)/(exp(y)+1).
```

Its integral is `-2 log(2)f(0)`, while the repository constant exceeds
Burnol's by `log(4)f(0)=2 log(2)f(0)`.  The two changes cancel.

## Source Evidence

Burnol states

```text
gHat(0)+gHat(1)-sum_rho gHat(rho)=sum_nu W_nu(g)
```

and notes that for smooth compactly supported tests every sum and integral is
absolutely convergent.  The derivation uses the zeta/Gamma functional equations
and Hadamard product data, not RH or the prime number theorem.

Primary source:

```text
Jean-Francois Burnol, The Explicit Formula in Simple Terms,
arXiv:math/9810169v2, pp. 3-4, 10-11.
https://arxiv.org/pdf/math/9810169
```

Repository definitions:

```text
ConnesWeilRH/Source/CCM25Concrete/SelectedWeilSquare.lean:67-78
ConnesWeilRH/Source/CCM25Concrete/SelectedWeilFormula.lean:75-86
ConnesWeilRH/Source/CCM25Concrete/SelectedWeilFormula.lean:94-154
ConnesWeilRH/Source/CCM25Concrete/SelectedWeilFormula.lean:233-237
```

## Formalization Audit

Mathlib supplies the von Mangoldt logarithmic derivative on `Re(s)>1`, basic
logarithmic-derivative calculus, and complex integral foundations.  The project
supplies an analytic completed Xi function, its functional equation, divisor
counting, and compact-test vertical decay.

The current dependency tree has no ready theorem for the Riemann-zeta Hadamard
product/logarithmic-derivative zero expansion and no directly reusable residue
theorem closing Burnol's contour shift.  The missing equality is therefore a
real formalization project rather than a field read-off.

## Route Consequence

This pass removes a possible sign/normalization death.  It does not close Plan
028.  The remaining CC20 M4 sign is archimedean, whereas a growing Xi-quotient
cutoff sees finite primes.  A same-object finite-S remainder sign or a
prime-free fixed-window negative detector remains necessary.

```text
classical same-square identity: valid target
Lean theorem in repository: absent
normalization/sign mismatch: none
finite-S CC20/M4 sign: open and decisive
route Lean: not authorized
RH: unproved
```

