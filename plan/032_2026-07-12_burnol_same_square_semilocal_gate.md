# 032 Burnol Same-Square Formula And Semilocal Gate

Date: 2026-07-12

Status: normalization passed; prime-free branch rejected by proof 113;
finite-S sign gate remains; route Lean denied.

## Objective

Decide whether the fixed-detector route can turn one hypothetical off-critical
zero into a contradiction without importing global Weil positivity.  Keep the
same compact log square through all three layers:

```text
source zero sum
  = SelectedWeilFormulaOwner.weilValue
  = QW of the same square
  -> fixed-test CC20/M4 sign contradiction.
```

This plan does not authorize a route owner, a stored spectral equality, or a
finite-S compact remainder premise.

## Gate 1: Exact Burnol Dictionary

Let `f` be the selected additive log-coordinate convolution square and define
the multiplicative test

```text
g(u) = u^(-1/2) f(log u).
```

Burnol uses

```text
gHat(s) = integral_0^infinity g(u) u^s du/u.
```

The change of variables `u=exp(x)` gives

```text
gHat(s) = integral_R exp((s-1/2)x) f(x) dx.
```

Therefore Burnol's two pole evaluations are exactly the selected owner fields:

```text
gHat(0)+gHat(1) = laplaceAt(-1/2)+laplaceAt(1/2).
```

For `n=p^k`, the finite-place term is also exact:

```text
log(p) [g(p^k)+p^(-k)g(p^(-k))]
  = log(p) p^(-k/2)
      [f(k log p)+f(-k log p)].
```

Summing over prime powers is precisely the repository's von Mangoldt-weighted
`finitePrimeTerm`.

The archimedean expressions look different but agree.  Burnol's formula becomes

```text
(log(pi)+gamma) f(0)
  + integral_0^infinity
      [exp(y/2)(f(y)+f(-y))-2 exp(-y)f(0)]
      /(exp(y)-exp(-y)) dy.
```

The selected owner instead uses `log(4*pi)+gamma` and replaces
`-2 exp(-y)f(0)` by `-2f(0)`.  Their integral difference is

```text
-2 f(0) integral_0^infinity 1/(exp(y)+1) dy
  = -2 log(2) f(0),
```

which cancels the constant difference `log(4)=2 log(2)`.  Thus the
normalization and signs agree exactly.

Primary source:

```text
Jean-Francois Burnol, The Explicit Formula in Simple Terms,
arXiv:math/9810169v2, pp. 3-4 and the convolution-algebra theorem on pp. 10-11.
https://arxiv.org/pdf/math/9810169
```

Repository evidence:

```text
Source/CCM25Concrete/SelectedWeilSquare.lean:67-78
Source/CCM25Concrete/SelectedWeilFormula.lean:75-86
Source/CCM25Concrete/SelectedWeilFormula.lean:94-154
Source/CCM25Concrete/SelectedWeilFormula.lean:233-237
```

Verdict: pass.  `SelectedWeilFormulaOwner.weilValue` has the correct classical
shape for the same-square zero sum.

## Gate 2: Formalization Bottom

The theorem is unconditional mathematics, but the current Lean stack does not
already contain its proof.  The available ingredients include:

```text
LSeries_vonMangoldt_eq_deriv_riemannZeta_div on Re(s)>1
basic logDeriv lemmas
analytic completedRiemannXi and its functional equation
Jensen/divisor counting for completedRiemannXi
rapid vertical decay for compact Mellin tests.
```

The audit found no reusable Riemann-zeta Hadamard product, completed-Xi
logarithmic-derivative zero expansion, or general residue theorem that directly
turns the contour shift into the zero sum.  Proving the spectral identity is
therefore a substantial complex-analysis/library lane, not a wrapper theorem.

Verdict: mathematically valid but not the first route implementation target.
Do not spend that cost until Gate 3 survives.

## Gate 3: Decisive Semilocal Sign

For the archimedean CC20 remainder, M4 gives

```text
D_infinity(Q(xi*xi*)) = <xi,(-2 Id+K_I)xi>
```

and finite-dimensional bad-space orthogonality makes this strictly negative.
This controls the full selected Weil value only when no finite prime is visible.

The Xi-quotient detector is obtained by a growing physical cutoff.  Once its
square reaches `log 2`, finite-prime terms enter.  The required identity then
uses a finite-S remainder `D_S`, not `D_infinity`.  Existing source work does
not prove that the finite-place correction preserves the `-2 Id + compact`
form.  The raw finite Euler phase has noncompact partial translations, and the
metric-projection repair is rejected by the wrong second-prime-power
coefficient.

Thus the next death test is exactly:

```text
Can one keep the negative Xi detector inside a prime-free support window,
or derive a same-object finite-prime main-term subtraction whose remaining
post-Q operator is -2 Id + compact with the correct coefficient for every p^m?
```

Failure of both branches rejects Plan 028 as an executable route even after the
classical explicit formula is formalized.

The original CCM24 source audit confirms that the finite-S inequality is not
already available under another name. Its introduction calls semilocal Weil
positivity a program and defers a second semilocal prolate candidate; the
proved `theta_S`/Sonin isomorphism supplies only domain transport. See proof
112. Do not turn those transport theorems into a positive trace premise.

## Execution Order

1. Reject or prove a fixed prime-free-window Xi detector with strict negative
   zero sum and the M4 finite constraints.
2. If that fails, audit source-backed finite-S identities only; reject any
   construction that assumes compactness after leaving a prime translation in
   the remainder.
3. Require the coefficient `p^(-m/2)/m` before the crossing length
   `m log(p)` for every prime power, especially `m=2`.
4. Only after one branch passes, formalize the Burnol spectral identity on
   `SelectedWeilFormulaOwner`.
5. Then build a standalone fixed-detector contradiction before touching the
   broad route API.

The first branch is now rejected by Plan 035/proof 113. On the M4 complement,
the corrected prime-free trace identity itself gives `QW >= ||xi||^2`; no
negative detector can remain after those constraints. The only surviving
branch is a new finite-S remainder theorem.

## Verification Contract

```text
smallest source target:
  ConnesWeilRH.Source.CCM25Concrete.SelectedWeilFormula

future import-facing checks:
  #check @selectedWeilFormula_eq_sourceZeroSum
  #print selectedWeilFormula_eq_sourceZeroSum
  #print axioms selectedWeilFormula_eq_sourceZeroSum

rejection evidence:
  one exact coefficient mismatch, noncompact remainder block, or proof that a
  fixed prime-free window cannot retain a strict negative detector.
```
