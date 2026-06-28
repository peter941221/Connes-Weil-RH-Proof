# Second External Opinion Audit

Date: 2026-06-28

Status:

```text
second external opinion: processed into public review rows
accepted-source certification: open
Lean status: not touched
```

## Result

The second opinion sharpens the review surface. It gives one direct source-level
attack on the route and three checks that protect the route from importing the
wrong theorem.

```text
direct attack:
  S2-B1 divergent bulk / trace-scale incompatibility

route-boundary checks:
  S2-B2 spectral pollution and domain mismatch
  S2-B3 even-sector spectral assumption
  S2-B4 semilocal fourth defect and S(g) uniformity
```

The current repository answers these rows only at route-evidence or
project-proof-package level. A referee can still reject a row by giving a
source-backed counterterm, a missing hypothesis, or an imported theorem that is
weaker than the route uses.

## S2-B1. Divergent Bulk

Attack model:

```text
Tr(A^* A)
  =
Bulk_(S,lambda)(g,g)
+ QW_lambda(g,g)
+ Rank_(S,I)(g)
+ PoleJetExtra_(S,I)(g)
+ R_lambda(g)

Bulk_(S,lambda)(g,g)
  ~ C log(lambda) ||g||^2.
```

If this model matches the source formulas and the bulk term remains outside the
named ledgers, ordinary trace positivity gives only a weak lower bound:

```text
QW_lambda(g,g) >= -Bulk_(S,lambda)(g,g) + lower order terms.
```

That bound cannot feed the final fixed-test limit.

Current local answer:

| item | evidence |
|---|---|
| finite-lambda equality target | `docs/proofs/trace-scale-compatibility-proof-package.md` |
| no-missing-bulk row | `docs/proofs/trace-scale-compatibility-proof-package.md`, Lemma 5 |
| public falsification test | `README.md`, "Falsification Tests For Reviewers" |

Review standard:

```text
If a reviewer identifies a source-owned BulkScaleTerm_(S,I,lambda,g)
that is not part of QW_lambda, Rank, PoleJetExtra, or CdefRemainder,
the route stops at the positive-trace read-off.
```

Current status:

```text
project proof-package coverage only.
accepted-source and Lean discharge remain open.
```

## S2-B2. Spectral Pollution

The second opinion correctly states a general operator-theory risk:

```text
finite-dimensional positivity or eigenvalue behavior does not imply
positivity of the infinite-dimensional Weil form without a controlled
spectral limit.
```

The route must therefore keep the following claims out of the accepted theorem
chain:

```text
finite-operator spectral convergence,
determinant convergence,
eigenvalue convergence to zeta zeros.
```

Current local answer:

| item | evidence |
|---|---|
| README boundary | `README.md`, "Short Verdict" |
| non-importable shortcut list | `README.md`, "Non-Importable Shortcuts" |
| source-readiness audit | `docs/audits/restricted-to-full-qw-source-readiness-audit.md` |
| bridge proof package | `docs/proofs/restricted-to-full-qw-bridge-proof-package.md` |

Review standard:

```text
The fixed-test bridge may use only:

1. CCM25 restriction-definition for QW_lambda;
2. the same source test g and F_g;
3. support containment in [lambda^-1, lambda];
4. finite-prime support stabilization for that fixed test.
```

Any appeal to finite-dimensional spectral positivity, determinant convergence,
or zero convergence reopens this row.

## S2-B3. Even-Sector Spectral Assumption

The second opinion points to a possible assumption in the CCM25 spectral
program: the minimum eigenvector should lie in the even sector.

The current route must not import that assumption. It is a spectral-program
claim, not a fixed-test scalar restriction theorem.

Review standard:

```text
If an accepted-source row depends on an even-sector minimum-eigenvector
conjecture, numerical eigenvalue evidence, or a finite-operator spectrum
limit, the route has imported the wrong theorem.
```

Current status:

```text
no route file should treat the even-sector assumption as accepted input.
```

## S2-B4. Semilocal Fourth Defect And S(g)

The second opinion combines two earlier risks:

```text
semilocal cross-terms may survive outside rank, pole, and Cdef;
constants may grow with the finite set S(g).
```

Current local answer:

| risk | evidence | current strength |
|---|---|---|
| hidden semilocal cross-term | `docs/audits/semilocal-fourth-defect-ledger.md` | project proof-package |
| dynamic `S(g)` quantifier | `docs/audits/s-local-global-quantifier-audit.md` | route-evidence |
| final global scalar | `docs/proofs/restricted-to-full-qw-bridge-proof-package.md` and `docs/proofs/final-sign-bridge-proof-package.md` | route-evidence |

Pointwise quantifier order:

```text
for arbitrary admissible g:
  choose finite S(g) from the visible support of F_g;
  choose lambda0 for that fixed test;
  prove QW(g,g) >= 0;
  use QW(g,g) = - sum_v W_v(F_g);
  return the CC20 inequality for the same F_g.
```

Uniform constants over the whole test-function space are not needed for this
proof shape. A reviewer can still reopen the row by identifying a route step
that takes a supremum over varying `g`, keeps an `S`-local scalar in the final
statement, or applies the final sign bridge to a different test.

## Third-Round Readiness

Use this table to handle the next attack without changing the route boundary.

| attack | required evidence from reviewer | first file to inspect |
|---|---|---|
| untracked divergent bulk | source formula line and proof that the term is outside `QW_lambda`, rank, pole, and `Cdef` | `docs/proofs/trace-scale-compatibility-proof-package.md` |
| hidden finite-part subtraction | source convention showing positivity is lost before `QW_lambda` read-off | `docs/proofs/trace-scale-compatibility-theorem-contract.md` |
| spectral convergence import | route citation that uses finite-operator spectra instead of restriction-definition | `docs/audits/restricted-to-full-qw-source-readiness-audit.md` |
| even-sector assumption import | accepted-source row that depends on the even-sector eigenvector conjecture | `docs/audits/source-import-legitimacy-audit.md` |
| fourth semilocal defect | source-owned cross-term outside Rows 1-7 classes | `docs/audits/semilocal-fourth-defect-ledger.md` |
| uniformity failure | route step requiring constants uniform in `g` or a final `S`-local scalar | `docs/audits/s-local-global-quantifier-audit.md` |

## Current Judgment

| question | answer |
|---|---|
| Does the second opinion produce a new public theorem? | no |
| Does it identify a stronger B1 falsification test? | yes |
| Does it force the route to import CCM25 spectral convergence? | no |
| Does it leave accepted-source certification open? | yes |
| Did this pass touch Lean files? | no |

The second opinion is now represented as public review criteria. The route
remains source-conditional until accepted-source review or Lean formalization
discharges the cited rows.
