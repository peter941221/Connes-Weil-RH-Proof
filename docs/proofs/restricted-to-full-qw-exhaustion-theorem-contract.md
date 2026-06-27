# Restricted To Full QW Exhaustion Theorem Contract

Status: theorem contract for the `QW_lambda -> QW` source-import gate.

This contract states the theorem needed after the fixed-test inequality:

```text
QW_lambda(g,g)
  >=
-C_(S_A,I,J)(g) Cdef_(S_A,I,lambda,J)(g).
```

It does not prove CCM25 spectral convergence. It also does not import the
numerical convergence claims from arXiv:2511.22755. It fixes the exact
fixed-test theorem that the route needs.

The source-readiness audit for this contract is:

```text
docs/audits/restricted-to-full-qw-source-readiness-audit.md
```

That audit finds an import-ready source-definition path: CCM25 defines
`QW_lambda` as the restriction of `QW`. After the common-test and support
bridges are proved, the route should use eventual equality rather than a
spectral convergence limit.

## Evidence Lock

| item | evidence |
|---|---|
| public route limit claim | `README.md:248-259` |
| source-import blocker audit | `docs/audits/source-import-legitimacy-audit.md` |
| sign/defect blocker audit | `docs/audits/sign-defect-blocker-audit.md:192-209` |
| fixed-test Cdef package | `docs/proofs/battle-3-cdef-exhaustion-proof-package.md:318-341` |
| fixed-test graph exhaustion warning | `docs/proofs/fixed-test-graph-cdef-exhaustion.md:13-15` |
| restricted-to-full source-readiness audit | `docs/audits/restricted-to-full-qw-source-readiness-audit.md` |
| CCM25 external warning | arXiv:2511.22755 abstract, https://arxiv.org/abs/2511.22755 |

The CCM25 abstract reports numerical spectral convergence and says a rigorous
proof of that convergence would establish RH. This contract forbids importing
that numerical statement as the route's `QW_lambda -> QW` theorem.

## Boundary

The route needs a fixed-test quadratic-form identification:

```text
fixed g, fixed source object, fixed finite-prime visibility
        |
        v
restricted quadratic forms QW_lambda(g,g)
        |
        v
full quadratic form QW(g,g).
```

It does not need, and must not assume:

```text
finite operator spectra converge to zeta zeros.
```

Those are different statements.

## Objects Fixed Before The Limit

The theorem must fix:

```text
g                         source half-density test
F_g = g^* * g             source convolution square
I                         support window containing supp(g)
S_A                       finite place set covering all visible primes of F_g
J                         graph/trace order used by Cdef
QW_lambda                 CCM25 restricted quadratic form
QW                        CCM25 full quadratic form
```

The order is:

```text
1. choose g;
2. form F_g;
3. choose I containing supp(g);
4. choose A so supp(F_g) lies in exp([-A,A]);
5. set S_A={infinity} union {p : log p <= A};
6. fix graph/trace order J;
7. send lambda -> infinity.
```

No term in the constant may smuggle in `lambda` after step 6.

## Contract Theorem 1. Same Source Test

Target:

```text
RestrictedAndFullQWUseSameSourceTest(g):
  QW_lambda(g,g) and QW(g,g) are evaluated on the same F_g=g^* * g.
```

Meaning:

The restricted and full forms must consume the same source object. A proof of
exhaustion for a different test does not pass.

## Contract Theorem 2. Finite-Prime Stabilization

Target:

```text
RestrictedFinitePrimeSupportStabilizes(g,S_A):
  for lambda large enough, every finite-prime atom visible to F_g
  appears in the restricted QW_lambda index set.
```

Meaning:

The finite-prime part must stabilize because the fixed test has compact
source support. The theorem must identify the restricted index set and the
full source finite-prime support pointwise.

Blocked shortcut:

```text
finite-prime sums converge
```

with no coverage theorem for the source prime-power atoms.

## Contract Theorem 3. Archimedean And Pole Term Stability

Target:

```text
RestrictedArchimedeanPoleTermsConverge(g):
  the archimedean and pole terms in QW_lambda(g,g)
  converge to the corresponding full QW(g,g) terms
  under the same Mellin and half-density convention.
```

Meaning:

The finite-prime cutoff is not the only possible drift point. The route must
also prove that the archimedean and pole conventions stay fixed while
`lambda` grows.

## Contract Theorem 4. No Spectral-Convergence Import

Target:

```text
RestrictedToFullQWExhaustionDoesNotUseSpectralConvergence:
  the proof of QW_lambda(g,g) -> QW(g,g)
  uses fixed-test support, source formulae, and dominated/finite support
  arguments only, not spectral convergence of finite operators to zeta zeros.
```

Meaning:

This theorem is a proof-hygiene guard. It blocks the route from importing the
main unresolved CCM25 convergence program under a different name.

## Contract Theorem 5. Restricted-To-Full Eventual Identity

Target:

```text
RestrictedToFullQWEventualIdentity(g):
  for lambda large enough,
  QW_lambda(g,g) = QW(g,g)
```

under the fixed-test order above.

This may be weakened to scalar convergence:

```text
QW_lambda(g,g) -> QW(g,g)
```

but the source-readiness audit indicates that the stronger eventual identity is
the right target once the support and common-test bridges are available. It is
not enough to assert weak operator convergence, spectral convergence, or
determinant convergence unless a theorem bridges that mode to the scalar
quadratic-form value.

## Combined Contract

The formal/import target is:

```text
RestrictedToFullQWExhaustionContract(g):
  RestrictedAndFullQWUseSameSourceTest(g)
  RestrictedFinitePrimeSupportStabilizes(g,S_A)
  RestrictedArchimedeanPoleTermsConverge(g)
  RestrictedToFullQWExhaustionDoesNotUseSpectralConvergence
  RestrictedToFullQWEventualIdentity(g)
```

After the source-readiness audit, the preferred concrete projection is:

```text
RestrictedToFullQWExhaustionContract(g)
  ->
exists lambda0,
  forall lambda >= lambda0,
    QW_lambda(g,g) = QW(g,g).
```

Route consumption target:

```text
liminf_(lambda -> infinity) QW_lambda(g,g) >= 0
  +
RestrictedToFullQWExhaustion(g)
  ->
QW(g,g) >= 0.
```

## Import Acceptance Checklist

A source import can discharge this contract only if it supplies:

| item | required evidence |
|---|---|
| same test | restricted and full forms use the same `F_g` |
| fixed data | `g`, `I`, `S_A`, and graph/trace order are fixed before the limit |
| finite-prime coverage | restricted prime-power support eventually contains the full support visible to `F_g` |
| termwise normalization | von Mangoldt weights, pairings, pole terms, and archimedean terms use one convention |
| scalar convergence or equality | theorem gives eventual `QW_lambda(g,g)=QW(g,g)`, or at least scalar real convergence |
| no unresolved CCM25 program | proof does not rely on finite spectra converging to zeta zeros |

## Current Judgment

| question | answer |
|---|---|
| Does this contract prove `QW_lambda -> QW`? | at route-evidence level through `docs/proofs/restricted-to-full-qw-bridge-proof-package.md` |
| Does source review find an import-ready path? | yes, after common-test and support bridges |
| Does it state the route's needed identification without importing spectral convergence? | yes |
| Does it permit CCM25 numerical spectral convergence as a theorem import? | no |
| Can the current route treat this as accepted-source or Lean discharged? | no |

The next pass should source-certify or formalize the eventual-identity theorem
from the CCM25 restriction definition plus the route's common-test and support
bridges.
