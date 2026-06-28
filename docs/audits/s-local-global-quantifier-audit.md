# S-Local To Global Quantifier Audit

Date: 2026-06-28

Status:

```text
B4 dynamic S(g) quantifier risk: closed at route-evidence level
accepted-source certification: open
Lean status: not started
```

## Question

The first external opinion raised this B4 risk:

```text
The route chooses a finite prime set S depending on g.
CC20 Proposition C.1 needs a global forall-g Weil inequality.
The constants in the S-local estimates may grow with S(g).
```

This audit asks whether the current route needs one uniform finite `S`, one
uniform Hilbert space model, or constants uniform in `g`.

## Verdict

At route-evidence level, B4 does not block the argument.

The route proves a pointwise statement:

```text
for each fixed admissible g:
  choose S(g) containing the finite primes visible to F_g = g^* * g;
  choose lambda0(g,S,I,J);
  prove QW(g,g) >= 0.
```

Then it discharges the CC20 hypothesis by universal introduction:

```text
take arbitrary g satisfying the finite vanishing conditions;
run the fixed-g construction;
return the global scalar inequality for that same g.
```

The route does not need:

```text
one finite S that works for all g,
one shared finite-S Hilbert model for all g,
or a Cdef estimate uniform over the whole test-function space.
```

It would need uniformity only if it used a density argument, a topological
closure argument in the test-function space, or an interchange of limits over
`g` and `lambda`. The current route uses none of those moves.

## Quantifier Shape

The safe order is:

```text
forall g satisfying triple vanishing
  let F_g = g^* * g
  exists finite S = S(g) with visible-prime coverage
  exists lambda0 = lambda0(g,S,I,J)
  forall lambda >= lambda0
    QW_lambda(g,g) = QW(g,g)
    and
    QW_lambda(g,g) >= -C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g)
  hence QW(g,g) >= 0
```

The unsafe order would be:

```text
exists finite S
  forall g
    ...
```

or:

```text
exists constants C independent of g
  forall g
    ...
```

The route does not use either unsafe order.

## Dependency Diagram

```text
arbitrary g
    |
    v
F_g = g^* * g
    |
    v
visible prime-power support of F_g
    |
    v
choose finite S(g) before lambda limit
    |
    v
fixed-S trace read-off and Row 7 lower bound
    |
    v
fixed-test Cdef(lambda,g) -> 0
    |
    v
eventual identity QW_lambda(g,g) = QW(g,g)
    |
    v
global scalar QW(g,g) >= 0
    |
    v
QW(g,g) = - sum_v W_v(F_g)
    |
    v
CC20 forall-g Weil inequality
```

The finite `S(g)` is a witness used inside the proof for one fixed test. It is
not part of the final CC20 statement.

## Evidence Map

| obligation | evidence |
|---|---|
| same source test and convolution square | `docs/proofs/source-common-test-tuple-theorem-contract.md`; `docs/proofs/source-test-convolution-compatibility.md` |
| admissible tuple uses fixed `S`, `I`, `lambda`, `g` before read-off | `README.md`; `docs/proofs/source-object-definition-theorem-contract.md` |
| finite-prime visibility is fixed from `F_g` before the lambda limit | `docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md`; `docs/proofs/ccm25-finite-prime-normalization-spine-discharge.md` |
| restricted support is the lambda cut of the same global support | `docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md` |
| fixed-test `QW_lambda(g,g)=QW(g,g)` uses restriction-definition, not spectral convergence | `docs/audits/restricted-to-full-qw-source-readiness-audit.md`; `docs/proofs/restricted-to-full-qw-bridge-proof-package.md` |
| lower bound transfers after fixed-test `Cdef` exhaustion | `docs/proofs/restricted-to-full-qw-bridge-proof-package.md`; `docs/proofs/battle-3-cdef-exhaustion-proof-package.md` |
| final scalar is independent of the auxiliary finite `S(g)` | `docs/proofs/restricted-to-full-qw-bridge-proof-package.md`; `docs/proofs/final-sign-bridge-proof-package.md` |
| CC20 receives a global Weil inequality for the same `F_g` | `docs/proofs/source-conditional-rh-route-closure-proof-package.md`; `docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md` |

## Why Uniformity In g Is Not Required

The proof target is:

```text
forall g, QW(g,g) >= 0.
```

A proof of that target may let witnesses depend on the arbitrary `g`:

```text
g |-> S(g),
g |-> lambda0(g),
g |-> C_(S(g),I,J)(g).
```

This is the same logical form as proving continuity at every point with a
point-dependent delta. A uniform delta would prove a stronger theorem, but the
pointwise theorem does not require it.

The route's limit is also fixed-test:

```text
for fixed g and fixed S(g),
  Cdef_(S(g),I,lambda,J)(g) -> 0.
```

The route never claims:

```text
sup_g Cdef_(S(g),I,lambda,J)(g) -> 0.
```

No step of CC20 Proposition C.1, as consumed by this route, requires that
stronger uniform statement.

## Why Dynamic S(g) Does Not Change The Final Object

The auxiliary finite set `S(g)` controls the semilocal fixed-S read-off. It
does not define the final global scalar.

The restricted-to-full bridge returns:

```text
QW_lambda(g,g) = QW(g,g)
```

for large enough `lambda`, where `QW(g,g)` is the CCM25 global quadratic form
on the same source test.

The final sign bridge returns:

```text
QW(g,g) = - sum_v W_v(F_g).
```

That local Weil sum is the CC20 global object consumed by Proposition C.1. It
does not keep `S(g)` as a parameter.

## What Would Reopen B4

B4 reopens if a reviewer supplies any one of these failures:

```text
1. CC20 Proposition C.1 requires uniform-in-g constants rather than a
   pointwise forall-g inequality.

2. The restricted-to-full bridge keeps an S-dependent scalar instead of
   returning the global `QW(g,g)`.

3. The finite-prime normalization permits a visible prime-power atom of F_g to
   be omitted, added twice, or assigned a wrong weight or pairing when S varies.

4. The endpoint-strip exhaustion uses a limit that is only known after taking
   a supremum over varying g.

5. The final sign bridge applies to a different test object than the one used
   to choose S(g).
```

Any of these would stop the route before CC20 Proposition C.1.

## Current Judgment

| question | answer |
|---|---|
| Does the route require one finite `S` for all tests? | no |
| Does the route allow `S` to depend on the fixed test? | yes |
| Does that dependence remain in the final CC20 hypothesis? | no |
| Does the route require uniform constants over all `g`? | no, not for the current pointwise forall-g proof shape |
| Does this close B4 at accepted-source or Lean level? | no |

B4 is closed at route-evidence level. The remaining certification work is to
replace the cited source-interface and bridge packages by accepted-source
theorems or Lean theorems with audited assumptions.
