# Restricted To Full QW Source Readiness Audit

Status: source-readiness audit for the fixed-test `QW_lambda -> QW` gate.

Target contract:

```text
docs/proofs/restricted-to-full-qw-exhaustion-theorem-contract.md
```

Composition bridge:

```text
docs/proofs/restricted-to-full-qw-bridge-theorem-contract.md
docs/proofs/restricted-to-full-qw-bridge-proof-package.md
```

This audit asks whether the route needs CCM25 spectral convergence to pass from
`QW_lambda(g,g)` to `QW(g,g)`. The answer is no, provided the route proves that
the fixed test entering `QW_lambda` is the same source test entering `QW` and
that its support lies in the restricted interval.

## Source Evidence

| source | lines | what the source gives |
|---|---:|---|
| `mc2arXiv.tex` | `400-428` | defines the Weil class and states the explicit formula for compact convolution tests |
| `mc2arXiv.tex` | `464-470` | defines `QW(f,g)=Psi(f^**g)` and `Psi` |
| `mc2arXiv.tex` | `496-529` | identifies `QW(kappa(f),kappa(g))` with the source convolution expression |
| `mc2arXiv.tex` | `530-535` | defines `QW_lambda` as the restriction of `QW` to `L^2([lambda^-1,lambda],d^*u)` |
| `mc2arXiv.tex` | `535-540` | gives the restricted formula with finite sum `1<n<=lambda^2` and pairing `T(n)` |
| `mc2arXiv.tex` | `266-272` | frames spectral convergence as numerical and says a proof would establish RH |
| `mc2arXiv.tex` | `302-303` | says numerical eigenvalue convergence and determinant convergence are strategy/outlook material |

Primary source page:

```text
https://arxiv.org/abs/2511.22755
```

## Source Reading

The key source sentence is the definition:

```text
QW_lambda is the restriction of QW to
L^2([lambda^-1, lambda], d^*u).
```

This gives a direct source route:

```text
g supported in [lambda^-1, lambda]
        |
        v
g lies in the domain of restricted QW_lambda
        |
        v
QW_lambda(g,g) = QW(g,g)
```

for the same source object.

The finite-prime formula is consistent with the same reading. If `g` is fixed
and compactly supported inside `[lambda^-1,lambda]`, then:

```text
F_g = g^* * g
```

has support inside `[lambda^-2,lambda^2]`. Hence finite-prime atoms outside the
restricted source support do not contribute to the full `QW` value for that
test. The restricted finite sum is not a spectral approximation; it is the
source formula for the restricted quadratic form.

## What Must Still Be Proved

The source definition does not discharge the whole route by itself. It still
requires three bridge facts:

| bridge | reason |
|---|---|
| same test | the `g` in the positive trace must be the same `g` in CCM25 |
| support containment | the fixed `g` must lie in `[lambda^-1,lambda]` when `QW_lambda(g,g)` is used |
| finite-prime visibility | the route's fixed `S_A` must cover every source prime-power atom visible to `F_g` |

These are already named elsewhere:

```text
docs/proofs/source-common-test-tuple-theorem-contract.md
docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md
docs/proofs/source-object-definition-theorem-contract.md
docs/proofs/restricted-to-full-qw-bridge-theorem-contract.md
```

## Spectral Convergence Is Not Used

The source also states:

```text
Numerical experiments show spectra converging to zeta zeros;
a rigorous proof of that convergence would establish RH.
```

That statement is not needed for the scalar fixed-test passage from
`QW_lambda(g,g)` to `QW(g,g)`. It concerns finite-dimensional spectral triples
and their spectra as `N, lambda -> infinity`.

The route should therefore replace:

```text
QW_lambda -> QW by spectral convergence.
```

with:

```text
QW_lambda is QW restricted to a source interval,
and the fixed source test lies in that interval.
```

## Contract Status

The theorem contract:

```text
RestrictedToFullQWExhaustionContract(g)
```

can be sharpened from a general limit theorem to an eventual-identity theorem:

```text
for lambda large enough,
QW_lambda(g,g) = QW(g,g).
```

This stronger statement follows from the source definition only after the
same-test and support-containment bridges are proved.

## Route Consequence

After the bridges are supplied, the route no longer needs to write this step as
a limiting approximation. It can use:

```text
choose lambda >= lambda0(g);
QW_lambda(g,g) = QW(g,g).
```

Then the fixed-test lower bound:

```text
QW_lambda(g,g) >= -C Cdef(lambda,g)
```

and `Cdef(lambda,g) -> 0` imply `QW(g,g) >= 0` without invoking finite-operator
spectral convergence.

## Current Judgment

| question | answer |
|---|---|
| Does CCM25 source support a fixed-test route from `QW_lambda` to `QW`? | yes |
| Does that route use spectral convergence? | no |
| Is it already discharged in this repository? | at route-evidence level only |
| What remains? | accepted source-import or Lean discharge of the bridge contract |

The source-import status is:

```text
route-evidence bridge written;
accepted-source and Lean discharge not yet supplied.
```
