# Connes-Weil RH Proof

This repository publishes a source-conditional Connes-Weil route to the
Riemann Hypothesis.

The main file is:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md
```

Status:

```text
v0.1 referee-readable source-conditional manuscript
```

The route depends on cited theorem-level inputs from:

| Source | Role |
|---|---|
| CCM24, Connes-Consani-Moscovici, arXiv:2310.18423 | fixed-S semilocal Hilbert model, support transport, Fourier compatibility |
| CCM25, Connes-Consani-Moscovici, arXiv:2511.22755 | Weil form `QW`, restricted form `QW_lambda`, finite-prime and pole normalizations |
| CC20, Connes-Consani, arXiv:2006.13771 | archimedean support-square trace, trace-class legality, finite-vanishing RH criterion |

The manuscript does not claim journal acceptance, Clay acceptance, or completed
Lean verification. It gives a proof route whose outside analytic source
theorems stay explicit.

## Claim

Assume the cited CCM24, CCM25, and CC20 source theorems in the normalizations
listed in the manuscript. Then the fixed-S Connes-Weil positive compression
argument gives the Riemann Hypothesis.

The proof has one spine:

```text
  Source theorem inputs
       |
       v
  +-----------------------------+
  | CCM24 fixed-S model         |
  | support and Fourier         |
  | transport                   |
  +-----------------------------+
       |
       v
  +-----------------------------+
  | CC20 support-square trace   |
  | trace-class legality        |
  +-----------------------------+
       |
       v
  +-----------------------------+
  | Project transport lemmas    |
  | and endpoint-strip control  |
  +-----------------------------+
       |
       v
  +-----------------------------+
  | Positive fixed-S trace      |
  | Tr(A^* A) >= 0              |
  +-----------------------------+
       |
       v
  +-----------------------------+
  | CCM25 read-off              |
  | Positive trace = QW_lambda  |
  | plus ledgers and Cdef       |
  +-----------------------------+
       |
       v
  +-----------------------------+
  | Triple vanishing kills      |
  | rank and pole ledgers       |
  +-----------------------------+
       |
       v
  +-----------------------------+
  | Fixed-test exhaustion       |
  | QW_lambda -> QW             |
  +-----------------------------+
       |
       v
  +-----------------------------+
  | CC20 Proposition C.1        |
  | finite-vanishing criterion  |
  +-----------------------------+
       |
       v
  Riemann Hypothesis
```

## Objects

Fix a finite set `S` of places containing the archimedean place. CCM24 gives a
canonical semilocal transform

```text
V_S = M_S U_S.
```

This transform moves the source semilocal model into a fixed Hilbert coordinate
where the support projections and Fourier-side projections can be compared.
For `lambda > 1`, the route uses the transported projection

```text
P_(S,G)(lambda) = V_S P_S(lambda) V_S^(-1).
```

For a compactly supported test function `g`, set

```text
F_g = g^* * g.
```

The tuple `(S,I,lambda,g)` must be admissible:

```text
supp(g) subset I,
I subset [lambda^(-1), lambda],
S contains every finite prime visible to F_g.
```

This condition prevents a fixed finite set `S` from losing prime-power terms
that the CCM25 restricted Weil form sees.

## Fixed-S Positive Trace

The central positive operator is

```text
A_(S,lambda,g)
  =
P_hat_(S,G)(lambda) P_(S,G)(lambda) theta_S(g).
```

The manuscript proves the Hilbert-Schmidt gate

```text
A_(S,lambda,g) in S_2.
```

Hence

```text
PositiveTrace^G_(S,lambda)(g)
  =
Tr(A_(S,lambda,g)^* A_(S,lambda,g))
  >= 0.
```

This is the only positivity source in the project-owned part of the route.
The argument does not assume Weil positivity in advance.

The trace is useful only after transport and read-off:

```text
PositiveTrace^G_(S,lambda)(g)
  =
QW_lambda(g,g)
  +
Rank_(S,I)(g)
  +
PoleJetExtra_(S,I)(g)
  +
R_(S,I,lambda)(g),

|R_(S,I,lambda)(g)|
  <=
C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

The equality has three separate jobs:

| Part | Purpose |
|---|---|
| `QW_lambda(g,g)` | CCM25 restricted Weil quadratic form |
| `Rank` and `PoleJetExtra` | finite-dimensional quotient ledgers |
| `R` | endpoint-strip and comparison error controlled by `Cdef` |

## Source Read-Off

The proof reads the no-defect trace through CCM25:

```text
QW(f,g) = Psi(f^* * g),

Psi(F)
  =
W_(0,2)(F) - W_R(F) - sum_p W_p(F),

W_R = -W_infty.
```

So the sign pattern used by the manuscript is

```text
Psi(F)
  =
W_(0,2)(F) + W_infty(F) - sum_p W_p(F).
```

On the restricted interval `[lambda^(-1), lambda]`, CCM25 gives

```text
QW_lambda(g,g)
  =
int_R |hat g(t)|^2 (2 partial_t theta(t))/(2 pi) dt
  +
2 Re(hat g(i/2) overline{hat g(-i/2)})
  -
sum_(1<n<=lambda^2) Lambda(n)<g|T(n)g>,

<g|T(n)g>
  =
n^(-1/2)((g^* * g)(n) + (g^* * g)(n^(-1))).
```

The proof keeps the CCM pole term inside `QW_lambda`. The extra
`PoleJetExtra` term records quotient directions from the fixed-S trace
matching. The route kills both by imposing finite vanishing.

## Killing The Ledgers

The test function must satisfy

```text
hat g(0) = hat g(+i/2) = hat g(-i/2) = 0.
```

Then

```text
Rank_(S,I)(g) = 0,
PoleJetExtra_(S,I)(g) = 0.
```

The positive trace identity gives

```text
QW_lambda(g,g)
  >=
-C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

The argument sends `lambda` to infinity while keeping the test `g`, the support
window `I`, and the finite-prime set `S_A` fixed. The finite-prime part
stabilizes because `F_g` has compact support. The endpoint-strip term vanishes:

```text
Cdef_(S_A,I,lambda,J)(g) -> 0.
```

Therefore

```text
QW(g,g) >= 0
```

for every compactly supported test satisfying the three vanishing conditions.

## RH Exit

CC20 Proposition C.1 gives a finite-vanishing Weil positivity criterion for RH.
The route uses the finite set

```text
F = {0, 1/2, 1}.
```

The manuscript checks the side condition that this finite set avoids the
non-trivial zeta zeros. The points `0` and `1` are excluded by definition. For
`1/2`, use

```text
eta(s) = (1 - 2^(1-s)) zeta(s).
```

The alternating eta expression is positive for `0 < s < 1`, and
`1 - sqrt(2) != 0`, so

```text
zeta(1/2) != 0.
```

CC20 uses the convention

```text
s = 1/2 - i t.
```

Thus

```text
t = 0     -> s = 1/2,
t = +i/2  -> s = 1,
t = -i/2  -> s = 0.
```

The triple vanishing conditions used to clear the fixed-S ledgers match the
finite vanishing set required by the CC20 criterion. This gives RH from the
source-conditional full Weil positivity result.

## Dependency Boundary

The route separates source theorems from project lemmas:

```text
  CCM24 / CCM25 / CC20
        |
        |  imported as source theorem inputs
        v
  project-owned transport, ledger, and exhaustion lemmas
        |
        v
  source-conditional RH theorem
```

The project-owned route does not import RH as an assumption. The route imports
source theorem interfaces and uses them to identify the positive fixed-S trace
with the CCM Weil form.

## Repository Layout

```text
docs/
  manuscripts/
    connes-weil-rh-proof-draft.md

README.md
```

Local working notes are ignored and do not belong to the public file tree.

## Verification

For the manuscript text:

```text
rg -n "source-conditional|Theorem 1|Route Theorem|Final Verification Status" docs/manuscripts
git diff --check
```

For future Lean work, use the segmented route target in the WSL ext4 worktree:

```text
lake build ConnesWeilRH
```

The Lean scaffold remains source-conditional until the CCM24, CCM25, and CC20
interfaces are replaced by formal source-paper proofs or accepted imported
theorems.
