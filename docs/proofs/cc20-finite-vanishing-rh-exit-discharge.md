# CC20 Finite-Vanishing RH Exit Discharge

Status: proof package for the final CC20 source-interface exit.

This package attacks:

```text
cc20FiniteVanishingRhExit
```

It proves the manuscript-level bridge from the route's triple-killed full Weil
positivity input to the Connes--Consani Proposition C.1 criterion. It does not
formalize CC20 inside Lean, and it does not replace Mathlib's definition of
`RiemannHypothesis`.

## Evidence Boundary

Official source package:

```text
https://arxiv.org/e-print/2006.13771
```

The relevant source file is `weil-compo.tex`.

| claim | evidence |
|---|---|
| CC20 finite-vanishing criterion | `weil-compo.tex:2072-2085` |
| CC20 allows any finite `F` containing `{0,1}` and disjoint from non-trivial zeros | `weil-compo.tex:2075-2078` |
| CC20 proof handles the extra finite vanishing set by adjoining `F` | `weil-compo.tex:2080-2085` |
| Mellin/Fourier half-density convention | `weil-compo.tex:2014-2030`; `docs/proofs/cc20-trace-legality-mellin-discharge.md:293-341` |
| route finite set `F={0,1/2,1}` | manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:1224-1291` |
| source-sign bridge into the CCM form | `docs/proofs/cc20-trace-legality-mellin-discharge.md:235-291`; `docs/proofs/ccm25-restricted-read-off-discharge.md:360-402` |
| Lean source-interface shape to discharge later | `ConnesWeilRH/Basic.lean:206-212`; `ConnesWeilRH/Source/CC20.lean:45-51`; `ConnesWeilRH/Route/RouteTheorem.lean:24-33` |

## Target Statement

The source-interface target is:

```text
CC20FiniteVanishingRhExitDischarge:
  If the route supplies full Weil positivity for every compactly supported
  half-density test whose three centered evaluations vanish, then CC20
  Proposition C.1 gives RH.
```

The route must pass this chain:

```text
triple vanishing in route variables
      |
      v
Mellin vanishing on F={0,1/2,1}
      |
      v
CC20 finite-set side conditions
      |
      v
CC20 Weil inequality with the source sign
      |
      v
Connes--Consani Proposition C.1
      |
      v
Riemann Hypothesis
```

## Lemma 1. Proposition C.1 Source Criterion

Statement:

```text
CC20PropositionC1(F):
  If F is finite, contains {0,1}, and is disjoint from the non-trivial zero set,
  then RH is equivalent to the CC20 finite-vanishing Weil inequality on tests
  vanishing on F.
```

Proof.

CC20 states the criterion in the appendix positivity section:

```text
weil-compo.tex:2072-2078
```

The source proposition uses compactly supported smooth multiplicative tests
`g` with:

```text
tilde g(z)=0 for all z in F.
```

It asserts the equivalence:

```text
RH
  iff
sum_v W_v(g * bar(g)^sharp) <= 0
for every such g.
```

The proof text also explains why the extra finite set is allowed: when it builds
the detecting test, it adjoins `F` to the finite zero set used in the Yoshida
argument:

```text
weil-compo.tex:2080-2085
```

Therefore the route must not replace Proposition C.1 by a new density lemma.
The source already includes the finite extra vanishing set.

## Lemma 2. The Route Finite Set Is Admissible

Statement:

```text
RouteFiniteSetAdmissible:
  F={0,1/2,1} is finite, contains {0,1}, and is disjoint from the set of
  non-trivial zeros of zeta.
```

Proof.

The set is finite and contains `{0,1}`.

The points `0` and `1` are not non-trivial zeros by definition. For `1/2`, use
Dirichlet's eta relation:

```text
eta(s) = (1 - 2^(1-s)) zeta(s).
```

For `0 < s < 1`, the alternating series for `eta(s)` has positive first
partial dominance:

```text
eta(s) = 1 - 2^(-s) + 3^(-s) - 4^(-s) + ...
```

The terms decrease to zero, so `eta(1/2) > 0`. The scalar:

```text
1 - 2^(1/2)
```

is nonzero. Hence:

```text
zeta(1/2) = eta(1/2) / (1 - 2^(1/2)) != 0.
```

The manuscript records this finite-set check in:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:1240-1260
```

Output:

```text
finiteSetAdmissible for F={0,1/2,1}.
```

## Lemma 3. Triple Vanishing Equals Mellin Vanishing On F

Statement:

```text
TripleVanishingToMellinF(g):
  the route's three vanishing conditions are exactly the CC20 Mellin
  vanishings on F={0,1/2,1}.
```

Proof.

CC20 relates the source Mellin transform of `k` to the multiplicative Fourier
transform of the half-density `f` by:

```text
tilde k(1/2 + i s) = hat f(-s).
```

Evidence:

```text
weil-compo.tex:2021-2030
docs/proofs/cc20-trace-legality-mellin-discharge.md:293-341
```

The route uses the centered variable:

```text
z = 1/2 - i t.
```

Thus the three centered route evaluations map as follows:

| route point `t` | source Mellin point `z` |
|---|---|
| `0` | `1/2` |
| `+i/2` | `1` |
| `-i/2` | `0` |

So route triple vanishing at:

```text
t in {0,+i/2,-i/2}
```

is the same source finite vanishing condition:

```text
tilde g(z)=0 for z in {0,1/2,1}.
```

The manuscript records the same translation in:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:1262-1287
```

Output:

```text
input.tripleVanishing supplies the CC20 finite-vanishing hypothesis.
```

## Lemma 4. Route Positivity Has The CC20 Sign

Statement:

```text
RouteFullWeilPositivityToCC20Inequality(g):
  after the sign and read-off discharge packages, route full Weil positivity
  is the CC20 finite-vanishing Weil inequality used in Proposition C.1.
```

Proof.

CC20 Proposition C.1 uses:

```text
sum_v W_v(g * bar(g)^sharp) <= 0.
```

The route proves full Weil positivity through the CCM-normalized quadratic
form:

```text
QW(g,g) >= 0.
```

These two statements match only after the source sign bridge has been fixed.
That bridge has two inputs:

| input | role |
|---|---|
| CC20 sign normalization | fixes the archimedean `u_infty` and `qd u` sign |
| CCM25 restricted and full read-off | fixes `QW`, `QW_lambda`, finite-prime subtraction, and pole normalization |

The relevant proof packages are:

```text
docs/proofs/cc20-trace-legality-mellin-discharge.md
docs/proofs/ccm25-restricted-read-off-discharge.md
docs/proofs/ccm25-finite-prime-support-pairing-discharge.md
```

After those packages, `FullWeilPositivity` must mean:

```text
QW(g,g) >= 0
```

with the source convention:

```text
QW(g,g) = - sum_v W_v(g * bar(g)^sharp).
```

Therefore:

```text
QW(g,g) >= 0
```

is exactly:

```text
sum_v W_v(g * bar(g)^sharp) <= 0.
```

This sign bridge is the main exit invariant. If a later formal statement gives
`FullWeilPositivity` a route-local sign without this equality, the final RH
exit does not follow from CC20.

## Lemma 5. Proposition C.1 Applies To The Route Input

Statement:

```text
CC20ExitApplies(input):
  input.tripleVanishing and input.fullWeilPositivity imply RH.
```

Proof.

Use Lemma 2 with:

```text
F={0,1/2,1}.
```

Use Lemma 3 to translate route triple vanishing into the source condition:

```text
tilde g(z)=0 for every z in F.
```

Use Lemma 4 to translate route full Weil positivity into:

```text
sum_v W_v(g * bar(g)^sharp) <= 0.
```

Then apply CC20 Proposition C.1:

```text
weil-compo.tex:2075-2078
```

The conclusion is the Riemann Hypothesis in the source sense. The Lean route
must keep the final theorem target as Mathlib's canonical:

```text
_root_.RiemannHypothesis
```

The current Lean wrapper already enforces that target:

```text
ConnesWeilRH/Route/RouteTheorem.lean:24-33
```

Output:

```text
FiniteVanishingCriterionPackage.criterion
```

with:

```text
finiteSetAdmissible = RouteFiniteSetAdmissible
criterion = CC20ExitApplies
```

## Integrated Exit Result

Combine Lemmas 1 through 5:

```text
CC20FiniteVanishingRhExitDischarge
```

The proof-package-level output has the same shape as the current Lean source
interface:

```text
FiniteVanishingCriterionPackage where
  finiteSetAdmissible := RouteFiniteSetAdmissible
  criterion :=
    fun input hTriple hFull =>
      CC20 Proposition C.1 applied with F={0,1/2,1}
```

The dependency graph is:

```text
CC20 Proposition C.1
        ^
        |
F={0,1/2,1} admissible
        ^
        |
route triple vanishing -- Mellin bridge -- CC20 vanishings on F
        |
route full positivity -- sign bridge ---- CC20 Weil inequality
```

## Remaining Boundary

This package closes the final CC20 exit at source-interface proof-package level.
It leaves these stronger evidence tasks:

| task | reason |
|---|---|
| formalize or import CC20 Proposition C.1 | this package cites the CC20 source theorem and does not reprove Yoshida's criterion |
| formalize the sign bridge `QW = - sum_v W_v` | the final Lean package must not hide the sign inside an opaque `fullWeilPositivity` proposition |
| connect source RH to Mathlib RH definition | current Lean targets `_root_.RiemannHypothesis`, but the source criterion still needs a formal definition bridge before certification |

The route still remains source-conditional. The mathematical exit is now
explicit enough that the next attack can move to CCM24 support-window transport
or to formal replacement of the source-interface package.
