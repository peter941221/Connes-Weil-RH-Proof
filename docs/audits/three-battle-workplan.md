# Three-Battle Workplan

Status: working checklist for the three proof packages behind the fixed-S
positive compression route.

This file turns `docs/audits/core-defect-gap-ledger.md` into an execution
order. It does not certify any battle as complete.

## Working Rule

Do not use a status label from `docs/ConnesWeilPositivity.md` as a proof.

Use that file to locate candidate lemmas and proof sketches. Then rewrite each
candidate as a theorem with:

```text
objects
hypotheses
conclusion
source formulas
project lemmas
failure mode
```

## Order Of Attack

```text
Battle 1: TestAndQuotientCompatibility
    |
    v
Battle 2: FixedSQuantizedSupportSquareTransport
    |
    v
Battle 3: CdefNormFormula + FixedTestCdefExhaustion
    |
    v
Triple-killed Weil positivity
```

This order matters. Battle 2 should not identify a route trace with
`QW_lambda(g,g)` until Battle 1 fixes the source test and quotient ledgers.
Battle 3 should not be used as a black-box error term until Battle 2 has
specified which defects enter `Cdef`.

## Battle 1 Checklist

Target:

```text
TestAndQuotientCompatibility(S,I,lambda)
```

Primary local evidence:

```text
docs/ConnesWeilPositivity.md:143025-143153
docs/ConnesWeilPositivity.md:143155-143573
```

### Tasks

| task | output |
|---|---|
| Define `F_g` | exact convolution-square convention for `F_g=g^* * g` |
| Define source test `h` | formula converting `F_g` to the source trace test |
| Match half-density convention | citation to CC20/CCM25 convention used by the route |
| Identify source quotient directions | basis or functional description of Connes quotient/radical channels |
| Match route ledgers | proof that source channels equal `Rank_(S,I)` and `PoleJetExtra_(S,I)` |
| State failure test | explicit mismatch that would kill the route |

### Done Means

Battle 1 passes only when the manuscript can display:

```text
Trace(R_Lambda U(h(F_g)))
  =
QW_lambda(g,g)
  +
source rank/pole channels
```

before any fixed-S transport claim enters.

## Battle 2 Checklist

Target:

```text
FixedSQuantizedSupportSquareTransport(S,I,lambda)
```

Primary local evidence:

```text
docs/ConnesWeilPositivity.md:143700-143860
docs/ConnesWeilPositivity.md:147000-147198
```

Focused audit:

```text
docs/audits/battle-2-fixed-s-support-square-transport.md
```

Proof package:

```text
docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md
```

### Tasks

| task | output |
|---|---|
| Fix one Hilbert coordinate | statement that all commutators live in the same scattering/canonical coordinate |
| Prove support transport | range equality for `P_S(lambda)` and transported `P_(S,G)(lambda)` |
| Prove Fourier projection transport | range equality for `P_hat_S(lambda)` and transported `P_hat_(S,G)(lambda)` |
| Pull back the phase | formula for `u_S=M_S^(-1) I M_S I` and the direction of conjugation |
| Expand support square | trace identity for `P_(S,G) P_hat_(S,G) P_(S,G)` after theta smoothing |
| Classify every leftover term | each term is rank, pole, or endpoint-strip `Cdef` |

### Done Means

Battle 2 passes only when the proof no longer uses:

```text
same quantized-calculus expansion
```

as a hidden step. The proof must show the expansion term by term after
transport through `V_S=M_S U_S`.

Current status: the proof package performs this decomposition at
route-evidence level and consumes the Battle 1 rank/pole ledger plus the
Battle 3 endpoint-strip `Cdef` package, both now represented by proof
packages.

## Battle 3 Checklist

Targets:

```text
CdefNormFormula(S,I,lambda,J)
FixedTestCdefExhaustion(S_A,I,g)
```

Primary local evidence:

```text
docs/ConnesWeilPositivity.md:146180-146320
docs/ConnesWeilPositivity.md:146790-146918
```

Focused audit:

```text
docs/audits/battle-3-cdef-exhaustion.md
```

Proof package:

```text
docs/proofs/battle-3-cdef-exhaustion-proof-package.md
docs/proofs/fixed-test-graph-cdef-exhaustion.md
```

### Tasks

| task | output |
|---|---|
| Define endpoint-strip index set | finite set `R_(S,I,lambda,J)` with all parameters named |
| Define `Cdef` by trace norms | no role-only definition |
| Prove Hilbert-Schmidt factorization | `L2(R) -> L2(E_(lambda,a)) -> L2(R)` estimate |
| Prove `Q` stability | boundary evaluations keep an endpoint-strip factor |
| Prove graph comparison | `Cdef <= C' Cdef_graph` |
| Prove fixed-test limit | `Cdef_graph_(S_A,I,lambda,J')(g) -> 0` with `g,S_A` fixed |

### Done Means

Battle 3 passes only when the final theorem can use:

```text
QW_lambda(g,g)
  >=
-C_(S_A,I,J)(g) Cdef_(S_A,I,lambda,J)(g)
```

and then prove the right side tends to `0` without changing `g`, `I`, or
`S_A`.

## Lean Follow-Up

After the manuscript has the three theorem packages, the Lean scaffold should
stop accepting the corresponding content as arbitrary bridge fields.

Current files to inspect:

```text
ConnesWeilRH/Route/Theorem1.lean
ConnesWeilRH/Route/Ledger.lean
ConnesWeilRH/Route/Exhaustion.lean
```

Expected direction:

| current shape | replacement direction |
|---|---|
| `SourceTraceReadOffData` carries bridge functions | replace with named theorem inputs for Battles 1 and 2 |
| `SourceBackedLedgers` carries arbitrary ledger source propositions | replace with Battle 3 objects and estimates |
| `FullWeilPositivity` only packages route predicates | require the three battle outputs before constructing positivity |

## Stop Conditions

Stop the proof route and mark the obstruction if any of these fail:

| battle | stop condition |
|---|---|
| Battle 1 | `h(F_g)` does not match the CCM25 restricted form or quotient channels |
| Battle 2 | fixed-S transport produces a leftover term outside rank, pole, and endpoint-strip `Cdef` |
| Battle 3 | endpoint-strip `Cdef` does not vanish for fixed `g,I,S_A` |

These are mathematical stop conditions, not implementation failures.
