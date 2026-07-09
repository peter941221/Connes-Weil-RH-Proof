# CC20 Exit Accepted-Source Packet

Date: 2026-06-28

Status:

```text
CC20 finite-vanishing exit accepted-source packet started
accepted-source certification: open
Lean status: not touched
```

## Purpose

This packet targets the theorem candidate:

```text
CC20FiniteVanishingRHExitTheorem(F_g):
  route triple vanishing
  route full Weil positivity
  correct CC20 sign convention
  ->
  CC20 source RH.
```

The route may use this theorem only after the final sign bridge has converted:

```text
QW(g,g) >= 0
```

into:

```text
sum_v W_v(F_g) <= 0.
```

## Source Anchors

| source | anchors | role |
|---|---|---|
| CC20 finite-vanishing criterion | `weil-compo.tex:2072-2085` | Proposition C.1 and the finite set `F` |
| CC20 finite-set side conditions | `weil-compo.tex:2075-2078` | `F` finite, contains `{0,1}`, disjoint from non-trivial zeros |
| CC20 proof with extra finite set | `weil-compo.tex:2080-2085` | adjoining `F` in the positivity criterion |
| CC20 Mellin/Fourier convention | `weil-compo.tex:2014-2030` | source transform convention for vanishing |
| CC20 sign normalization | `weil-compo.tex:2131-2165` | local Weil sign convention |

## Theorem Shape

The accepted-source theorem must prove:

```text
CC20FiniteVanishingRHExitTheorem:
  F = {0, 1/2, 1}
  F finite
  {0,1} subset F
  F disjoint from the source non-trivial zero set
  route triple vanishing -> Mellin vanishing on F
  forall admissible F_g,
    sum_v W_v(F_g) <= 0
  ->
  CC20 source RH.
```

## Certification Chain

| row | theorem candidate | current evidence | accepted-source check |
|---|---|---|---|
| finite set | `RouteFiniteSetAccepted` | `docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md` | confirm `F={0,1/2,1}` is finite, contains `{0,1}`, and satisfies CC20 side conditions |
| Mellin vanishing | `RouteTripleVanishingToCC20MellinAccepted(F_g)` | `docs/proofs/cc20-trace-legality-mellin-discharge.md`; `docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md` | confirm route triple vanishing becomes CC20 vanishing on the same half-density object |
| CC20 inequality | `RouteWeilInequalityToCC20Accepted(F_g)` | `docs/audits/final-sign-accepted-source-packet.md`; `docs/proofs/final-sign-bridge-proof-package.md` | confirm the input is `sum_v W_v(F_g) <= 0`, not route-local `QW(g,g) >= 0` without sign bridge |
| Proposition C.1 import | `CC20PropositionC1Accepted(F)` | `docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md` | confirm CC20 Proposition C.1 states the exact implication used by the route |
| source RH conclusion | `CC20SourceRHConclusionAccepted` | `docs/proofs/cc20-rh-exit-object-normalization-discharge.md` | confirm the source conclusion is the CC20 RH predicate later consumed by the definition bridge |

## Rejection Conditions

A reviewer should reject this row if one of these conditions occurs:

```text
1. F={0,1/2,1} violates a CC20 side condition;
2. route triple vanishing is not CC20 Mellin vanishing on the same test;
3. the proof feeds QW(g,g) >= 0 directly to Proposition C.1 without the sign bridge;
4. Proposition C.1 requires a stronger uniformity condition than the route proves;
5. the source RH conclusion differs from the predicate handled by the RH definition bridge.
```

## Current Judgment

| question | answer |
|---|---|
| Does this packet make the CC20 exit accepted-source? | no |
| Does it give an exact accepted-source review packet? | yes |
| What remains? | external acceptance of Proposition C.1 use, finite-set side conditions, vanishing translation, and sign input |
| Did this pass touch Lean? | no |

The CC20 final exit now has a review packet. It still depends on the final sign
packet and the RH definition packet before the route can claim a standard RH
conclusion.
