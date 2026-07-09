# Final Sign Accepted-Source Packet

Date: 2026-06-28

Status:

```text
final sign accepted-source packet started
accepted-source certification: open
Lean status: not touched
```

## Purpose

This packet targets the theorem candidate:

```text
FinalCCM25CC20SignTheorem(g,F_g):
  QW(g,g) = - sum_v W_v(F_g)
```

and the direction:

```text
QW(g,g) >= 0
  ->
sum_v W_v(F_g) <= 0.
```

The theorem must use the same source test `g` and the same convolution square
`F_g = g^* * g` used in the trace read-off.

## Source Anchors

| source family | anchors | role |
|---|---|---|
| CCM25 `QW` and `Psi` | `mc2arXiv.tex:445-470` | global `QW`, `Psi`, pole, finite-prime, and archimedean signs |
| CCM25 restricted and finite-prime normalization | `mc2arXiv.tex:530-540` | restricted sign conventions and prime-power pairing |
| CC20 local signs | `weil-compo.tex:2131-2165` | `u_infty`, `qd u`, archimedean sign, and local Weil convention |
| CC20 final inequality input | `weil-compo.tex:2072-2085` | Proposition C.1 consumes `sum_v W_v(F_g) <= 0` |

## Certification Chain

| row | theorem candidate | current evidence | accepted-source check |
|---|---|---|---|
| common test | `SourceQWUsesCommonTest(g,F_g)` | `docs/proofs/source-test-convolution-compatibility.md` | confirm `QW(g,g)` and the CC20 local Weil sum use the same `F_g` |
| `QW=Psi` | `SourceQWEqualsPsi(g,F_g)` | `docs/proofs/ccm25-qw-psi-definition-sign-discharge.md` | confirm the source `Psi` object matches route `QW` without changing half-density conventions |
| `Psi` sign expansion | `SourcePsiSignExpansion(F_g)` | `docs/proofs/final-sign-bridge-spine-discharge.md` | confirm pole, archimedean, and finite-prime signs in `Psi` |
| archimedean sign | `SourceArchimedeanSignBridge(F_g)` | `docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md` | confirm CCM25 `W_R` equals the negative of the CC20 archimedean contribution with the route convention |
| finite-prime signs | `SourceFinitePrimeSignOwnedByFormula(F_g)` | `docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md` | confirm the finite-prime sign comes from the source formula and not from route-local absorption |
| pole sign | `SourcePoleSignInCC20LocalSum(F_g)` | `docs/proofs/final-sign-bridge-spine-discharge.md` | confirm the pole term lands in the CC20 local sum with the displayed sign |
| final equality | `SourceQWEqualsNegCC20WeilSum(g,F_g)` | `docs/proofs/final-sign-bridge-proof-package.md` | confirm `QW(g,g)=-sum_v W_v(F_g)` for the same `F_g` |
| inequality direction | `SourceQWNonnegativeToCC20Nonpositive(g,F_g)` | `docs/proofs/final-sign-bridge-proof-package.md` | confirm the proof multiplies by `-1` and feeds the CC20 nonpositive inequality |

## Rejection Conditions

A reviewer should reject this row if one of these conditions occurs:

```text
1. QW(g,g) and sum_v W_v(F_g) use different test objects;
2. the finite-prime sign is absorbed by a route convention instead of source formula;
3. the archimedean sign differs from CC20's convention;
4. the pole term is omitted or counted twice;
5. the final implication uses QW(g,g) >= 0 with the wrong sign.
```

## Current Judgment

| question | answer |
|---|---|
| Does this packet make the final sign bridge accepted-source? | no |
| Does it give an exact accepted-source review packet? | yes |
| What remains? | external acceptance of the sign, pole, finite-prime, and test bridges |
| Did this pass touch Lean? | no |

The final sign bridge now has a review packet. It remains route-evidence until
a referee or formal proof accepts the exact sign theorem.
