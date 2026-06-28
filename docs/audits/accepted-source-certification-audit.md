# Accepted Source Certification Audit

Status: external-review checklist for the source-conditional route.

This audit is the next layer after the proof-package matrix. It asks which
claims an outside reader must accept as source theorems, referee-checkable
project proofs, or later Lean theorems before the route can move beyond
source-conditional status.

## Result

Good result:

```text
The route now has a complete route-evidence proof chain and a complete
proof-package matrix for the exposed source-interface rows.
```

Certification result:

```text
No source-interface row has yet been upgraded to accepted-source status or to a
Lean theorem with audited axioms.
```

The current artifact should be sent out as:

```text
source-conditional route evidence for external mathematical review.
```

It should not be described as an unconditional proof, accepted source proof,
journal proof, Clay proof, or completed Lean proof.

## Evidence Base

| evidence | review use |
|---|---|
| `docs/audits/source-reread-v0.2.md:29-52` | locates the CCM24, CCM25, and CC20 source-line ranges used by the route |
| `docs/audits/source-interface-discharge-completion-audit.md:14-25` | records that every source-interface row has a named proof package and that no row is yet accepted-source or Lean discharged |
| `docs/audits/source-import-legitimacy-audit.md:266-280` | records the current source-import judgment for CCM24, CCM25, and CC20 |
| `docs/audits/sign-defect-blocker-audit.md:223-225` | records that the hostile sign/defect objection is answered at route-evidence strength, not accepted-source or Lean strength |
| `docs/proofs/cc20-source-remainder-rows1-2-referee-discharge.md:464-472` | records Rows 1-2 and Rows 3-7 as closed at project proof-package level, with accepted-source certification open |
| `docs/proofs/sonin-prolate-defect-referee-discharge.md:457-466` | records Rows 3-7, no-hidden-defect equality, and finite-lambda lower bound at project proof-package strength |
| `docs/audits/restricted-to-full-qw-source-readiness-audit.md:159-173` | records the fixed-test `QW_lambda=QW` bridge as route-evidence only |
| `docs/proofs/final-sign-bridge-proof-package.md:21-35` | records the final CCM25-to-CC20 sign bridge as route-evidence only |
| `docs/proofs/rh-definition-bridge-proof-package.md:22-36` | records the RH definition bridge as route-evidence only |
| `docs/proofs/source-conditional-rh-route-closure-proof-package.md:333-350` | records the full route composition as closed at route-evidence level, with source-import, Lean, and external certification open |
| `docs/audits/accepted-source-theorem-upgrade-ledger.md` | states row-level accepted-source theorem candidates, source anchors, current evidence, and upgrade blockers |
| `docs/audits/trace-scale-source-term-ledger.md` | starts the first S2-B1 accepted-source packet by mapping possible trace-scale source terms to `QW_lambda`, rank, pole, or endpoint-strip `Cdef` |
| `docs/audits/sign-defect-accepted-source-packet.md` | starts the Rows 1-7 sign/defect accepted-source packet, from CC20 post-`Q` source remainder through fixed-S transport and no-hidden-defect equality |
| `docs/audits/restricted-to-full-accepted-source-packet.md` | starts the restricted-to-full accepted-source packet for fixed-test `QW_lambda(g,g)=QW(g,g)` without spectral convergence |

## Acceptance Classes

| class | what an outside reviewer should check | route strength |
|---|---|---|
| source line located | the cited source file contains the object, formula, or theorem shape | evidence location only |
| proof package written | this repository gives a manuscript-level derivation from cited source inputs | route evidence |
| accepted source import | a source theorem, referee, or external proof accepts the exact theorem statement and hypotheses | certification input |
| Lean theorem | Lean proves the route theorem and `#print axioms` leaves only approved source interfaces and kernel foundations | formal certification input |

The route has reached the second class for the full chain. The external review
task is to upgrade specific rows to the third class or mark them for Lean.

## Source-Facing Rows To Review

| row | current evidence | reviewer question |
|---|---|---|
| CCM24 fixed-S model and window transport | `source-reread-v0.2.md:37-40`; `source-interface-discharge-completion-audit.md:36-48` | Do the CCM24 source hypotheses give the exact fixed `S`, support window, Fourier window, bounded comparison, and Sonin comparison used by the route? |
| CCM25 `QW`, `Psi`, and `QW_lambda` | `source-reread-v0.2.md:41-42`; `source-interface-discharge-completion-audit.md:56-68` | Do the source formulas match the route test object, lambda window, pole term, finite-prime indexing, and sign convention? |
| CC20 trace legality and support-square read-off | `source-reread-v0.2.md:43-49`; `source-interface-discharge-completion-audit.md:78-91` | Do the CC20 trace-class, cyclicity, Mellin, and sign conventions apply to the exact transported test object used here? |
| Rows 1-2 CC20 source remainder orientation | `cc20-source-remainder-rows1-2-referee-discharge.md:1-24`; `cc20-source-remainder-rows1-2-referee-discharge.md:449-472` | Does CC20 supply the `D=L-W_infty`, `E=S-W_infty`, and post-`Q` image used as the source remainder entering Row 3? |
| Rows 3-7 sign/defect bridge | `sonin-prolate-defect-referee-discharge.md:1-38`; `sonin-prolate-defect-referee-discharge.md:433-466` | Does the project proof correctly transport and classify the CC20 post-`Q` remainder into killed rank/pole ledgers plus endpoint-strip `Cdef`, with no fourth positive defect? |
| restricted-to-full `QW_lambda=QW` | `restricted-to-full-qw-source-readiness-audit.md:18-21`; `restricted-to-full-qw-source-readiness-audit.md:140-173` | Does the fixed-test bridge follow from the CCM25 restriction definition plus common-test, window, and finite-prime support stabilization, without spectral convergence? |
| final sign bridge | `final-sign-bridge-proof-package.md:18-35`; `final-sign-bridge-proof-package.md:340-350` | Does `QW(g,g) = - sum_v W_v(F_g)` hold with the displayed signs, so that `QW(g,g) >= 0` becomes the CC20 nonpositivity hypothesis? |
| CC20 finite-vanishing exit and RH definition bridge | `rh-definition-bridge-proof-package.md:19-36`; `rh-definition-bridge-proof-package.md:305-314` | Does the CC20 source RH conclusion transport to Mathlib's `_root_.RiemannHypothesis` with the same zeta function, zero predicate, exclusions, and critical-line equation? |
| S2-B1 trace-scale source-term ledger | `trace-scale-source-term-ledger.md` | Does every source-owned scalar in the positive-trace read-off land in `QW_lambda`, rank, pole, or endpoint-strip `Cdef`, with no untracked divergent bulk or hidden finite-part subtraction? |
| sign/defect accepted-source packet | `sign-defect-accepted-source-packet.md` | Does a referee accept the Rows 1-7 source-owned classification theorem, including fixed-S transport, rank/pole identification, endpoint-strip `Cdef`, and no hidden positive defect? |
| restricted-to-full accepted-source packet | `restricted-to-full-accepted-source-packet.md` | Does a referee accept eventual fixed-test scalar equality from CCM25 restriction-definition, support containment, and finite-prime stabilization, with no spectral input? |

## Non-Importable Shortcuts

These claims must not be used as accepted source imports:

| shortcut | replacement in this repository |
|---|---|
| CCM25 finite-operator spectral convergence to zeta zeros | fixed-test scalar `QW_lambda(g,g)=QW(g,g)` bridge through the CCM25 restriction definition |
| determinant convergence toward Xi | not used in the route theorem |
| automatic harmless Sonin/prolate defect | Rows 1-7 sign/defect proof chain |
| automatic CCM24 transport for post-`Q` derivative, boundary, and tail terms | Row 3 split into bulk graph transfer, boundary functional transfer, and series-tail bounded comparison |
| source-paper statement ending in "RH" equals Mathlib RH by name | RH definition bridge through zeta equality, zero transport, exclusions, and `s.re=1/2` |

## Review Order

An outside reviewer should check the route in this order:

```text
1. Source objects:
   one test g, one convolution square F_g, one tuple (S,I,lambda).

2. Trace legality:
   Hilbert-Schmidt, trace-class, and cyclicity before positivity and trace
   read-off.

3. CCM25 arithmetic normalization:
   QW, QW_lambda, pole term, finite-prime support, von Mangoldt weights, and
   prime-power pairing.

4. Sign/defect bridge:
   CC20 source remainder -> fixed-S transport -> rank/pole/Cdef
   classification -> no hidden positive defect.

5. Restricted-to-full:
   fixed-test QW_lambda(g,g)=QW(g,g), not spectral convergence.

6. Final exit:
   QW(g,g)=-sum_v W_v(F_g), CC20 Proposition C.1 with F={0,1/2,1}, and the
   source-RH-to-Mathlib-RH definition bridge.
```

## Current Judgment

| question | answer |
|---|---|
| Does the repository now give a complete route-evidence chain? | yes |
| Does the chain answer the earlier hostile sign/defect criticism at project proof-package strength? | yes |
| Does the chain avoid importing CCM25 spectral convergence? | yes |
| Does any source-interface row have accepted-source certification? | no |
| Does any route closure theorem currently count as a discharged Lean proof of RH? | no |
| Is the artifact ready for external mathematical review? | yes, as source-conditional route evidence |

The next useful external response is not a broad opinion on RH. It is a row-by
row verdict on whether the source-facing rows above count as accepted theorem
inputs, need revision, or should be encoded as Lean source interfaces.
