# RH 887 — axiom ledger: how far the `RiemannHypothesis` output is from unconditional

Date: 2026-08-08. Status: build-independent static audit of `UnconditionalSkeleton.lean`.
Purpose: quantify how far the repository is from an unconditional RH claim by listing
every `axiom` the skeleton's `_root_.RiemannHypothesis` output depends on, and classifying
each against the documented gates. The authoritative kernel hook (`#print axioms`) is §4.

## 0. The honest bottom line (evidence-first)

`ConnesWeilRH/Dev/UnconditionalSkeleton.lean` says, in its own header (lines 16-28), that
it is a temporary checklist skeleton (items 6-15), NOT a claimed RH library: every
declaration must be replaced by concrete proofs or clean theorem imports before any final
`unconditional_rh` theorem is claimed, and the unresolved bottoms are kept as explicit
proposition `axiom`s named `...Root` (removing `sorryAx` without claiming those roots are
producers).

The final output `rhDefinitionBridgeToMathlibFromTheorems : _root_.RiemannHypothesis`
(line 8055) routes through the `FromTheorems` / `From08A` chain that bottoms on these
`...Root` axioms. So the repository does not prove RH unconditionally; consistent with
AGENTS §1 / §2.

## 1. Full axiom inventory (exact source locations)

41 `axiom` declarations found in `UnconditionalSkeleton.lean`:

| #   | line | name | note |
|-----|------|------|------|
| 1   |  154 | normalizedCoreSourceWeilFormDataRoot | empty model (guard). Lane B |
| 2   |  670 | normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot | finite-prime data. Lane B |
| 3   | 1080 | normalizedCoreS2B1RemainderRowsOutsideNoBulkRoot | S2B1 rows |
| 4   | 1089 | normalizedCoreS2B1TracePackageRemaindersRoot | trace remainders |
| 5   | 1564 | normalizedCoreCC20PropositionC1SourceCriterionRoot | C1 sign. Lane R (RH-equiv) |
| 6   | 1678 | normalizedSourceObjectReadOffRowsInputRoot | object bridge rows |
| 7   | 1719 | normalizedSourceObjectScalarRemainderRowsProviderRoot | scalar rows |
| 8   | 2728 | normalizedSelectedFinitePrimeIndexDifferenceInputRoot | idx-diff input. Lane B |
| 9   | 4749 | normalizedRestrictedToFullFinitePrimeIndexDifferenceRowsRoot | threshold rows. Lane B |
| 10  | 5896 | normalizedSelectedYoshidaDetectorPolePairingNonnegativeCoreRoot | RH-equiv (Lane R) |
| 11-41 | 7754-7894 | normalizedSelectedFinalRoute*Root (30) | final-route certificate rows |

## 2. Classification (four lanes)

- Lane R - RH-equivalent (the two hard axioms): #5 (C1) and #10 (Yoshida). Each sits beside
  a library theorem that its proposition is `_root_.RiemannHypothesis` (#5 at lines
  1555-1559, #10 at 5890-5894). These axioms ARE the RH claim wrapped in model language. They
  cannot be discharged by replacing with a healthy-carrier datum; only an actual RH proof
  removes them.
- Lane A - healthy-carrier sign/trace content a future RH proof could assemble: the arch-sign
  datum (HilbertSignArchCorrected / HilbertArchSignHSData) and the half-density Mellin law.
  These are re-typed inputs, not the axioms themselves.
- Lane B - broken concrete model, must be re-typed not proved in place: #1 SourceWeilFormData
  is empty, and the finite-prime/pole rows (#2,#8,#9) force additive-vs-Mellin convolution
  `2=1`. Their issues must move to the CompactLog model.
- Lane C - analytic operator bottom: trace assembly + Gate-3U/Proof-717 `(I-P)F = -(I-P)D`
  (docs/872 §7) and infinite-carrier prolate trace-class `hfactor` (docs/867). Finite piece
  closed; infinite seam open.

## 3. Quantitative reading

- ~10 axioms are model / ground / RH-edge axes (lines 154-5896): two (5,10) are RH-equivalent,
  ~8 are broken-model or ground.
- ~30 axioms (lines 7754-7894) are final-route certificate/threshold package rows, largely
  data the Compact carrier can carry as resolved proofs.

Closing unconditional RH = prove the analytic core (Lane C) + re-type the broken model
(Lane B) + assemble Lane A so that Lane R's RH-equivalent axioms are discharged, never merely
kept. This ledger is the auditable record of "which of those items remain".

## 4. One-command kernel audit (after the skeleton module is built)

```sh
cat > _axrh.lean <<EOF
import ConnesWeilRH.Dev.UnconditionalSkeleton
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.rhDefinitionBridgeToMathlibFromTheorems
EOF
lake env lean _axrh.lean
```
Expected: while RH is unproven, the output still lists each `...Root` axiom.

## 5. What this artifact does not claim

An axiom ledger does not close RH. It converts "the repo does not yet prove RH" into a
concrete per-axiom inventory so closure is not faked by a build that merely replays the
`...Root` axioms.