# Source Rank Pole Ledger Identification Theorem Contract

Status: project-proof theorem contract for Row 5 of the sign/defect discharge
ledger.

This contract sits after:

```text
docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md
```

and before endpoint-strip `Cdef` domination.

The route-evidence proof package is:

```text
docs/proofs/source-rank-pole-ledger-identification-proof-package.md
```

It aims to prove, inside the project route:

```text
SourceRankPoleLedgerIdentification(S,I,lambda,g,F_g).
```

## Boundary

This contract covers only no-strip ledger identification:

```text
source no-strip channels
  ->
Rank_(S,I)(g) and PoleJetExtra_(S,I)(g)
  ->
triple vanishing may later kill those ledgers.
```

It does not prove:

```text
endpoint-strip Cdef domination,
fixed-test Cdef exhaustion,
no-hidden-positive-defect equality,
or RH.
```

Those remain Rows 6-7 and the final RH exit.

## Evidence Inputs

| input | current evidence |
|---|---|
| Row 4 no-strip/projection-order split | `docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md` |
| Battle 1 no-strip quotient channels | `docs/proofs/battle-1-test-quotient-proof-package.md:39-68`, `288-356` |
| rank repair zero-mode normal form | `docs/proofs/rank-repair-finite-normal-form.md:89-143`, `356-399` |
| no extra no-strip channel | `docs/proofs/fixed-s-no-defect-compact-form-read-off.md:193-227` |
| CCM25 pole separation | `docs/proofs/ccm25-restricted-read-off-discharge.md:310-371` |
| manuscript no-strip ledger statement | `docs/manuscripts/connes-weil-rh-proof-draft.md:865-878`, `1004-1011`, `1169-1172` |

## Contract Theorem 1. Source No-Strip Channels

Target:

```text
SourceNoStripChannelsForTransportedRemainder(S,I,lambda,g,F_g):
  the no-strip part of TransportedCC20PostQRemainder has only the three
  evaluation channels:

    hat g(0),
    hat g(+i/2),
    hat g(-i/2).
```

Required projections:

```text
no_strip_channels_from_Row4
zero_mode_channel
positive_Tate_channel
negative_Tate_channel
no_derivative_jet_channel
no_finite_prime_channel
```

Reject:

```text
triple vanishing kills the remainder.
```

Triple vanishing may be used only after these no-strip channels have been
identified.

## Contract Theorem 2. Rank Ledger Identification

Target:

```text
SourceRankLedgerIdentification(S,I,g):
  the zero-mode no-strip channel is exactly Rank_(S,I)(g), and

    Rank_(S,I)(g) = C_(S,I) |hat g(0)|^2.
```

Required projections:

```text
rank_channel_is_zero_mode
pure_Euler_rank_scalar
rank_constant_depends_on_fixed_S_I
rank_no_other_evaluation
```

## Contract Theorem 3. Pole Ledger Identification

Target:

```text
SourcePoleLedgerIdentification(S,I,g):
  the two Tate no-strip channels are exactly PoleJetExtra_(S,I)(g), and this
  route ledger uses only hat g(+i/2) and hat g(-i/2).
```

Required projections:

```text
pole_channel_positive_i_half
pole_channel_negative_i_half
pole_ledger_outside_QW_lambda
CCM25_pole_functional_not_double_counted
```

Meaning:

The CCM25 pole functional inside `QW_lambda` and the route's extra
`PoleJetExtra` ledger both use the same two evaluations, but they are not the
same occurrence in the trace read-off. Triple vanishing later kills both.

## Contract Theorem 4. No Extra No-Strip Channel

Target:

```text
SourceNoExtraNoStripChannel(S,I,lambda,g,F_g):
  after Row 4 projection-defect splitting and CCM25 no-defect read-off, no
  no-strip channel remains outside Rank_(S,I)(g), PoleJetExtra_(S,I)(g), and
  the CCM25 main form QW_lambda(g,g).
```

Required projections:

```text
no_finite_prime_quotient_channel
no_derivative_jet_channel
no_extra_positive_rank_channel
no_strip_channels_exhausted
```

## Contract Theorem 5. Ledger Vanishing Gate

Target:

```text
SourceRankPoleLedgerVanishingGate(S,I,g):
  if

    hat g(0)=hat g(+i/2)=hat g(-i/2)=0,

  then

    Rank_(S,I)(g)=0
    PoleJetExtra_(S,I)(g)=0.
```

Required projections:

```text
triple_vanishing_applied_after_identification
rank_vanishes_from_zero_mode
pole_vanishes_from_Tate_channels
no_Cdef_claim_from_vanishing
```

## Combined Contract

Target:

```text
SourceRankPoleLedgerIdentification(S,I,lambda,g,F_g):
  SourceNoStripChannelsForTransportedRemainder
  + SourceRankLedgerIdentification
  + SourcePoleLedgerIdentification
  + SourceNoExtraNoStripChannel
  + SourceRankPoleLedgerVanishingGate.
```

Projection target:

```text
SourceRankPoleLedgerIdentification
  ->
Row 6 may handle only endpoint-strip terms as Cdef candidates.
```

## Proof Acceptance Checklist

This project proof can be accepted only if it supplies:

| requirement | required evidence |
|---|---|
| Row 4 input | no-strip channels come from the transported source remainder |
| rank equality | rank ledger is proportional to `|hat g(0)|^2` |
| pole support | pole ledger uses only `hat g(+i/2)` and `hat g(-i/2)` |
| pole separation | `PoleJetExtra` is outside `QW_lambda` and not double-counted with CCM25 `W_(0,2)` |
| no extra channel | no derivative, finite-prime, or positive rank channel remains |
| vanishing order | triple vanishing is applied only after ledger identification |

## Current Judgment

| question | answer |
|---|---|
| Is this a source import? | no |
| Does this use Row 4 output? | yes |
| Does this discharge sign/defect once stated? | no |
| What would it discharge if proved? | Row 5 no-strip rank/pole identification |

The current status is:

```text
project proof target stated;
route-evidence proof package written;
not a Lean theorem or accepted source import.
```
