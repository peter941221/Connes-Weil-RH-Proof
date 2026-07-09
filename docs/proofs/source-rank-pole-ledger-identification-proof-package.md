# Source Rank Pole Ledger Identification Proof Package

Status: route-evidence proof package for Row 5 of the sign/defect discharge
ledger.

This package proves the project-level bridge targeted by:

```text
docs/proofs/source-rank-pole-ledger-identification-theorem-contract.md
```

It is not a CC20, CCM24, or CCM25 source import. It is not a Lean theorem. It
does not prove endpoint-strip `Cdef` domination or no-hidden-defect equality.

## Result

Good result:

```text
SourceRankPoleLedgerIdentification is closed at route-evidence level.
```

Boundary:

```text
This package itself does not prove endpoint-strip Cdef domination or
no-hidden-defect equality.
Global ledger status now has Rows 6-7 closed at route-evidence level.
The RH proof is not complete.
```

## Target

For the no-strip part exposed by Row 4:

```text
TransportedCC20PostQRemainder
  =
no-strip channels
  +
endpoint-strip normal-form channels,
```

prove:

```text
SourceRankPoleLedgerIdentification(S,I,lambda,g,F_g):
  every no-strip channel is Rank_(S,I)(g) or PoleJetExtra_(S,I)(g), and both
  vanish under the route triple-vanishing conditions.
```

## Evidence Boundary

| claim | evidence |
|---|---|
| Row 4 no-strip split | `docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md:335-343` |
| no-strip channels are `hat g(0)`, `hat g(+i/2)`, `hat g(-i/2)` | `docs/proofs/battle-1-test-quotient-proof-package.md:60-68`, `329-356` |
| rank is zero-mode | `docs/proofs/rank-repair-finite-normal-form.md:89-143`, `374-399` |
| CCM25 pole functional and route pole ledger separation | `docs/proofs/fixed-s-no-defect-compact-form-read-off.md:133-143`; `docs/proofs/ccm25-restricted-read-off-discharge.md:310-371` |
| no extra no-strip channel | `docs/proofs/fixed-s-no-defect-compact-form-read-off.md:193-227` |
| manuscript ledger statement | `docs/manuscripts/connes-weil-rh-proof-draft.md:865-878`, `1004-1011`, `1169-1172` |

## Proof Skeleton

```text
Row 4 no-strip channels
        |
        v
three evaluations only:
  hat g(0), hat g(+i/2), hat g(-i/2)
        |
        +-- hat g(0)
        |     -> Rank_(S,I)(g)
        |
        +-- hat g(+i/2), hat g(-i/2)
              -> PoleJetExtra_(S,I)(g)
        |
        v
triple vanishing kills rank and pole ledgers
```

The proof stops before endpoint-strip `Cdef` domination.

## Lemma 1. Source No-Strip Channels Are The Three Evaluation Channels

Statement:

```text
SourceNoStripChannelsForTransportedRemainder(S,I,lambda,g,F_g):
  the no-strip part of the transported source remainder has only
  hat g(0), hat g(+i/2), and hat g(-i/2).
```

Proof.

Row 4 sends every non-no-strip part of `TransportedCC20PostQRemainder` into
endpoint-strip projection-defect normal form. Therefore Row 5 sees only the
no-strip channels.

Battle 1 identifies the no-strip finite-dimensional quotient channels as:

```text
Tate pole channels:  hat g(+i/2), hat g(-i/2)
rank channel:        hat g(0).
```

Evidence:

```text
docs/proofs/battle-1-test-quotient-proof-package.md:60-68
```

The conditional Battle 1 result repeats the same three channels and excludes
finite-prime quotient channels:

```text
docs/proofs/battle-1-test-quotient-proof-package.md:329-339
```

Output:

```text
zero_mode_channel
positive_Tate_channel
negative_Tate_channel
no_finite_prime_channel
```

## Lemma 2. Rank Ledger Is The Zero-Mode Channel

Statement:

```text
SourceRankLedgerIdentification(S,I,g):
  Rank_(S,I)(g)=C_(S,I)|hat g(0)|^2.
```

Proof.

Rank repair proves that pure Euler rank terms act by scalar multiplication on
the zero-mode functional:

```text
(A_S hat h)(0)=A_S(0) hat h(0).
```

Evidence:

```text
docs/proofs/rank-repair-finite-normal-form.md:89-143
```

Every non-pure rank-repair term contains a projection/Euler commutator and was
already routed by Row 4 to endpoint-strip normal form. The remaining no-strip
rank repair is:

```text
C_(S,I)|hat g(0)|^2.
```

Evidence:

```text
docs/proofs/rank-repair-finite-normal-form.md:374-399
```

Output:

```text
rank_channel_is_zero_mode
rank_constant_depends_on_fixed_S_I
rank_no_other_evaluation
```

## Lemma 3. Pole Ledger Is The Two Tate Channels

Statement:

```text
SourcePoleLedgerIdentification(S,I,g):
  PoleJetExtra_(S,I)(g) uses only hat g(+i/2) and hat g(-i/2).
```

Proof.

Battle 1 identifies the Tate quotient directions with:

```text
W_(0,2)(F_g)
```

supported only at:

```text
hat g(+i/2), hat g(-i/2).
```

Evidence:

```text
docs/proofs/battle-1-test-quotient-proof-package.md:139-227
```

The CCM25 pole functional inside `QW_lambda` is:

```text
W_(0,2)(F)=hat F(i/2)+hat F(-i/2),
```

and the restricted quadratic form contains:

```text
2 Re(hat g(i/2) overline{hat g(-i/2)}).
```

Evidence:

```text
docs/proofs/ccm25-restricted-read-off-discharge.md:310-371
```

The route `PoleJetExtra_(S,I)(g)` remains outside `QW_lambda`. It records the
fixed-S positive-trace quotient directions before triple vanishing kills them.
The proof must keep this occurrence separate from the CCM25 pole term already
inside `QW_lambda`.

Output:

```text
pole_channel_positive_i_half
pole_channel_negative_i_half
pole_ledger_outside_QW_lambda
CCM25_pole_functional_not_double_counted
```

## Lemma 4. No Extra No-Strip Channel

Statement:

```text
SourceNoExtraNoStripChannel(S,I,lambda,g,F_g):
  after Row 4 and the CCM25 no-defect read-off, no no-strip derivative,
  finite-prime, or extra positive rank channel remains.
```

Proof.

The no-defect compact-form read-off states that after Battle 2 separates
projection-order defects and after Battle 1 records the rank/pole ledgers, the
no-defect CCM25 read-off has no additional no-strip rank, pole, or
derivative-jet channel.

Evidence:

```text
docs/proofs/fixed-s-no-defect-compact-form-read-off.md:193-227
```

Finite-prime terms remain inside the CCM25 finite-prime Weil ledger. They do
not enter through quotient no-strip channels.

Output:

```text
no_finite_prime_quotient_channel
no_derivative_jet_channel
no_extra_positive_rank_channel
no_strip_channels_exhausted
```

## Lemma 5. Ledger Vanishing Gate

Statement:

```text
SourceRankPoleLedgerVanishingGate(S,I,g):
  if hat g(0)=hat g(+i/2)=hat g(-i/2)=0, then
  Rank_(S,I)(g)=0 and PoleJetExtra_(S,I)(g)=0.
```

Proof.

By Lemma 2:

```text
Rank_(S,I)(g)=C_(S,I)|hat g(0)|^2.
```

So `hat g(0)=0` kills the rank ledger.

By Lemma 3, `PoleJetExtra_(S,I)(g)` uses only:

```text
hat g(+i/2), hat g(-i/2).
```

Thus the two Tate vanishings kill the pole ledger.

This is the first point where triple vanishing is used. It is not used to
classify terms, and it does not prove endpoint-strip `Cdef` domination.

Output:

```text
triple_vanishing_applied_after_identification
rank_vanishes_from_zero_mode
pole_vanishes_from_Tate_channels
no_Cdef_claim_from_vanishing
```

## Theorem. Source Rank Pole Ledger Identification

Statement:

```text
SourceRankPoleLedgerIdentification(S,I,lambda,g,F_g):
  every no-strip channel in the transported source remainder is exactly
  Rank_(S,I)(g) or PoleJetExtra_(S,I)(g), and both ledgers vanish under triple
  vanishing.
```

Proof.

Combine Lemmas 1 through 5.

The proof uses:

```text
Row 4 no-strip/projection split,
Battle 1 quotient-channel identification,
rank-repair zero-mode normal form,
CCM25 pole separation,
no-defect no-extra-channel read-off.
```

It does not use:

```text
endpoint-strip Cdef domination,
fixed-test Cdef exhaustion,
no-hidden-defect equality,
or lambda -> infinity.
```

## Output To The Discharge Ledger

This package supplies, at route-evidence level:

```text
SourceRankPoleLedgerIdentification
SourceRankPoleLedgerVanishingGate
```

It does not supply:

```text
SourceEndpointStripRemainderCdefDomination
NoHiddenPositiveDefectOutsideCdef
SoninProlateDefectEqualsEndpointStripCdef
```

## Current Status

```text
No-strip channel list:                  proved at route-evidence level
Rank ledger identification:             proved at route-evidence level
Pole ledger identification:             proved at route-evidence level
No extra no-strip channel:              proved at route-evidence level
Ledger vanishing gate:                  proved at route-evidence level
Row 5 rank/pole identification:         proved at route-evidence level

Rows 6-7 global ledger status:          proved at route-evidence level
Accepted source-import status:          open
Lean proof status:                      open
RH proof:                               not complete
```
