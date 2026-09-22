# Record 1805 — C3' Round 2A signed-balance reduction

Date: 2026-09-22.

Status: formal reduction complete; the C3' sign, SourceRH, and RH remain open.

## Result

`C1C3CarrierTransport` now proves two same-owner identities:

- `carrierMixedDeterminantPhase_signed_expansion` rewrites the mixed
  Archimedean/prime discrepancy using the square and pair prime
  credit-deficit owners.
- `carrier_twoSpan_phase_budget_signed_balance` rewrites the full three-term
  phase budget using those owners and the signed prime determinant expansion.

The resulting target is exactly:

```text
Archimedean determinant
+ square/pair Archimedean terms times signed prime balances
+ square signed-prime product minus pair signed-prime square
<= 0
```

No pointwise sign, absolute-value replacement, frozen prime set, or continuous
prime approximation is introduced.

## Verification

The owning leaf and paired Audit build completed successfully in the ext4
mirror: 3785 jobs, zero `error:` lines, zero `sorryAx`, and only
`[propext, Classical.choice, Quot.sound]` in the new focused axiom prints.

## Remaining Round 2B target

The remaining mathematical task is the actual signed estimate for the
selected detector. In particular, the formal sigma-tail result is not yet a
theorem about the Archimedean determinant owner, and the mixed and prime
credit-deficit terms still require bounds on the same physical phase cells.
This record therefore closes only Round 2A, not Round 2.
