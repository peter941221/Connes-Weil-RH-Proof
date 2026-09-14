# 1424 - R3 trace-legality normal form

Date: 2026-09-14.

Status: `FORMAL / SOURCE-LEDGER REDUCTION`.  This record advances R3 but does
not claim the G8 readback limit or RH.

Consumer: the healthy-`CompactLog`, B5-shaped statement
`0 <= C1SameOwnerWeil.qw g` for the detector selected against a hypothetical
off-line zero.

## 1. New theorem

The new Dev leaf
`ConnesWeilRH/Dev/C1G8R3TraceLegalityNormalForm.lean` proves

```text
IsTraceClassAlong globalBasis completeThreeBranch(owner, lambda)
  <->
IsTraceClassAlong globalBasis sourceSecondSupportProlateRemainder(owner, lambda).
```

The paired audit leaf prints the theorem's axioms.  The accepted build is
`build-logs/1424_r3_normal_form_try3.log`:

```text
Build completed successfully (3171 jobs)
error: 0
sorryAx: 0
axioms: [propext, Classical.choice, Quot.sound]
```

## 2. Why the equivalence is nontrivial

The forward direction uses the existing compact-root transport theorem to
prove that the two outer branches are trace-class, then subtracts them from
the complete three-branch commutator.  The reverse direction is the existing
outer-pair-plus-remainder theorem.

Thus the remainder is not merely a convenient sufficient hypothesis.  For
this source ledger it is the exact trace-ideal obstruction: any proof of
complete trace legality must prove the coupled remainder, and any proof of
the coupled remainder immediately restores complete trace legality.

No sign, detector-health, `qw`, `SourceRH`, universal Weil positivity, or
external dictionary is used.

## 3. Exact scope boundary

This closes the trace-legality question for the formal source three-branch
ledger.  It does not identify the sequence
`g8SourceCutoffPairData ... n` with that ledger in the limit, and it does not
prove the two fields of `G8SameOwnerReadbackData`.

The remaining R3 work is therefore sharply typed:

```text
coupled sourceSecondSupportProlateRemainder trace-ideal theorem
  + G8 cutoff-to-source-ledger transport
  + signed trace readback to qw
  -> G8SameOwnerReadbackData.
```

The first term is now an iff obstruction rather than an overbroad sufficient
condition.  The latter two are still open and retain the anti-circularity
requirements of map 012.

## 4. Verdict

```text
R3-F2 radial outer branch                  FORMAL CLOSED (source ledger)
R3-F3 remainder normal form                FORMAL GREEN
G8 cutoff/source-ledger transport          OPEN
remainder estimate / trace limit           OPEN
G8SameOwnerReadbackData                    OPEN
RH                                         NOT CLAIMED
```
