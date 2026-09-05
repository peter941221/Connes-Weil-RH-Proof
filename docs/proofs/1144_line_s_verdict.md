# Record 1144 - Line S verdict: REFUTED at identity level (armchair)

Date: 2026-09-05.

Status: falsifier resolution for map
[`005`](../map/005_p2_scalar_witness_zero_configuration_design.md)
section 4.1.  No probe was run and none is needed; this record changes no
route selection, closes no obligation, and claims no sign.  RH is not
claimed.

## 1. Line S as registered

Map 005 section 4.1 registered the channel-cancellation producer: rewrite
`ICgate (defect)` through the arithmetic-spectral balance (Z3) into its
zero-sum form, split the spectral difference into channels (the rho-term
carrying the detection mass, the on-line-zero background termwise
nonnegative, vanishing pole terms), and show the window cross-terms absorb
the detection channel - a Weil-criterion-shaped rearrangement yielding the
witness field `hdec : ICgate (ICdefect ...) <= epsilon`.

Registered falsifier: a model-level channel decomposition on the
record-1116 twin at the true `delta = 0` configuration; if no admissible
window cross-term covers the detection channel, Line S dies as stated.

## 2. The identity-level refutation

Record 1143 (`ConnesWeilRH.Source.C1P2DefectZeroSumIdentity`, axioms
exactly `[propext, Classical.choice, Quot.sound]`) pins the statement
level:

```text
S2  defectGate_eq_qw_sub            ICgate (ICdefect g W) = qw W - qw g
S3  defectGate_eq_spectralValue_sub ICgate (ICdefect g W)
                                      = SW W.convSq - SW g.convSq
S5  defectGate_gt_add_mu_of_qw_negative
    (vanishing g) -> qw g < 0 -> ICgate W.convSq <= -mu
    -> mu < ICgate (ICdefect g W)
```

The refutation is three lines:

1. The defect gate is ONE number, and S3 identifies it exactly as the
   spectral difference `SW W.convSq - SW g.convSq`.  Any channel
   decomposition of that difference is a partition of the same number:
   the channels sum to `ICgate (ICdefect ...)`, not to anything else.
   Rearrangement cannot change the truth value of `hdec`, which
   constrains the whole.

2. On every detector to which the P2 producer applies - a right
   off-line-zero detector with `qw g < 0` - S5 forces
   `ICgate (ICdefect ...) > mu`, given exactly the window certificate
   `hcert` that the producer itself must supply.  (The positivity
   `0 < ICgate g.convSq` is re-derived from the detector's spectral
   negativity `qw g < 0` plus triple vanishing, the same arithmetic
   already used inside `no_stageB_budget_of_qw_negative`,
   `C1T2Assembly.lean:293`.)

3. Therefore the hypothesis set `{qw g < 0, hcert, hdec, hmargin}` is
   inconsistent (1140, kernel-checked), and the inconsistency is reached
   WITHOUT unfolding any channel structure.  A channel identity strong
   enough to make `hdec` true on a negative detector would have to
   violate S3 itself, since S3 fixes the quantity `hdec` constrains.

Hence no admissible window cross-term can "cover the detection channel"
in the required sense: partial or full cancellation is invisible at the
level where `hdec` is stated, and the total is pinned above `mu >= epsilon`
whenever the detector is negative.  The registered falsifier resolves
negatively on the identity alone; running the 1116-twin probe would
measure a quantity already known to exceed the budget in every
instantiation, which is the AGENTS rule 1 anti-pattern (numerically idle
experiment).

## 3. Scope of the verdict

```text
+---------------------------------------------+---------------------------+
| Claim                                       | Status                    |
+---------------------------------------------+---------------------------+
| Channel-cancellation as a producer of hdec  | DEAD (this record)        |
| (Line S as registered in map 005 4.1)       |                           |
+---------------------------------------------+---------------------------+
| Estimate-sized budgets (DR2)                | Already dead (1140), now  |
|                                             | also dead quantitatively  |
|                                             | (record 1142: 6-13 orders)|
+---------------------------------------------+---------------------------+
| Lines B (Bombieri eigensystem) and          | ALIVE, unchanged; they do |
| C (correction-remainder algebra)            | not pass through channel  |
|                                             | rearrangement of the      |
|                                             | defect difference         |
+---------------------------------------------+---------------------------+
| The P2 obligation itself                    | OPEN; RH-equivalent per   |
|                                             | map 005 2.3               |
+---------------------------------------------+---------------------------+
```

Sharpened reading for the surviving lines (consistent with map 005
checklist A3, now with a formal backing): since the witness fields are
REFUTED on every negative detector, any P2 producer proof must either
first establish the detector sign `qw g >= 0` for the pinned detector or
proceed by contradiction on the detector branch.  There is no
budget-only shortcut: the budget fields are inconsistent with the
detector branch (1140), so producer work and the semi-local sign are the
same mathematical content, as map 005 section 2.3 anticipated.  This is
also why record 1142's scale wall was never an obstruction to the route
itself: in the RH-consistent world the witness is vacuous, and in the
off-line-zero world it is refutable.

## 4. Map changes

Map 005 section 4.1 is marked REFUTED (this record); section 6 marks B1
LANDED (record 1143) and B2 LANDED (record 1142).  Lines B and C and
pre-bricks B3/B4 are unchanged.  No binding record is touched; the route
remains map [`003`](../map/003_b1_b5_minimal_exit_route_selection.md).

## 5. Verification

No numerical content.  Every cited step is a kernel-checked Lean
declaration in `ConnesWeilRH.Source.C1P2DefectZeroSumIdentity` (record
1143) or `ConnesWeilRH.Source.C1T2Assembly` (`no_stageB_budget_of_qw_negative`,
`defectGate_singleton_eq_sub`), with axiom audits exactly
`[propext, Classical.choice, Quot.sound]` (build log
`c1p2-zero-sum-identity.log`, 3658 jobs, zero errors).
