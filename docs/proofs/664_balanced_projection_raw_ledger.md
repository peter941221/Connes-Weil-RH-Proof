# Proof 664: balanced projection/raw ledger

## Result

This proof is useful but does **not** close Bone 1A. It expands Proof 663's
balanced response into the two terms that must still cancel on the same
object.

Let

```text
K_S   = unpolarized restricted Euler frame,
G_S   = K_S^dagger K_S,
R_S   = G_S^(-1/2),
L_S   = R_S G_S,
B_0   = J^dagger W J,
Raw_S = actual raw quadratic response.
```

Define

```text
LeftBand_S
  = B_0 - G_S^(-1) K_S^dagger W K_S,

BalancedRaw_S
  = R_S Raw_S L_S.
```

Lean first proves the exact polar-gauge collapse

```text
R_S PolarCompression_S L_S
  = G_S^(-1) K_S^dagger W K_S.
```

Consequently Proof 663's balanced mismatch satisfies

```text
X_S = B_0 - LeftBand_S - BalancedRaw_S.
```

Subtracting adjacent suffixes cancels only the fixed source compression:

```text
X_S - X_(p::S)
  = LeftBand_(p::S) - LeftBand_S
    + BalancedRaw_(p::S) - BalancedRaw_S.
```

## Target projection readback

Let `P_S` be the range projection of the polar frame. Lean identifies it
with the canonical Gram-corrected projection of `K_S`:

```text
P_S = K_S G_S^(-1) K_S^dagger.
```

Writing `T_S` for the complete Euler transport and

```text
C_S = W P_S - P_S W,
```

the literal-list rectangular target collapse gives

```text
LeftBand_S
  = J^dagger T_S^(-1) (I-P_S) C_S T_S J
  = TargetBoundary_S.
```

The standard projection-first commutator has the opposite sign. Proof 658
therefore supplies the legitimate inner estimate

```text
||C_(p::S)-C_S|| <= 8 q_p ||W||.
```

This estimate applies only to `C_S`. It does not bound the completed
`TargetBoundary` difference because the suffix-dependent inverse/forward
transports still surround the commutator.

## Active bottom

The exact completed adjacent ledger is

```text
X_S - X_(p::S)
  = TargetBoundary_(p::S) - TargetBoundary_S
    + BalancedRaw_(p::S) - BalancedRaw_S.
```

Combined with Proof 663, the remaining route-scaled ambient response is

```text
q_p^(-1/2) K_(p::S)
  [TargetBoundary_(p::S) - TargetBoundary_S
   + BalancedRaw_(p::S) - BalancedRaw_S]
  R_S.
```

The next producer must prove a suffix-uniform `O(sqrt(q_p))` bound for this
completed product. It is not legal to estimate the target-boundary and raw
increments separately and then invoke the adjacent projection gap: the
required cancellation is precisely their recombination.

Lean packages this completed column as
`routeScaledBalancedTargetRawLedgerColumn` and proves
`exists_routeUniformScaledCompleteTargetBound_iff_targetRawLedger`.
Thus the existing Bone 1A route predicate consumes the new ledger with the
same bound; this is not merely a detached operator identity.

## Lean artifacts

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrier
  AntiresonantInteriorBalancedProjectionRawLedger.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrier
  AntiresonantInteriorBalancedProjectionRawLedgerAudit.lean
```

## Verification

The Windows truth source was copied to the Ubuntu-24.04 WSL2 ext4 mirror and
built under the shared Lake lock.

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| Proof 664 focused source             |  3451 | PASS   |
| Proof 664 focused axiom audit        |   n/a | PASS   |
| CCM25Concrete aggregate              |  3939 | PASS   |
| full repository                      |  4020 | PASS   |
+--------------------------------------+-------+--------+
```

All fifteen audited theorems use exactly
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, or user axiom
was added. Bone 1A, the Proof 656 factor, Gate 3U, the finite-S sign, Burnol's
identity, and `_root_.RiemannHypothesis` remain open.
