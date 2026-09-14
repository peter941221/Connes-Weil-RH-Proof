# 1428 - R3 doubled-shift Hardy involution

Date: 2026-09-14.

Status: `FORMAL / GREEN`; this is a new structural normal form for R3. It
does not prove the cutoff trace limit, the prolate remainder estimate,
`G8SameOwnerReadbackData`, `qw >= 0`, or RH.

## 1. The new object

The exact scale transport in R3 moves the radial and Fourier projections in
opposite directions. After conjugating one side to unit scale, the remaining
relative motion is twice the logarithmic scale parameter. Let `T_b` denote the
global logarithmic translation and `H` the committed global
Hardy--Titchmarsh operator. The new operator is

```text
K_b = T_(2*b) H.
```

This is not a numerical model and does not replace the finite-S source owner.
It is defined on the committed `finiteSCarrier`, the same global logarithmic
carrier used by the R3 Hardy transport.

## 2. Exact theorem

The new leaf
`ConnesWeilRH/Dev/C1G8R3DoubledShiftNormalForm.lean` proves

```text
doubledShiftHardy b * doubledShiftHardy b = id
```

for every real `b`, where the displayed multiplication is composition of
continuous linear maps. The proof uses only the already formal pointwise
identities

```text
H (T_a u) = T_(-a) (H u)
H (H u) = u
T_a (T_c u) = T_(a+c) u.
```

Thus the new scale parameter is not an arbitrary perturbation: it produces a
one-parameter family of exact involutions. This isolates the remaining R3
dependence in the relative displacement between the source half-line
projection and `K_b`, rather than in a spurious failure of Hardy covariance.

## 3. Why this matters for R3

The target consumer remains the healthy-`CompactLog`, B5-shaped statement
`0 <= C1SameOwnerWeil.qw g` for the detector selected against a hypothetical
off-line zero. The new involution does not supply that sign. Its value is that
future trace estimates can be organized around a fixed algebraic object with
`K_b^2 = id`:

```text
scale-dependent source trace
  -> relative-shift operator K_b
  -> source second-support prolate remainder and leakage estimate
  -> cutoff/source-ledger compatibility
  -> same-owner Weil readback.
```

The last three arrows remain open. In particular, involutivity alone gives no
trace-classness, no summability, no cutoff limit, and no positivity.

## 4. Acceptance

Build log: `build-logs/1428_doubled_shift_try20.log`.

```text
targets                         2 (main leaf + audit)
footer                          Build completed successfully (3175 jobs)
error lines                     0
sorryAx                         0
audited axiom print             [propext, Classical.choice, Quot.sound]
```

No detector-health premise, `SourceRH`, or universal Weil positivity is used.
