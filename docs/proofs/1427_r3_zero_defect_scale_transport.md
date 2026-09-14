# 1427 - R3-F5 zero-defect scale transport

Date: 2026-09-14.

Status: `FORMAL / GREEN`; this closes the scale-defect branch only. It does
not prove the G8 trace limit, `G8SameOwnerReadbackData`, `qw >= 0`, or RH.

## 1. Exact result

The R3-F4 leaf defined two defects for the global logarithmic translation
`T_b` and the Hardy--Titchmarsh operator `H`:

```text
D^R_b = T_b H - H T_(-b)
D^L_b = H* T_(-b) - T_b H*
```

The new leaf
`ConnesWeilRH/Dev/C1G8R3ZeroDefectClosure.lean` proves, for every real `b`,

```text
D^R_b = 0
D^L_b = 0.
```

The proof is a connection, not a new assumption. It imports the already
formal global Hardy translation theorem
`archimedeanHardyTitchmarsh_comp_globalLogTranslation` and the already formal
self-adjointness theorem
`archimedeanHardyTitchmarsh_adjoint_eq_self` from the semilocal unitarity
module. The right defect uses the translation theorem at `-b`; the left
defect uses the same theorem after self-adjointness.

## 2. Projection consequence

Combining the two zero-defect facts with the exact defect decomposition from
`C1G8R3SoninScaleDefect.lean` gives the formal theorem

```text
sourceFourierSupportProjection lambda
  = T_(log lambda) * sourceFourierSupportProjection unitSoninScale
      * T_(-log lambda).
```

This is the desired scale covariance for the actual source Fourier-support
projection. It is an operator identity on the committed global logarithmic
`L2` carrier, not a numerical approximation and not a replacement owner.

## 3. Acceptance

Build log: `build-logs/1427_zero_defect_try3.log`.

```text
targets                         2 (main leaf + audit)
footer                          Build completed successfully (3174 jobs)
error lines                     0
sorryAx                         0
audited axiom print terminators 3 (`Quot.sound]`)
audited leaves                  [propext, Classical.choice, Quot.sound]
```

## 4. What this does and does not solve

The exact scale transport removes one R3 bookkeeping obstacle: the source
projection at arbitrary `lambda` can now be moved to the unit-scale source
projection by genuine unitary translations. It does not transport the G8
cutoff trace itself. In particular, it does not prove that the expanding
cutoff family has a trace-class limit, nor that its limit is the same-owner
Weil value.

The remaining R3 target is therefore narrower:

```text
G8 cutoff trace ledger
  -> scale-transported source three-branch trace
  -> summable prolate-remainder / leakage estimate
  -> same-owner Weil readback.
```

The decisive open object remains the source second-support prolate remainder
from R3-F3, together with the finite-cutoff-to-source-ledger compatibility.
No sign premise, detector health, `SourceRH`, or universal Weil positivity is
used in this record.
