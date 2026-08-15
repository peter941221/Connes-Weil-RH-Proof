# C1 Xi Conditional Contour Spine

Status: three conditional Gate 2 contour modules are Lean-checked. This is not
an explicit-formula proof and does not claim RH.

## Closed bricks

```text
H-A1 weighted zero sum
        |
        v
finite factor: pole sum + one analytic cofactor
        |
        +--> horizontal envelope + explicit M_n/T_n^4 decay contract
        |          |
        |          v
        |      horizontal boundary -> 0
        |
        +--> finite-height rectangle assembly
                   |
                   v
        right-line limit = -(2*pi*i) * complete zero sum
```

The following are proved without new project axioms:

- `C1XiHABridge.lean` keeps H-A1, the finite pole sum, and one cofactor under
  the same factorization owner. `GlobalWeightedLogDerivComparison` is an input
  contract; it is not a producer for the missing global comparison.
- `C1XiHorizontalLimit.lean` proves
  `horizontalBoundary_tendsto_zero_of_growth_contract` from the explicit
  `M_n / |T_n/(2*pi)|^4 -> 0` bound.
- `C1XiFiniteHeightLimit.lean` proves
  `rightLineLimit_eq_neg_spectralWeilValue` from the per-height rectangle
  equation and three supplied limits.

## Verification

The import-facing probes
`C1XiHABridgeProbe.lean`, `C1XiHorizontalLimitProbe.lean`, and
`C1XiFiniteHeightLimitProbe.lean` were built in WSL2 ext4 with:

```text
lake build ConnesWeilRH.Dev.C1XiHABridgeProbe \
  ConnesWeilRH.Dev.C1XiHorizontalLimitProbe \
  ConnesWeilRH.Dev.C1XiFiniteHeightLimitProbe
```

The build completed 3545 jobs. `#print axioms` for all audited declarations
reported only `[propext, Classical.choice, Quot.sound]`; there is no `sorryAx`.

## Remaining route to RH

```text
OPEN A: global H-A1/log-derivative comparison
        |
        +--> OPEN B: cofactor growth along one selected height sequence
        |             |
        |             +--> horizontal contour limit (conditional theorem exists)
        |
        +--> OPEN C: arithmetic right-line readback
                      |
                      v
              same-owner explicit formula (Gate 2)
                      |
                      v
              positive-trace / Weil criterion on the same owner
                      |
                      v
              finite-vanishing criterion
                      |
                      v
              Yoshida detector existence and transport
                      |
                      v
              SourceRH / RH root
```

The zero-spectral absolute summability, exact xi-zero indexing, finite
factor/residue/rectangle readback, and vertical fold are already closed. Gate
3U remains a separate diagnostic branch and is not a substitute for the
same-owner Gate 2 route.
