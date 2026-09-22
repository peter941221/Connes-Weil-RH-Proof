# 1825 — C3' constructed odd negative component

Date: 2026-09-22

## Formal result

`exists_odd_negative_diagonal_of_offLineZero` proves that for every
right-oriented hypothetical off-line zero there exists a compact-log test
`g` such that:

- `g` is odd;
- its Laplace values at `1/2` and `1` vanish;
- its Laplace value at the zero is nonzero;
- its complete same-owner gate is strictly negative.

The construction is the odd part of an exact seven-node residual correction.
The correction is placed in a narrow window whose Archimedean budget is
strictly negative; the convolution square is therefore prime-free and the
negative gate follows exactly. The public correction theorem records the
values at rho, -rho, 0, plus/minus 1/2, and plus/minus 1.

## Boundary

This closes the negative parity component's node and detection preservation.
It does not prove the even companion's required gate sign and does not
identify the constructed pair with the selected `HealthyYoshidaDetectorData`
orbit owner. The detector-specific C3' signed budget and Round 2 remain open.

## Verification

Evidence: `/home/peter/rh/build-logs/1826_odd_component_audits.log`.
The focused audit build completed successfully in 3812 jobs, with no `error:`
or `sorryAx`; all audited declarations use only `propext`, `Classical.choice`,
and `Quot.sound`.
