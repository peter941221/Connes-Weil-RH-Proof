# 1898 — Formal no-go for the unit-target geometric contraction

Date: 2026-09-23

## Result

For a genuine `CompactLogTest` `f`, if

```text
support f.test ⊆ (-1, 1)
laplaceAt f 0 = 1
```

then Lean proves

```text
1/2 <= SchwartzMap.seminorm Complex 0 0 f.test.
```

Consequently the geometric-contraction premise
`2 * seminorm(base) < 1` is impossible for the current base owner, whose
unit Mellin targets include the zero node.

## Formal evidence

Declarations:

- `seminorm_zero_zero_ge_half_of_laplaceAt_zero_eq_one_of_support_Ioo`
- `not_strict_base_contraction_of_unit_zero_target_of_support_Ioo`

Source and audit: `ConnesWeilRH/Dev/C1P2BaseSeminormBound.lean` and
`C1P2BaseSeminormBoundAudit.lean`.

Build: `build-logs/20260923_base-nogo7.log`; successful, 3664 jobs, zero
`error:` lines, standard axioms only, no `sorryAx`.

## Route consequence

This closes only the current geometric-contraction producer shape.  It does
not refute the detector-specific B5 target or RH.  The active producer returns
to the same-owner signed physical-kernel budget and C3' phase-locked route.
