# 2104 - Continuous-owner correction and compact-support survivor

Date: 2026-09-28.

Status: `TRUNCATED-OWNER-NO-GO` for promoting records 2095-2099 to COVER;
`COMPLETE-KNOWN-PREFIX-SURVIVOR` for records 2101-2103. Neither is an
unconditional selected-owner certificate or an RH proof.

## What failed

Records 2095 and earlier sampled a ten-height list `GAMMAS_EXT` on the
registered ordinates. At a gamma between two registered heights, the same
list gives 18 nodes rather than 17. The original `family_for_ext` has only
nine kill widths and raises `width pool exhausted for group kill` there.
Extending that list to ten widths at scale 0.86 produced positive sampled Q
at all four delta values on the first interior ordinate:

```text
gamma 39.2524485855, scale 0.86, deltas .15/.25/.35/.445:
Q = +1.145820e12, +3.443916e11, +2.570318e11, +4.819553e11
support 9.976; prime-power count 2479
```

This is a named failure of that 18-node, scale-0.86 family, not of every
Route A family. Scale 0.84 (record 2098) and scale 0.80 (record 2099) both
had negative sampled Q at all 12 interior grid points; the weakest 2099
reading was only `-7.240865369096948e10`. These signs still do not price
the producer errors.

More fundamentally, `healthyCorrectionNodes rho 0 empty` includes EVERY
source nontrivial zero in the closed ball of radius
`2^(0+1) + 2 + |2-rho|`. The ten-height numerical list is only a known-zero
UNDER-APPROXIMATION. Record 2100 compares it with the first 30 numerical
critical-line zeros at delta 0.15:

```text
gamma       radius     surrogate nodes   omitted known zeros   minimum nodes
37.586178   41.610415         17                  11                  28
39.252449   43.275657         18                  12                  30
40.918719   44.940983         17                  14                  31
48.005151   52.024129         17                  20                  37
```

The omitted count deliberately EXCLUDES a same-height on-line zero from the
registered-height rows; the numerical calculation does not adjudicate whether
such a zero can coexist with a hypothetical off-line zero. It also cannot
rule out additional off-line zeros or other zeros absent from the first-30
list. Consequently no interpolation over the 2095 registration grid can
certify the actual source-defined owner. This is the scoped no-go.

## What survived

A new numerical family keeps distinct widths for the five same-height orbit
rows and three real-axis rows, but uses the SAME width 2.2 for different
kill ordinates. Distinct modulation frequencies need not consume a larger
support radius. At scale 0.80, support is 5.12 and the support-derived
visible-prime count is 52 on the tested known prefixes. The interpolation
matrix is square; direct `A c = y` solves, not an H1 pseudo-inverse, enforce
the pins. Record 2101's 30-node control at m=400:

```text
H1 pseudo-inverse correction residual: 1.359049258061228e-4
square direct-solve correction residual: 7.745818620035488e-11
square direct-solve sampled Q:          -2.2109713101324633e13
```

The H1 route failed its registered `1e-5` pin gate due to its numerical
regularization; that failure is NOT a mathematical no-go. Record 2102
repeats the 30-node owner at m=6400 and four delta values; all four sampled
Q values remain negative, with weakest `-1.675397327895099e12` and pin
residual at most `2.55e-11`. Record 2103 tests three interior gamma heights
and four delta values each, using 30, 33, and 36 nodes, respectively:

```text
12 / 12 sampled signs negative
minimum absolute sampled margin: 1.675397327895099e12
maximum correction pin residual: 9.742463965089872e-11
support: 5.12; visible-prime count: 52
```

## Scope and next gate

This is an architecture candidate, not a definite Go. `mpmath.zetazero`
positions are numerical and only the first 30 were supplied; no theorem
identifies those positions with the complete actual closed-ball zero set.
The interpolation coefficients, signed finite-window functional, quadrature,
full-line tail, and model-to-physical transfer lack outward certificates
for this changed owner. The old L2 charge of `4.4122e10` belongs to the
17-node G8-H owner and must NOT be pasted onto this 30-36-node family.

The next useful test is parameterized by a finite closed-ball zero set,
not by a fixed numerical height list: establish an interpolation condition
and signed margin whose constants depend on the actual owner cardinality and
separation, or find a named family counterexample. Reprice every error term
for the compact-support, shared-kill-width family before Lean producer work.

Evidence: `results/2096_cover_cell_interior_m6400.json`,
`results/2097_continuous_owner_scale_probe_m6400.json`,
`results/2098_cover_continuous_owner_scale084_m6400.json`,
`results/2099_cover_continuous_owner_scale080_m6400.json`,
`results/2100_truncated_zero_owner_audit.json`,
`results/2101_known_prefix_shared_width_kill_test.json`,
`results/2102_full_known_prefix_direct_owner_m6400.json`, and
`results/2103_full_known_prefix_direct_owner_grid_m6400.json`.

## 2105-2109 owner-matched numerical budget

For the weakest tested 30-node known-prefix owner at gamma `39.252449`,
delta `0.445`, scale `0.80`, the owner-matched finite-window EM forward
remainder is `5.720420308066749e7`, the a_mat true-transfer movement is
`5.9268334716796875e4`, the true-Gram H1 diagnostic movement is
`1.733805888696289e7`, and the R=48 tail price is `2.2087121764650203e-138`.
The combined ledger is `7.460153030234718e7`, or
`4.452766460841471e-5` of the sampled negative margin
`1.675397327895099e12`.

This is the first owner-matched budget showing that the changed compact family
is not numerically killed by finite-window, tail, or matrix-transfer terms.
The owner is still only the first 30 numerical critical-line zeros in the
closed ball, not the complete abstract `sourceNontrivialZeroSet` owner. No
formal outward promotion or producer theorem is licensed.

Evidence: `results/2105_known_prefix_em_forward_bound.json`,
`results/2106_known_prefix_tail_price.json`,
`results/2107_known_prefix_amatrix_transfer.json`,
`results/2108_known_prefix_gram_transfer.json`, and
`results/2109_known_prefix_margin_ledger.json`.

## 2110-2112 off-line-owner stress

The complete abstract owner may contain additional off-line zeros, so a stress
was applied by adding one symmetric four-point off-line orbit inside the same
closed ball. Reusing one width for every added kill node is not viable:
record 2110 gives matrix condition numbers `1e34..1e36`, a singular case, and
pin residuals as large as `3.36e7`.

A named selector change assigns distinct widths to the added off-line orbit.
At m=400, all three stress points are nonsingular with condition numbers
`8.8e5..1.6e6` and negative Q. At m=6400, the `(re,im)=(0.60,20.0)` stress
point remains negative:

```text
nodes                         34
support                       6.08
visible-prime book            103
condition                     8.834357170631646e5
correction pin residual       5.124852127014793e-11
Q(|xi|<=40)                   -6.175280807191016e13
```

This rescues the selector mechanism under one stress orbit, but is not a
complete-owner theorem. The next test is cardinality/width scaling for more
than one added off-line orbit, followed by owner-matched EM and tail pricing.

Evidence: `results/2110_extra_offline_owner_sensitivity.json`,
`results/2111_extra_offline_unique_widths_2111.py`'s artifact is
`results/2111` only if regenerated with a committed output path,
and `results/2112_extra_offline_unique_widths_m6400.json`.

## 2113-2116 compact width-ladder cardinality screen

The first unique-width ladder grew support and the visible-prime book too
quickly. A compact ladder for added off-line nodes,
`width_i = 2.21 + 0.05*i`, keeps the support nearly fixed. At m=400, 0--4
added symmetric off-line orbits (30--46 nodes) remain nonsingular and have
negative Q. The m=6400 rerun confirms all five cardinalities:

```text
extra orbits   nodes   support   book   condition       Q
0              30      4.640     37     7.09e5          -6.143e13
1              34      4.640     37     7.16e5          -6.134e13
2              38      4.640     37     4.35e6          -8.190e13
3              42      4.640     37     1.44e7          -2.139e14
4              46      4.736     40     7.57e7          -7.329e14
```

This is the strongest selector direction so far. It still does not prove the
complete abstract owner, and the m=6400 rows are finite-window screens. The
next gate is an owner-cardinality bound plus a parameterized conditioning and
error ledger for the same compact ladder; only then can the candidate be
promoted toward the Lean node-certificate socket.

Evidence: `results/2113_owner_cardinality_scaling_screen.json`,
`results/2114_owner_cardinality_two_orbit_m6400.json`,
`results/2115_owner_cardinality_compact_widths_m400.json`, and
`results/2116_owner_cardinality_compact_widths_m6400.json`.
