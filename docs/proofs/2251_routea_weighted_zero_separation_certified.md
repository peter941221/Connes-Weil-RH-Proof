# 2251 — Certified per-node isolation and local uniform-in-rho separation

Date: 2026-09-30

Consumer: the 2247 measured separation input for the 2157 derivative
cost floor — "measured at the three stress candidates; a uniform-in-rho
separation theorem remains research-grade".

Verdict: **certified per node at the chosen candidate, plus a local
uniform-in-rho lemma with an explicit radius**. Global uniformity over
all `rho` remains open.

## Certified brackets

Every critical-line pin gets a Hardy-Z sign-change bracket refined by
bisection:

```text
brackets                  21 (the in-ball critical-line zeros)
target width              1e-24
max width                 5.293955920339377e-25
min pairwise gap          1.4401493697908734   (gamma_17/gamma_18 spacing)
coordinate conflicts      none
refined endpoint margin   2.9109288740357516e-26
evaluation error budget   mpmath 60 dps: absolute error of order 1e-58,
                          so every sign decision is safe by 30+ orders
```

The non-zero kill pin `27.67032193035704` is certified as a non-zero
directly (`|Z| = 2.845101349` at 60 dps), the off-line pins use their
exact stored coordinates (convention A), and the real-axis pins carry no
zeros below `gamma_1`.

## Per-target certified separations

```text
target rho          (0.945 + 39.25244858548658 i): min 1.7246687029005743
   nearest pin 0.5 + 37.58617815882567 i (critical-line zero, gamma_6)
   floor 2157 (measured) 0.0030755954591358543, certified lower 0.0030755954591358543
target 1 - conj rho (0.055 + 39.25244858548658 i): min 1.7246687029005743
   floor 0.009608984322583001
target rho + 1/2    (1.445 + 39.25244858548658 i): min 1.915589239572187
   floor 0.0007699022126940044
```

These reproduce the committed 2247 candidate-1 values bitwise
(`1.7246687029005743`), now with two-ulp outward lower bounds.

## Local uniform-in-rho lemma

```text
window gap to gamma_22     0.39130846470884956
ball gap to gamma_22       0.3935763212762261
eps_rho = 0.95 * min/2     0.18587152073670352
separation lower bound     s_min - 2 eps_rho = 1.3529256614271667
floor 2157 lower bound     0.0015137680096211589
target-target margin       0.5 - 2 eps_rho = 0.12825695852659297
```

For every `rho'` with `|rho' - rho| <= eps_rho` the construction node set
is unchanged: the moving elements are the targets and the off-line pins
(each Lipschitz-1 in `rho'`), all other pins are fixed constants, and the
ball / window membership thresholds move by at most `2 eps_rho` while
staying below the computed gaps to the first excluded ordinate
`gamma_22 = 82.91038085408603`. Hence every target-to-pin separation at
`rho'` is `>= s_min - 2 eps_rho`, and the 2157 floor (decreasing in the
separation) is at least the registered local floor.

## What this closes and what it does not

Closed: the per-node certified isolation at the candidate and a local
uniform-in-rho statement with explicit radius and margin; the 2247
"certified zero isolation" objection is answered pointwise.

Not closed: global uniformity over all `rho` (a covering argument is
needed); the brackets are numeric certificates (mpmath 60 dps with an
explicit error budget), not Lean-formalized interval arithmetic; no
producer GO, no RH claim.

## Provenance

- script: `scripts/routea_weighted_zero_separation_certified_2251.py`;
- artifact: `results/2251_separation_certified.json`;
- machinery: `scripts/routea_weighted_zero_separation_input_2247.py`
  (`assemble_owner`, `floor_2157`).