# 2259 — Rigorous interval re-certification of the Hardy-Z brackets (Arb ball arithmetic)

Date: 2026-09-30

Consumer: the mpmath 60-dps numeric certificates of the 2251/2254
separation input. The bracket sign changes and the nonzero kill pin are
re-derived with certified enclosures (python-flint Arb balls), replacing
heuristic precision-by-practice with ball arithmetic.

Verdict: **all 72 brackets re-certified (21/24/27 per candidate); max
bracket width upper bound `1.6543612251060554e-26`; min pairwise gap lower
bound `1.383836594509236`; min certified endpoint margin
`8.656304746693204e-28`; the kill pin at `27.67032193035704` is certified
nonzero with `|Z| >= 2.8451013491344974`. The numbers reproduce the 2254
mpmath screening values and strictly dominate them in rigor (ball
enclosures, certified signs, no float bisection).**

## Method

```text
Z(t)  = exp(i theta(t)) zeta(1/2 + i t)
theta(t) = Im log Gamma(1/4 + i t/2) - (t/2) log pi
```

`zeta` and `lgamma` are evaluated with `acb.zeta` / `acb.lgamma` at
200-bit precision (Arb certified complex functions). A sign is accepted
only when the real part's ball excludes zero (with an 8-ulp padding on the
float conversion); the bisection runs on certified signs in arb arithmetic
(no float step), 80 steps from a `1e-6` start margin; a critical-line zero
exists in each final bracket by IVT (Z is real analytic, endpoint signs
opposite and certified). Endpoints are stored as 30-digit decimal strings
plus certified float bounds; widths and pairwise gaps are certified ball
bounds (`mid +/- rad`), not float conversions.

## Results per candidate

```text
gamma               39.25244858548658   42.12289614653125   45.66611208104108
brackets                            21                  24                  27
max width upper           1.6544e-26 (all three, the 80-step resolution)
min endpoint margin       8.6563e-28 (all three)
min pairwise gap lower    1.4401       1.4401       1.3838
```

Kill pin (the 2251 nonzero node at height `27.67032193035704`): certified
`|Z| >= 2.8451013491344974`, `is_zero = false`.

## Comparison against the 2254 mpmath screening

```text
quantity                 2254 (mpmath 60 dps)     2259 (Arb balls)
total brackets           72                       72
max width                5.293955920339377e-25    1.6543612251060554e-26
min endpoint margin      2.9109288740357516e-26   8.656304746693204e-28
min pairwise gap         1.3838365945092335       1.383836594509236
```

The gaps agree to 15 digits; the certified width/margin differ only by the
deeper bisection (80 steps vs the 2254 schedule) and the ball padding —
the two computations are independent machinery on the same sign
structure.

## Environment

python-flint 0.9.0 in a local venv (numpy
2.5.3, mpmath 1.4.1, scipy 1.18.1). The system python is PEP-668
externally managed; the venv is the supported install path. Runtime ~2 s.

## Nonclaims

This certifies the bracket sign changes (zero existence per bracket) and
the kill pin's nonvanishing, not the completeness of the zero list and not
the separation geometry (the 2254 two-ulp float guards stand for the
geometric lower bounds). The node classification uses the same mpmath
`1e-9` rule as 2254. No producer GO, no gate sign change, no RH claim.

## Provenance

- script: `scripts/routea_weighted_zero_brackets_arb_2259.py`;
- artifact: `results/2259_hardyz_arb_certification.json`
  (md5 `fc942030e4b47ca6ec46cdfdf65f71f4`);
- machinery: `scripts/routea_weighted_zero_separation_input_2247.py`;
- predecessor: `scripts/routea_weighted_zero_separation_certified_2254.py`.