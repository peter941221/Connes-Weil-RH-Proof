# 1398 v2 — Preregistration revision: the GV scale clause only (v1's tie window is divergent; zero digits in v1, no run was made)

Date: 2026-09-13. Law 42: this is the sanctioned revision path —
[1398 v1](1398_rung3_joint_witness_prereg.md) was committed, then a
defect was found in it by source re-read during instrument construction,
BEFORE any run and therefore before any digit (the 1388 -> 1390
pre-run-revision precedent). v1 is hereby SUPERSEDED; no model content
moves. RH not claimed.

## What moved (exactly one clause)

v1 section 3, gate GV, defined the tie scale

```text
S := |(log4pi+gamma) F(0)| + integral_0^{2Rg} |2 F(0)| / (e^y - e^{-y}) dy
```

The integral is DIVERGENT at the origin: the denominator is 2 sinh y ~ 2y
and the SCALE carries the numerator's constant term, not its vanishing
correction. So S = infinity, the tie window 1e-6 * S is infinite, and
every cell would be forced to TIE. Unsatisfiable-as-written gate: a v1
drafting error, not model content.

REVISED GV — the only change in this prereg. With `reF0 := re F(0)`,
`k(y) := 1 / (e^y - e^{-y})`, `y0 := 1e-3` (the instrument's own
origin-subinterval cutoff of v1 section 3), and `Rg := Ru + Rf`:

```text
I := integral_{y0}^{2 Rg} k(y) dy
   = 0.5 * ( ln tanh(Rg) - ln tanh(y0/2) )       [antiderivative:
     int dy / (2 sinh y) = 0.5 ln tanh(y/2), evaluated at the UPPER minus
     LOWER limit; I > 0 since tanh is increasing; computed in float64]
S := abs((log(4 pi) + gamma) * reF0) + abs(2 * reF0) * I

GV VERDICT BAND    POS if A > 1e-6 * S;  NEG if A < -1e-6 * S;  TIE
                   otherwise (TIE cells report, no verdict content)
```

Rationale, pre-committed: `(0, y0]` is excluded because the A integral
itself takes its origin-region content from a single panel there (v1
section 3), where the true integrand is bounded by cancellation; the
scale deliberately does NOT divide by that cancellation, so a cell whose
A sits inside `1e-6 * S` reports TIE and claims nothing — exactly the
pre-committed meaning of the band, now with a finite window. `I` is a
pure instrument constant per cell (depends only on `Rg`), not on any
measured sign; at `Rg = 0.04`: I = 0.5·ln(tanh(0.04)/tanh(5e-4)) =
0.5·ln(80.0) = 2.19; at `Rg = 0.3464`: I = 0.5·ln(tanh(0.3464)/tanh(5e-4))
= 0.5·ln(665.6) = 3.23 — both positive, and `S >= |log4pi_g·reF0| > 0`
strictly since `reF0 > 0` is enforced by GF; S is O(reF0) either way, so
the REVISED window is the same order as the
intended one and strictly tighter than v1's (infinite) one.

## Everything else

Model (v1 sections 1.1-1.5, including 1.4's degeneracy reductions and
the `J(0) = 1/2` master identity via the `S`-symmetry), cells (v1
section 2: positional decode, A-blind max-ratio ordering, tier-1 = 1394
witness geometry evaluated first and gate-checked alone, 40 tier-2
candidates), instrument and remaining gates (v1 section 3: the binding
reading `npw = 32/64` = quadrature nodes per period with 16-node GL
panels, which satisfies "at most 2 periods per panel" with slack, and
G0/GI/GS/GT/GF/GD/GR/GQ verbatim; validity-violation semantics
unchanged), outputs and sentinel (v1 section 4, artifacts
`docs/proofs/1398_rig_*`), precondition (v1 section 5, MET), kill scope
(v1 section 6 VERBATIM — the one-sided law is unchanged), environment
and protocol (v1 section 7, script `scripts/run_1398_rig.py`), boundary
(v1 section 8): ALL RE-LOCKED VERBATIM and unchanged.

The v1 file stays in the record as the superseded draft (the 1388
precedent: a committed prereg is never edited; this v2 is the executable
preregistration). Acceptance is log-based, log-not-exit-code.

Zero digits: no rung-3 value was computed in v1 or in this revision; the
divergence of v1's S-integral and the two illustrative magnitudes of `I`
above are inspections of the formulas themselves, not measurements at
any owner. RH not claimed.
