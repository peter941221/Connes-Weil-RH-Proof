# Record 1339 — 1338 verdict: the zero-carrying carrier thins on the Gamma_R flavor but never hides; M2 unfunded, Option H permanent

Date: 2026-09-11.
Status: VERDICT RECORD for the executed probe `docs/proofs/1338_wzero_vanishing_index_and_capacity_probe.py` (official N = 8192, all pre-run amendments inv1-inv7 committed at `03fa922` BEFORE this run; completion by the `DONE 1338` sentinel, 126.5 s, data `docs/proofs/1338_probe_results.json`; the stdout run log (1543_1338_official.log) lives on
the Linux-side execution mirror under the build-logs convention).
Every number below was produced under green gates; the verdict bands and the license rule were committed in record 1338 section 4 before any official digit (law 42). MODEL-twin numerics only: no statement about the formal carrier, no vanishing, no `qw` sign, no `SourceRH`, no RH claim. RH is not claimed.

## 1. The run

```text
+------+-----+-----+------+--------+--------+-------+-------+---------+---------+---------+
| flav |  L  |   r | wind |    2M  | rankE  |   f   |  f0   | cliff   | Aunc    | A       |
+------+-----+-----+------+--------+--------+-------+-------+---------+---------+---------+
| LC   | 32  | 387 | -389 |    140 |    140 | 0.638 | 0.638 | 3.8e+02 | [2.000, | [2.179, |
|      |     |     |      |        |        |       |       |         |  2.013] |  2.234] |
| LC   | 48  | 658 | -661 |    254 |    254 | 0.614 | 0.614 | 1.4e+02 | [1.997, | [2.192, |
|      |     |     |      |        |        |       |       |         |  2.011] |  2.236] |
| LC   | 64  | 952 | -955 |    380 |    380 | 0.601 | 0.601 | 7.0e+01 | [1.997, | [2.191, |
|      |     |     |      |        |        |       |       |         |  2.009] |  2.229] |
| LR   | 32  | 156 | -158 |    140 |    140 | 0.103 | 0.103 | 2.0e+03 | [1.997, | [1.891, |
|      |     |     |      |        |        |       |       |         |  2.007] |  2.065] |
| LR   | 48  | 273 | -275 |    254 |    254 | 0.070 | 0.070 | 7.5e+02 | [1.997, | [1.976, |
|      |     |     |      |        |        |       |       |         |  2.007] |  2.083] |
| LR   | 64  | 402 | -404 |    380 |    380 | 0.055 | 0.055 | 3.6e+02 | [1.997, | [1.969, |
|      |     |     |      |        |        |       |       |         |  2.009] |  2.096] |
+------+-----+-----+------+--------+--------+-------+-------+---------+---------+---------+
```

Gates: G5 zero-data green (199 gammas, max residual 2.3e-13), G0 = 2.2e-13,
G1/G2/G4/G6/G7 all green (`G1_G2_G4_G6_G7_all: true` in the JSON). LC ranks
hit the 1334 continuity targets {387, 658, 952} EXACTLY (G6). The LR
windings match the record-1337 section 6 closed form `2 L (ln L - 1)`:
measured 157.6 / 275.4 / 404.1 vs predicted 157.8 / 276.1 / 405.5 (< 0.4%).
G4 cross-checks 1.6e-12..2.0e-12, constrained-sector traces ~1e-16 — the
machinery (null spaces, both evaluation paths) is exact.

## 2. Verdict under the pre-committed bands

```text
VERDICT {"S1_LC": "NO-THIN",   "S2_LC": "FALSIFIES", "S0unc_LC": "FALSIFIES",
         "S1_LR": "THINS",     "S2_LR": "FALSIFIES", "S0unc_LR": "FALSIFIES",
         "LICENSE_M2": false}
```

Three independent readings, all decisive (no cell INCONCLUSIVE):

1. **S0unc FALSIFIES — the 1335 capacity verdict stands after the sector
   defect.** The corrected unconstrained near-kernel sector has
   `A_tau in [1.997, 2.013]` for all five prime lags at every cell: exactly
   the generic average-value regime. Record 1334's headline number was
   computed on the wrong singular block (record 1338 section 0), but the
   re-measurement on the RIGHT block gives the same answer. The
   corrigendum is substantively VOID: 1335's "capacity falsifies" survives
   instrument-level scrutiny, and the a-fortiori joint-corridor force of
   record 1337 section 2 is restored (the qualification is deleted below).

2. **rankE = 2M at every cell — dimension was never the obstruction.** All
   point-vanishing functionals at the ±xi_n lattice are linearly
   independent on the sector at both flavors, to a tolerance-pair sharp
   cliff (G3 never fired at N = 8192). The `W_zero` constraint system is
   maximally efficient: it removes exactly `2 N(2 pi (L-3))` dimensions and
   not one more. So record 1336's idea fails NOT because the constraints
   are dependent, and (LC) not because the sector is too big relative to
   the constraint count — it fails because the SURVIVORS do not hide.

3. **The flavor question resolved as a wash.** LC (the committed twin)
   gives `f = f0` EXACTLY at all three L (independence saturated, fraction
   floor 0.60-0.64 -> band NO-THIN): record 1337 section 6's factor-2
   prediction, confirmed, as a paper prediction rather than a discovery.
   LR (single-Gamma_R) DOES thin — `f = 0.055` at L = 64, the survivors
   fall to the independence floor as the arithmetic allows — but the
   survivor capacity is STILL generic, `A = [1.969, 2.096]`. This is the
   1337 section 4 decision table's row "THINS / FALSIFIES: thin but still
   no hiding", read off verbatim.

## 3. Why the off-line loophole cannot save it (paper argument, honest scope)

Record 1337 section 3 (caveat R2) registered that the probe can only use
certified on-line zero data. Check whether that limits the reach of this
falsification:

```text
A_tau(SURVIVORS) = (1/r') sum_k s_p(xi_k) K'(xi_k) h,  r' ~ L log L -> infinity.
An off-line witness (the route's own hypothesis) adds O(1) extra surviving
directions (1337 section 3) and removes O(1) constraints: it perturbs the
MEAN by O(1/r') -> 0, and it cannot remove the r' - O(1) bulk directions
whose measured energy is generic.
Convergence of the per-mode series sum_j E_j requires the TAIL to vanish;
a finite-rank perturbation cannot turn a bulk of energy ~2 directions into
a summable tail.
```

So the capacity failure is a BULK property: the same relativization
robustness that saved C4 from the self-contradiction trap (1337 section 3)
now transfers the FALSIFICATION across the line/off-line boundary. What
this does NOT cover: any carrier model whose sector is NOT the Gamma-only
 Toeplitz near-kernel (e.g. a different global completion, or a carrier
defined with the zeta-side growth conditions built in from the start, which
is not the committed model and not what M3 would have re-parameterized).
Within the committed model class, the C4 route is closed at truncation
level on both flavors.

## 4. Decision (under the record-1338 license, no discretion used)

```text
+--------------------------------+--------------------------------------------+
| consequence                    | status                                     |
+--------------------------------+--------------------------------------------+
| M2 (G2 strip-RKHS package ->   | UNFUNDED. The falsifier was the capacity   |
|   W_zero formal definition)    | of the survivors, not the definition; G2   |
|                                | stays consumer-less (1331 verdict stands).|
| M3 (51-brick radial            | NOT FORCED. hcolumn-on-W_zero is now model |
|   re-parameterization)         | -false in the same sense hcolumn-on-W is  |
|                                | (1335): unsatisfiable on the Gamma model.  |
| Option H (hold the radial leg, | PERMANENT for the radial leg per the       |
|   freeze C4 family)            | preregistered pivot clause.                |
| Next campaign surface          | L4 Fork B (analytic) + A4 + the 10-row NM  |
|                                | registry, per record 1337 section 4.       |
+--------------------------------+--------------------------------------------+
```

The radial leg of G8 is now closed at the model level THREE times, each
under an independent instrument reading: 1329 (probe negative at finite
density), 1335 (capacity falsifies on the unconstrained sector — now
confirmed on the corrected block), 1338 (capacity falsifies on the
zero-constrained survivors, both flavors). The only G8 premise still
formally open is `hcolumn` itself, and no funded route to it survives
this record.

## 5. What this record does NOT establish

No Lean theorem, no statement about `sourceSoninCarrier` or `ran P_S`, no
vanishing consumed or produced, no `qw` sign, no `SourceRH`, no RH claim.
The probe falsifies a MODEL-TWIN capacity expectation; the registered
interpretation limits of record 1338 section 4 apply unchanged. The bulk
robustness argument of section 3 is paper-level arithmetic on averages, not
a theorem about any formal object.

RH is not claimed.
