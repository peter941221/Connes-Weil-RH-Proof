# 1981 — Wire audit: the diagonal sign is the only Cut-2 obligation; offline-owner pre-registration

Date: 2026-09-25.

Status: FORMAL audit brick landed + PRE-REGISTRATION of the offline-owner
run (committed before that run). No gate sign is proved numerically here and
no RH claim is made. The record-1980 route verdict is PARTIALLY REVISED: the
healthy-pivot failure it registered was an artifact of the wire, not of the
route.

## 1. Audit result: `0 < C` is a packaging artifact of the 1917 wire

The committed wire
`exists_pos_lambda_gate_and_prefix_of_annihilator_gate_neg`
(`C1FourPointSpanGateCertificate.lean:379`) takes
`HealthyYoshidaDetectorData rho g` and uses it for exactly one step: deriving
`hC : 0 < ICgate g.convolutionSquare` (`ibid:296-298`, via
`pinned_orbit_positive_pivot`). That `hC` feeds only
`exists_pos_lambda_quadratic_nonpos` (`ibid:194-200`), where it certifies the
closed-form witness `gatePlusRoot` — whose denominator is `2 * C`. The
spectral prefix transport
(`finiteSpectralPrefix_re_le_neg_xiMultiplicity_mul_sq_of_fullOrbit_transport`,
`C1FourPointSpectralPrefixTransport.lean:330`) carries NO sign hypothesis and
holds for every `lambda`. The record-1980 verdict (PARK, on `C > 0` failing
at `C ≈ -1`) therefore killed a packaging artifact.

New brick `ConnesWeilRH/Dev/C1FourPointSpanGateDiagOnly.lean` (+ Audit;
build log `1981_diagonly3.log`, `Build completed successfully (3811 jobs)`,
zero error/sorryAx; all three theorems on exactly
`[propext, Classical.choice, Quot.sound]`):

* `exists_pos_lambda_quadratic_nonpos_of_diag_neg {D B C} (hD : D < 0)`:
  for ANY signs of `B` and `C`, a strictly positive coefficient with a
  nonpositive span quadratic exists. Explicit witness
  `diagNegWitness D B C = min 1 (|D| / (2 * (|B| + |C| + 1)))`; the estimate
  is `D - lam*B + lam^2*C <= D + (|B|+|C|)*lam < D + |D|/2 = D/2 < 0`.
* `exists_pos_lambda_gate_and_prefix_of_annihilator_gate_neg'`: the committed
  consumer wire with `HealthyYoshidaDetectorData` REMOVED. Surviving
  hypotheses are exactly what the conclusions consume: the support bound
  (needed to state the span parabola identity), `htarget`/`hzero` (consumed
  by the spectral prefix transport), `hoff`, and the single strict sign
  `hdiag`. Conclusion unchanged: one `lam > 0` carries the nonpositive span
  gate AND the prefix margin `-xiMultiplicity(rho) * lam^2`.

Consequence for the obligation ledger of map 106 section 2: the binding
Cut-2 obligation on the owner is the single sign

```text
    D = ICgate(u.convolutionSquare) < 0,
```

with no condition on `C`, `b`, or the determinant. The record-1918
branch selection (vertex face) AND the record-1980 counter-selection
(healthy pivot) both targeted obligations that the wire does not need.

## 2. What the committed 1980 data says under the corrected obligation

Re-reading `results/1980_owner_completion.json` (the on-line `rho = gamma_1`
owner) under the corrected single-sign obligation:

```text
+------------+---+-------------+------------+---------------------------+
| knob       | n | D           | spread_D   | corrected reading         |
+------------+---+-------------+------------+---------------------------+
| sc=1.00    | 0 | +7.596e+04  | 8.1e-07    | FAIL (registered point)   |
| sc=0.90    | 0 | +2.407e+04  | 1.0e-05    | FAIL                      |
| sc=1.10    | 0 | -7.003e+04  | 1.8e-06    | PASS (11 certified digits)|
| sc=1.00    | 1 | -3.229e+02  | 6.6e-05    | PASS (4 certified digits) |
+------------+---+-------------+------------+---------------------------+
```

Two of the four knobs pass with wide certified margins, and the mechanism
section of record 1980 (committed `W(0) = 0` plus kill-set zeros confining
the density to the sigma-negative zone) is exactly the geometry that drives
`∫ K P^2 W` negative. BUT the committed contradiction theorem requires
`hoff : rho.re != 1/2` — an OFF-LINE zero — and the 1980 owner was the
on-line `gamma_1` proxy (chosen only because it is the one established
ordinate). The decisive measurement has therefore never been made.

## 3. Pre-registered offline-owner run (registered before execution)

Owner: `healthyCorrectionNodes rho 0 empty` with the hypothetical off-line
zero `rho = 1/2 + delta + i*gamma_1`, `delta in {0.05, 0.10}` (the two
abscissas of the 1918/1959 design probes), `N = 0`. The orbit no longer
collapses: 4 distinct orbit nodes (targets `+1, -1, 0, 0`), `rho + 1/2`
(target `-1`), the real triple (targets `0`), and the same four kill
ordinates — `M = 12` nodes. Representative family as in record 1980 (Gevrey
windows, per-node distinct widths; the height-`gamma_1` width pool is
extended to five distinct widths for the five same-height nodes).

Classification (fixed now; registered point = window scale 1.00,
convolution count n = 0, certified pair, window `xi_max = 40, dxi = 0.004`):

```text
GO_CANDIDATE : D < 0 at the registered point of an offline owner, with
               relative certified spread_D < 1/3.
PARK_CONFIRM : D >= 0 at both offline registered points — the record-1980
               freeze stands under the corrected obligation, and the lane
               returns to map-043 O-programs.
```

Informational (no classification force): the other knobs
(scale `{0.90, 1.10}`, `n = 1`), pins, `W(0)`, confinement, 1919 identity,
`T_need`, and the witness coefficient at
`lam = diagNegWitness D B C` with the Cut-1 window factor and required
tail budget reported at that coefficient.

Scope honesty: the `hoff` zero of the committed theorem is hypothetical
(this is the standing de-Branges-transfer question of Cut 3, untouched
here). A GO_CANDIDATE on this owner revives the lane's program: interval
certification of `D` on this owner, the seed-ladder rungs `4 <= j < M - 1`
feeding `C_base4, C_corr2`, and the joint margin — bounded mechanical work
by the record-1976 method, at the certified coefficient
`lam = diagNegWitness D B C`.

## 4. Discipline note

Record 1980 §4 added: re-audit a branch selection when the family changes.
This record adds its dual: **audit the consumer's hypotheses before reading
a route verdict off them** — a hypothesis that feeds only a witness
construction can be removed by supplying a better witness, and a
route-killing sign failure at such a hypothesis is not evidence about the
route.

## 5. Outcome (run executed after the pre-registration commit)

Instrument health on every row: pins `max |L_base - 1| <= 5.3e-15`,
`max |L_corr - y| <= 3.5e-12`, condition `2.5e+03 .. 1.3e+04`, `W(0) <=
1.6e-35`, mass beyond `|xi| > 4 <= 7.2e-06`, certified spread on `D` between
`1.7e-06` and `1.5e-03`, 1919 identity `<= 3.1e-06` relative on the
registered rows (`<= 2.7e-04` at `n = 1`), strip contraction exists with
`T_need = 31.83`. The kill set is the hypothetical-world prefix
(`{rho} ∪ {gamma_2..gamma_5}`: the displaced on-line ordinate is NOT a node;
verified `M = 12` on every row).

Registered points (scale 1.00, `n = 0`):

```text
+-------+-------------+-------------+--------------+-------------+----------+
| delta | C           | b           | D            | spread_D    | verdict  |
+-------+-------------+-------------+--------------+-------------+----------+
| 0.05  | +6.4296     | -6.7748e+04 | +1.0057e+06  | 2.4e-04     | FAIL     |
| 0.10  | +1.4223     | -1.4272e+04 | -1.0737e+06  | 5.1e-05     | PASS     |
+-------+-------------+-------------+--------------+-------------+----------+
```

Verdict per the pre-registered rule: **GO_CANDIDATE** — at
`rho = 1/2 + 0.10 + i*gamma_1` on the completed owner the single Cut-2
obligation `D < 0` holds with a certified margin of about four digits, and
the point additionally satisfies the legacy 1918 signs (`C = +1.42 > 0`,
`det < 0`), i.e. it is an instance of BOTH the corrected obligation and the
original map-106 section 2 endpoint geometry. Informational knobs: `D < 0`
also at both `scale = 0.90` rows (huge margins, `-3.7e+08` / `-7.8e+07`),
`D > 0` at scale 1.10 and `n = 1` — the sign is knot-stable in scale
(0.90 negative band, 1.10 positive band) rather than fragile-at-every-knot;
the corrected obligation needs exactly one admissible point.

Witness economics at the registered point (reported per registration, at
the conservative coefficient `lam = diagNegWitness = 1` and at the larger
positive root `lam+ = (b + sqrt(b^2 - 4CD))/(2C) ~ 70`):

```text
lam = 1   : window factor ~ 7.5e+09, required M_n ~ 7.5e-13
            (geometric decay (1/2)^n reaches this near n ~ 50;
             existence of such n is FORMAL, record 1933/1935)
lam+ ~ 70 : window factor ~ 4.3e+05, required M_n ~ 7.7e-09
            (n ~ 35-40)
```

## 6. Route consequence

The record-1980 freeze is LIFTED under the corrected obligation. The live
program on the revived lane, in order:

```text
1  interval certification of D < 0 (and C > 0) on the completed owner at
   the registered point (rho = 1/2 + 0.10 + i*gamma_1, N = 0) — the
   record-1976 Taylor+Lagrange method, one brick family;
2  seed-ladder rungs 4 <= j < M - 1 (= 10) feeding C_base4, C_corr2 —
   bounded mechanical work, one rung per brick;
3  the Cut-1 joint margin at the certified coefficient (the window-factor
   numbers above are the budget the decay constants must meet);
4  Cut 3 assembly through the audited, hypothesis-free wire
   (exists_pos_lambda_gate_and_prefix_of_annihilator_gate_neg').
```

Scope honesty unchanged: the passing owner is a representative family at a
hypothetical off-line zero; the de-Branges transfer from the off-line
hypothetical zero to RH remains the standing Cut-3 question, untouched by
this record.

## 7. Reproduce

```text
python3 scripts/fourpoint_offline_owner_1981.py            # registered run
python3 scripts/fourpoint_offline_owner_1981.py --quick    # coarse smoke
```

Output: `results/1981_offline_owner.json`. WSL, numpy/scipy only.
