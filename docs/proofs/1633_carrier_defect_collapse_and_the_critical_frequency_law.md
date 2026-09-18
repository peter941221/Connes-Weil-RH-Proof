# 1633 — the carrier defect collapses in λ: the critical-frequency law ξ_c = λ⁻², the same-family floor discipline, and the B1 direction

Date: 2026-09-18. Round: item 3 of map 043 (the numerical scaling law),
executed first so that its result decides the direction of items 1 and 2.
No Lean brick; three scripts land (`scripts/carrier_defect_1633.py`,
`scripts/symbol_localization_1633.py`, `scripts/carrier_scaling_1633.py`,
`scripts/carrier_floor_1633.py`, `scripts/carrier_tail_1633.py`).

Read with: 1632 (the class audit and the ε-gap), 1631 (the phase budget
γ = −2πξlog|ξ| + 2πξ + π/4 + O(1/ξ)), 1630 (the finite-section probe this
round reproduces to the digit), 1629 (the base in Toeplitz form), 1627 (no
witness of finite exponential type), map 043 (the B1/B2 decision tree).

## 1. Verdict block

```text
(A) RIG VALID  all three stages reproduce the 1630 probe D[H_0] column
                exactly (4.318915e-01, 6.900534e-02, 2.687186e-02,
                3.030392e-06 at lambda = 1, 1/2, 1/e, 0.1) and the model
                calibrations are exact: model m := 1 reads 1.000000e+00 at
                lambda = 1 and 0.000000e+00 (integer shift) at lambda = e^-1.

(B) FLOOR      The same-family floor is informative ONLY when the model's
    DISCIPLINE  exact witness is not in the family.  A bump of width W with
                |c| >= W lands fully on x > 0 in the model, so a width-W
                translate family has floor identically 0 for |c| >= W.  The
                1630 probe's "floor" column for lambda <= e^-1 was therefore
                degenerate; its real readings were upper bounds only.

(C) KEY        real < floor at EVERY lambda and EVERY width tested
    READING     (ratio 0.13-0.83).  The m-multiplication is not a smearing
                obstruction: it BEATS the free-shift model by factors up to
                8x, and the wider the trial function the larger the gain.
                This refutes the naive "m spreads the support" mechanism as
                the explanation of the residual defect.

(D) LAW        The frequency that lands on the boundary x = 0 is
                xi_c(lambda) = lambda^{-2}  (stationary phase of the total
                phase psi(xi) = 2 pi [xi log|xi| + (c-1) xi], c = 2 log lambda).
                Measured local slopes p_eff track the predicted sqrt(tail)
                slopes (1.14/3.70/3.19/5.26/7.13 vs 3.60/5.07/5.98/8.28/11.35
                at lambda = 1/2 ... 0.15); for a FIXED smooth H the defect
                -> 0 as lambda -> 0, which is exactly the 1630 fixed-bump
                collapse.  The reading stops tracking at lambda = 1/8, where
                xi_c crosses the rig window edge |xi| <= 64: below it the
                windowed tail is identically zero (a rig property, F43).

(E) DIRECTION  B1.  There is no resolution-stable positive defect floor
                below lambda ~ 1/2 that would support B2 (a uniform gap).
                Attainment stays OPEN and is exactly 1632's epsilon-gap:
                inf D = 0 does not exhibit an element of the carrier, and
                1627 (no finite-type witness) is consistent with a
                non-attained infimum.  Items 1 and 2 should go analytic on
                the tail mechanism, not numeric.

(F) CORRECTION Stage-1 script `carrier_scaling_1633.py` had a Gram-weight bug
                (summation over xi weighted DU instead of DXI), so all of its
                generalized eigenvalues were low by sqrt(DU/DXI) = 1/sqrt(2);
                the tell was the model calibrating at 0.707 instead of 1.0.
                Its conclusion ("sigma_min is flat in lambda") was an
                approximation artifact of indicator pixels and is SUPERSEDED
                by the width-resolved data below.
```

## 2. What was measured, and with what

| script | object | verdict |
|---|---|---|
| `carrier_defect_1633.py` | mass split of F⁻¹(U H) and of K = F⁻¹(m(−·)) | reproduces 1630; K is 98.4 % on x < 0 with 1/\|x\| tails both sides |
| `symbol_localization_1633.py` | localization controls + pole/zero ledger | controls exact (δ at ±μ, e^{−x}); \|m(−i)\| = 806.8971 matches 1632 |
| `carrier_scaling_1633.py` | σ_min over indicator pixels, two families | calibrations exact; readings approximation-limited (see (F)) |
| `carrier_floor_1633.py` | σ_min over bump translates, W ∈ {1,2,4,8,16} | real vs same-family floor, 8 λ values |
| `carrier_tail_1633.py` | measured σ_min vs predicted √tail at ξ_c = λ⁻² | slope match for λ ≥ 0.15 |

Transform dictionary (fixed, both rigs): F(h)(ξ) = ∫h(x)e^{−2πixξ}dx, so
H²(C₊) = {Fh : supp h ⊆ (−∞,0]} and H²(C₋) = {Fh : supp h ⊆ [0,∞)}; the
defect is D(H) = ‖P_{x<0}(U H)‖/‖U H‖ with U(ξ) = e^{2πicξ}m(−ξ),
c = 2 log λ; the committed carrier is {H ∈ H²(C₊) : D(H) = 0} ≠ {0}.

## 3. The same-family floor (stage 2)

`carrier_floor_1633.py`, families = C^∞ bumps of width W translated at
spacing W/2 over [−24, 0], 32 768-point grid, du = 1/128.

```text
+---------+--------+---------------+---------------+---------------+
| lambda  |  |c|   |  W = 8 floor  |  W = 8 real   |   ratio       |
+---------+--------+---------------+---------------+---------------+
| 1.0     |  0.000 |   9.9028e-01  |   3.6356e-01  |   3.67e-01    |
| 0.3679  |  2.000 |   9.5835e-01  |   2.6554e-01  |   2.77e-01    |
| 0.2     |  3.219 |   8.1830e-01  |   1.2679e-01  |   1.55e-01    |
| 0.1     |  4.605 |   5.4784e-01  |   7.0673e-02  |   1.29e-01    |
| 0.05    |  5.991 |   2.4523e-01  |   3.0693e-02  |   1.25e-01    |
| 0.02    |  7.824 |   7.6045e-07  |   9.7964e-04  |   1.29e+03    |
| 0.01    |  9.210 |   1.2837e-08  |   6.5566e-06  |   5.11e+02    |
+---------+--------+---------------+---------------+---------------+
```

The floor column is the model m := 1 under the same shift: for W = 8 and
|c| < 8 the wide bump cannot fully escape the half-line, so the floor is a
live number (0.99 at λ = 1 down to 2.5e-1 at λ = 0.05), and the real symbol
beats it at every λ — by a factor 7.7 at λ = 1 and 8.0 at λ = 0.05. The
last two rows are where the model's own floor finally collapses (the shift
outruns the width); they carry no information about m and are the reason the
sharp W = 1 family is the one used for the λ-sweep.

Sharp family (W = 1, 49 translates), real σ_min as an upper bound on the
true infimum:

```text
lambda:   1.0     0.5     e^-1    0.3     0.2     0.15    0.125   0.1     0.07    0.05    0.03
sigma:  1.31e-1 5.95e-2 1.91e-2 9.99e-3 1.18e-3 1.53e-4 3.06e-5 3.00e-6 4.63e-8 1.67e-8  0
```

Eleven orders of magnitude across λ ∈ [1, 0.05], with local slope drifting
2 → 11 and the last rows at the rig's roundoff floor (exact zeros printed).

## 4. The mechanism: ξ_c = λ⁻²

Write U(ξ) = e^{iψ(ξ)} on the real axis. With the committed 1631 phase
budget, γ(−ξ) = 2πξlog|ξ| − 2πξ + π/4 + O(1/ξ), so

```text
psi(xi) = 2 pi c xi + gamma(-xi) = 2 pi [ xi log|xi| + (c-1) xi ] + pi/4 + O(1/xi),
psi'(xi) = 2 pi ( log|xi| + c ),      c = 2 log lambda.
```

Stationary phase for u = F⁻¹(U·Ĥ) puts the mass carried by frequency ξ at

```text
x(xi) = -psi'(xi)/(2 pi) = -( log|xi| + 2 log lambda ),
```

so x(ξ_c) = 0 at **ξ_c = λ⁻²**: below ξ_c the m-chirp lands the mass on
x > 0 (the half-line we need), above ξ_c on x < 0. The wrong-half mass is
therefore sourced by the high-frequency tail of Ĥ above ξ_c, and the
predictions are:

1. for a FIXED smooth H the defect → 0 as λ ↓ 0 (ξ_c → ∞), which reproduces
   the 1630 fixed-bump collapse without any new hypothesis;
2. the local slope of σ_min in λ should track the slope of √tail:

```text
lambda      0.5    0.3679   0.3     0.2     0.15
measured    1.14   3.70     3.19    5.26    7.13
predicted   3.60   5.07     5.98    8.28   11.35
```

The measured slope sits consistently below the prediction and follows the
same acceleration; the ratio σ_min/√tail drifts from 0.58 (λ = 1) through
3.2, 4.9, 8.6, 29 to 99, so this is a slope law, not a constant-factor law,
and the amplitude carries an unknown O(1)-in-λ factor. Below λ = 1/8 the
window's tail is empty and the mechanism has nothing left to say inside the
rig; the readings there are floors (F43).

## 5. What this settles and what it does not

Settled: the residual carrier defect is not a uniform obstruction with a
resolution-stable positive floor; it is a boundary-layer quantity whose decay
is driven by ξ_c = λ⁻², and the m-multiplication is a focusing operator
relative to the free shift (measured on 5 widths × 8 λ values).

Not settled: whether inf D = 0 is ATTAINED. σ_min over any finite-dimensional
family can go to 0 while the closed subspace {H : D(H) = 0} is trivial: the
operator P₋U restricted to H²(C₊) need not be bounded below on a nonzero
subspace for the infimum to vanish. 1627 (no finite-type witness) forbids
the band-limited offenders, so attainment is precisely 1632's ε-gap and is
not a numerical question. No claim is made about the carrier, the gate, or
RH this round.

## 6. Direction handed to items 1 and 2

O1. Tail lemma (analytic): prove D(H, λ) ≤ C·√(mass of |Ĥ|² on |ξ| > λ⁻²)
    + o(...) with C independent of H and λ, using the committed phase budget
    in a van der Corput / stationary-phase estimate on U. The two rigs give
    the shape of the constant (drifting, so C is not 1).
O2. Uniformity: decide whether the convergence D(H, λ) → 0 is uniform over
    the unit sphere of H²(C₊) as λ ↓ 0. Uniformity would make the defect
    operator a small perturbation for small λ; non-uniformity is the
    ε-gap in its sharp form.
O3. Only if O2 gives uniformity: a perturbation/dimension argument on
    P₋U|_{H²(C₊)} to force a nonzero kernel — that would be a proof of the
    carrier base for small λ, the first positive result on the single point
    of failure.

## 7. Laws added

```text
F52  A same-family floor is informative only where the model's exact witness
     is absent from the family (W > |c|); a degenerate floor reports ratios
     that must not be read as evidence for B2.

F53  The boundary frequency of the carrier is xi_c = lambda^{-2}: the
     stationary phase of the committed 1631 phase lands frequency xi at
     x = -(log|xi| + 2 log lambda).  For a fixed smooth H the defect -> 0.

F54  Measured: real < same-family floor at every lambda and every width
     (ratios 0.13-0.83).  m(-xi) is a focusing operator relative to the free
     shift; the "m smears the support" picture is not the obstruction.

F55  A generalized-eigenvalue defect rig must weight the Parseval sum over xi
     by DXI, not DU (stage-1 bug: every value low by sqrt(DU/DXI)).  Contract:
     the model m := 1 at lambda = 1 must read exactly 1, and the 1630 D[H_0]
     column must reproduce to the digit.
```