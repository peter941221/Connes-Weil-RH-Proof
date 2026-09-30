# 2303 — CORRECTED-STRIP-COVERED: certified centered-strip envelope for the width-a^2 owner

Record 2303 rebuilds the 2267 centered-strip envelope on the **corrected
physical owner** identified by 2276: the ideal integral behind 1980/2249 is
the change of variable `y = a x` of the legacy construction, so the physical
profile is `phi_(a^2)(y) exp(i theta y)` with `phi_R(y) = exp(-30/(1-(y/R)^2))`
on `|y| < R = a^2`, while the stored coefficient vectors are unchanged. The
legacy 2267 envelope was built on `u = x/a` profiles and is not a supplier
for this owner (2276 scoped no-go). 2303 re-runs the full directed reduction
with the single substitution `a -> a^2` at the family-radius interface.

Status: **CORRECTED-STRIP-COVERED** (artifact grade, not Lean).

## Result

    certified continuum sup over sigma in [-1/2, 1/2]
        N(sigma) = min(D2_base M_corr, D2_corr M_base) / (2 pi)^2

    sup_certified = 2823660.8460007603
    frozen bUpper2243 = 9506275.102584327
    margin = 3.36664904924696x

The binding point is `sigma = -0.5`, binding channel **a** (`D2_base *
M_corr`). The channel switch is the structural change against the legacy
envelope: on the legacy owner the binding channel was the `corr_D2` product,
whose coefficient inflation is enormous (`363.85` here, `89.09` on the
legacy radii). On the corrected owner the corrected `corr_D2` norm is
`95118296.55` and only enters channel b (`C_b = 6532283.81`), so the
certified minimum is carried by the two moderate-inflation norms.

| quantity (sigma = -0.5)     | value                 |
|-----------------------------|-----------------------|
| raw point product           | 337039.47691484215    |
| panel base_M0 / base_D2     | 0.023095012125432673 / 109.68226237365003 |
| panel corr_M0 / corr_D2     | 35.119080091604026 / 135256.46852099142 |
| inflation base_M0 / base_D2 | 5.112647634069513e-4 / 0.17784967033779361 |
| inflation corr_M0 / corr_D2 | 1.0459684167472054 / 363.85284380367915 |
| certified norms M_b, D2_b   | 2.7111947718049683 / 10266.016007707964 |
| certified norms M_c, D2_c   | 257.6016684071858 / 95118296.55422348 |
| C_a / C_b                   | 66987.05297622057 / 6532283.814038719 |
| C_upper (B_point)           | 2644542.851480454     |
| x e^(2 rmax 0.005)         | 2823660.8460007603    |

## The reduction, layer by layer

1. **Directed grid.** 256-bit MPFR, `NX = 240001` nodes on
   `[-6.553600000000003, 6.553600000000003]`, `dx = 5.4613333333333355e-05`;
   per node the four channel values (M0, D2 for base and corr) are
   accumulated by the 2234 `node_bounds` routine, which is radius-generic:
   passing the corrected family list `(a^2, theta)` yields exactly the
   corrected `u = y/R`, `e1 = -2K u/(R q^2)`,
   `e2 = -(2K/R^2)(q^-2 + 4u^2 q^-3)`. Each node carries a
   `2^-200 x magnitude-sum` slack plus three `nextafter` ulps.

2. **sigma sums.** 101 MPFR point sums `int U(x) e^{sigma x} dx` by the
   composite trapezoid with directed additions and an upward-rounded
   `dx/2` factor.

3. **Zero-count gate.** The composite-EM panel
   `(dx^2/12)(2 rmax) M_k(sigma)` is admissible only at `N_risk = 0`, i.e.
   only with a certified Z = 0 for each channel. The 2242 pavement was rerun
   on the corrected families (256-bit natural interval extension, 32-ulp
   hull, bisection to depth 48):

   | channel | verdict                | boxes | depth | min floor  |
   |---------|------------------------|-------|-------|------------|
   | base_M0 | ZERO-FREE-CERTIFIED    | 11068 | 4     | 9.441818e-31 |
   | base_D2 | ZERO-FREE-CERTIFIED    | 12332 | 1     | 6.065727e-27 |
   | corr_M0 | ZERO-FREE-CERTIFIED    | 130222| 10    | 1.787576e-26 |
   | corr_D2 | ZERO-FREE-CERTIFIED    | 183972| 8     | 1.152957e-22 |

   The edge arcs carry exactly one family (radius `a_30^2 = 6.5536`); on
   `|y| in (a_29^2, a_30^2)` the exact factorization
   `e1^2 + e2 = (2K/R^2) G2(q) q^-4`, `G2(q) = 2K - (2K+4)q + 3q^2`,
   `d/dq[G2 q^-4] = q^-5(-240 + 192q - 6q^2)` gives
   `Re B2 >= (2K/R^2) G2(q_c) q_c^-4 - theta^2 = 3374.2458105506257 > 0`
   at `q_c = 0.32548427581787187`: **EDGE-ZERO-FREE-CERTIFIED**.

4. **Coefficient inflation.** The 2237 certified radii
   `r_base = 1005486.289224448`, `r_corr = 2057069012.526474` charged
   through the corrected ladder `r sum_f 2 a_f e^{|sigma| rmax}
   sup|phi_f^(k)|`, with the support-supremum weight `e^{|sigma| rmax}`
   (the 2267 symmetric convention; the legacy `e^{min(sigma,1) rmax}`
   form under-majorizes for negative sigma).

5. **Continuum transfer.** `|d/dsigma log N| <= 2 rmax` (each strip norm
   is an `e^{sigma x}`-weighted L1 integral with support `|x| <= rmax`),
   applied at the half-step 0.005: factor `1.0677311749439153`, giving the
   certified continuum sup from the grid maximum.

## Anchors and controls

+ the owner capture in `results/2275_gap_owner_audit.json` is bitwise equal
  to the 2267 replay operands (families, base and corr vectors); MD5
  `d461872e14212dcba8efe1874de6f652` / `c37e16a9dfeb4383c7bab1d23aa59566`;
+ the numpy screen reproduces the 2277 raw reading **bitwise**:
  `B_max = 337039.47691484215` at `sigma = -0.5`;
+ all 101 certified point sums are uppers of the raw binary64 rows
  (`raw_upper_ok = true`; the largest certified/raw product ratio is
  8.2765792264718 at `sigma = +0.5` and 7.846389021511061 at
  `sigma = -0.5`, entirely the coefficient inflation);
+ the 2238 ladder majorants `sup|psi^(k)| <= P_k(30)/R^k` were rechecked
  numerically at the corrected radii through the exact log-derivative
  Bell evaluation: per-order ratios (measured sup)/(majorant) are
  1.000, 0.0803, 0.0154, 0.0026, 0.0004 for k = 0..4, so the corrected
  radii do not violate the ladder.

## What this does and does not change

+ It replaces the 2267 envelope as the registered strip supplier for the
  corrected owner. The frozen constant `bUpper2243` is unchanged; the
  corrected envelope sits at 0.297 of it.
+ The Lean consumer `a005_item5_producer_wired` still takes `hstrip` as a
  hypothesis. 2303 supplies artifact-grade evidence for that hypothesis on
  the captured owner; it does not formalize the strip certificate, and it
  does not identify the captured owner with the selected Lean test
  functions. The residual inputs remain hstrip, hmargin, hcharge-rest and
  hgap until the certificate interface and the owner bridge exist.
+ The coefficient radii remain the 2237 certified ones for the *stored*
  coefficient vector, which the corrected owner shares (2276).

## Non-claims

+ artifact-grade reduction replay in the 2234/2242/2243 standard, not a
  Lean certificate;
+ the sigma-transfer is the log-derivative law at half-step 0.005: the
  certified sup is a grid maximum times `e^{2 rmax h}`, valid on the
  continuum but not tight;
+ no hgap supplier, no infinite-tail certificate, no selected-owner
  readback, no signed producer margin, no producer GO, no RH claim.

## Reproduction

From the repository root in the Linux verification environment:

    MODE=recon  python3 scripts/routea_corrected_strip_envelope_2303.py
    seq 0 11 | xargs -P 12 -I{} env CHUNK={} MODE=chunk \
        python3 scripts/routea_corrected_strip_envelope_2303.py
    seq -50 50 | xargs -P 14 -I{} env SIGMA_INDEX={} MODE=sigma \
        python3 scripts/routea_corrected_strip_envelope_2303.py
    printf '%s\n' base_M0 base_D2 corr_M0 corr_D2 | xargs -P 4 -I{} \
        env MODE=pave_{} python3 scripts/routea_corrected_strip_envelope_2303.py
    MODE=edge   python3 scripts/routea_corrected_strip_envelope_2303.py
    MODE=reduce python3 scripts/routea_corrected_strip_envelope_2303.py

Artifact: `results/2303_corrected_strip_envelope.json` (with
`results/2303_recon.json`, `results/2303_sigma_*.json`,
`results/2303_pave_*.json`, `results/2303_edge.json`).