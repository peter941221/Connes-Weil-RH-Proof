# 2267 — Certified centered-strip envelope of the direct-product screen

Date: 2026-09-30

Owner correction (record 2276): the historical certified status below
describes the legacy width-a physical inputs. The 2249 transform instead
has physical width a^2. Even with identical stored coefficient vectors,
the two functions are provably different. Transfer of this envelope as
hstrip for the 2249/2275 owner is withdrawn; the numeric replay remains
unchanged. See [2276](2276_routea_owner_scale_price.md) for the Lean support
witness and corrected-owner analytic majorant prices.

Consumer: 2265 pinned the producer side of the weighted-zero C3' candidate
to `laplaceAt_convolution_spectral_bound_of_strip`, whose hypothesis `hB`
is a certified bound on the two-channel product
`N(σ) = min(D₂_b(σ)·M_c(σ), D₂_c(σ)·M_b(σ))` over the centered strip
`σ ∈ [-1/2, 1/2]` — exactly the range the spectral chain evaluates at
(`centeredXiCoordinate ρ = (ρ.re − 1/2) + i·ρ.im`). 2264 audited the raw
binary64 min-product over `σ ∈ [-0.6, 1.1]` and found the centered-strip
maximum `2874525.124523096` at `σ = -1/2`, only `0.302382` of the frozen
screen constant — but at screen grade: no panels, no coefficient
inflation, no σ-transfer. This record delivers the certified envelope
with the committed 2234/2243 machinery.

Verdict: **CERTIFIED-STRIP-COVERED. The certified sup on the centered
strip is `6663660.437141987` against the frozen constant
`bUpper2243 = 9506275.102584327`, margin `1.426584561481876×`. The
maximum certified grid point sits at the strip edge `σ = -1/2`
(`B_point = 6495235.763900986`, channel a binding); the log-derivative
transfer adds only `e^{2·a_max·0.005} = 1.0259304941903822`. The
`σ = 1.0` row recomputed through this reduction reproduces the 2243
binding row `C_upper` bitwise (`rel = 0.0`), and all 101 certified
point sums are uppers of the 2264 raw readings (`rel_max = 2.44e-15`).**

## Method

1. **Point values.** `results/2234_sigma_{j}.json` for `j = -50..50`
   (`σ = j/100`), the 256-bit MPFR sigma-worker sums over the committed
   per-node upper chunks with the 4-ulp end guards. The 50 negative-σ
   rows are fresh runs of the same worker (committed machinery, no code
   path change beyond the sign of the exponent); the positive rows are
   the frozen 2234 files.
2. **Panels.** The 2238 composite-EM identity with the 2242 certified
   zero count (`N_risk = 0`), in the σ-symmetric form
   `panel_cem_sym(σ) = (dx²/12)(2 a_max) e^{|σ|a_max}(m_{k+2} +
   2|σ|m_{k+1} + σ²m_k)`. The weight supremum on the support
   `[-a_max, a_max]` is `e^{σa_max}` for `σ ≥ 0` and `e^{-σa_max}` for
   `σ < 0`, so the |σ| form is the correct majorant and reduces to the
   2243 `panel_cem` at `σ ≥ 0` (checked bitwise at `σ = 1`).
3. **Coefficient inflation.** The 2237 certified radii with the same
   support-supremum weight `e^{|σ|a_max}`; identical to 2243 at `σ ≥ 0`.
4. **Reduction.** The bitwise 2243 loop (guarded `up_many` chain,
   `C = min(c1, c2)`, `B = (2π)²C`) with the cover factor removed: the
   grid coverage is applied once at the end by the σ-transfer instead of
   per row.
5. **σ-transfer.** Each strip norm is an `e^{σx}`-weighted L¹ integral
   with support `|x| ≤ a_max`, so `|d/dσ log M| ≤ a_max` and
   `|d/dσ log N| ≤ 2 a_max` (min of the two products). On the 0.01 grid
   (half-step `h = 0.005`),
   `sup_{[-1/2,1/2]} N ≤ max_j B_point(j) · e^{2 a_max h} = max ·
   1.0259304941903822`.

## Results

```text
quantity                       value                        note
sup certified (max x transfer) 6663660.437141987            <= frozen
frozen bUpper2243              9506275.102584327            2243 composite-EM
margin                         1.426584561481876            frozen / sup
max grid point                 sigma -0.5, B 6495235.763900986   channel a
pos-half max                   sigma +0.5, B 6483864.128985706   channel a
transfer factor e^{2 a_max h}  1.0259304941903822           h = 0.005
anchor raw-2264 (101 pts)      v_min >= raw, rel_max 2.44e-15
anchor 2243 sigma=1 row        C_upper rel 0.0 (bitwise), B rel 5.88e-16
```

Representative grid rows (`C` = certified min-channel product / (2π)²):

```text
sigma   C_channel_a           C_channel_b           binding   B_point
-0.5    164526.24390862274    6572727.195941412     a         6495235.763900986
 0.0    148229.17670194048    1838185.3175871747    a         5851853.338989304
+0.5    164238.19703123157    6570436.279456675     a         6483864.128985706
```

## Interpretation

- Channel a (`D₂_base · M_corr`) binds everywhere on the centered strip,
  because the corr-side second-derivative inflation is dominated by the
  2237 radius `r_corr = 2057069012.526474` — channel b is 40× larger at
  `σ = 0` and grows to 40× at both edges. The certified envelope is
  therefore an envelope of the *base-second-derivative* channel.
- The certified max sits at the strip boundary `σ = -1/2` (the raw
  min-product is nearly flat across the centered strip: `72812.57` at
  `-1/2` vs `72787.28` at `+1/2`, both below the `σ = 1` value
  `77444.14`), and the edge wins by `0.18%` over `+1/2` because the raw
  channel-a product peaks at `-1/2` by `0.53%` while the σ-inflation at
  `-1/2` is a factor `e^{-1.28}` smaller. The transfer then adds `2.6%`.
- The |σ| panel/inflation forms are conservative for `σ < 0` (the true
  weight decays on the negative half), so the certified negative-half
  numbers are slightly above the tightest attainable; the margin
  `1.4266×` is comfortable even so.
- Combined range: this record certifies `[-1/2, 1/2]` (the exact `hB`
  range); the 2234 frozen reduction already carries its own certified
  0.01-grid envelope on `[0, 1]` from which `bUpper2243` was taken.
  Together the union `[-1/2, 1]` — the range 2264 registered as the
  producer obligation — is covered at the 2243 standard, superseding
  the 2264 screen-grade audit.

## Nonclaims

- the numeric core (per-node upper chunks with the committed `2^-200`
  slack, 256-bit RNDN σ-sums with the 4-ulp guards, 2237 certified
  radii, the plain-float `coeff_inflation`/`majorant_phi_le` internals
  behind the guarded assembly) is exactly the 2243 machinery; no new
  certification standard is introduced by this record;
- for `σ < 0` the panel and inflation use the support-supremum weight
  `e^{a|σ|}` and the cross term `2|σ|m_{k+1}` — conservative, not
  tight;
- the σ-transfer is a grid-maximum times `e^{2a_max h}`, valid on the
  continuum `[-1/2, 1/2]` but not tight (`2.6%` at `h = 0.005`);
- the envelope bounds the strip product `N(σ)`; it does not by itself
  produce the Lean proof of `hB` (the truth of the strip bound for the
  concrete pair is a numeric statement now certified at artifact
  grade);
- no producer GO, no gate sign change, no RH claim.

## Provenance

- script: `scripts/routea_weighted_zero_sigma_envelope_certified_2267.py`;
- artifact: `results/2267_sigma_envelope_certified.json`
  (md5 `1df12e7319590fcadf4f1cd73713724a`);
- σ sums: `results/2234_sigma_{j}.json`, `j = -50..50`
  (negative half freshly produced by
  `scripts/routea_weighted_zero_direct_product_outward_2234.py`,
  `MODE=sigma SIGMA_INDEX=-50..-1`);
- gates/anchors: `results/2242_zero_count_certificate.json`,
  `results/2237_generation_certificate.json`,
  `results/2243_panel_cem_reprice.json`,
  `results/2264_sigma_range_audit.json`;
- predecessor records: `docs/proofs/2265_routea_weighted_zero_direct_product_decay_lean.md`,
  `docs/proofs/2264_routea_weighted_zero_sigma_range_audit.md`.
