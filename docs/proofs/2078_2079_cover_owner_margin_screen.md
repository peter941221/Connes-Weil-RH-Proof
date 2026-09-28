# 2078/2079 - COVER owner-margin screening

Date: 2026-09-28.

Status: COVER-SAMPLED-NEGATIVE, NOT UNIFORM.

A coarse `m=400` screen was first used only to select parameter cells. Because
that evaluator is known to alias in the high-frequency window, it was not used
as evidence of the sign. The registered heights were then rerun at `m=6400`
with the same owner construction and `|xi| <= 40`, step `0.02`.

```text
gamma       scale       Q(|xi|<=40)
37.586178   0.88       -2.148344933047647e13
40.918719   0.88       -3.406049851783499e12
40.918719   0.90       -4.858771061468819e12
43.327073   0.88       -7.501608321416552e13
43.327073   0.90       -1.550821978647676e14
48.005151   0.88       -3.120262435063324e14
```

All six sampled owners are negative, including the original G8-H owner. The
G8-H reading agrees with record 2071. This removes evaluator aliasing as the
explanation for the sampled sign pattern.

Decision: `COVER-SAMPLED-NEGATIVE`. The result is not a uniform COVER proof:
there is no all-gamma/all-delta/all-scale quantifier closure, and the finite
window, tail, matrix, and model-to-real quantities are still candidates.
The next admissible move is a parameterized continuity/envelope certificate,
not a claim that six sample points cover the hypothetical-zero space.

Artifacts: `results/2078_cover_owner_margin_screen.json` and
`results/2079_cover_owner_margin_m6400.json`.
Scripts: `scripts/routea_cover_owner_margin_screen_2078.py` and
`scripts/routea_cover_owner_margin_m6400_2079.py`.