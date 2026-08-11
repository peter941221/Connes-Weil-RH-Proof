# 978 — Wall-A 1.4 `hI`: explicit-F complex engine closed; surviving leaf pinned

Date: 2026-08-11.  Status: execution record + forward spec for the Wall-A near band.
RH NOT claimed.

## Closed (axiom-clean) — `Dev/Wall14PlateauExplicitComplex.lean`
Build green; every helper `#print axioms = [propext, Classical.choice, Quot.sound]`, 0 sorry.

- `bumpExFunction : ℝ → ℂ` lifts the explicit plateau bump `bumpEx`.
- `bumpEx_contDiff : ContDiff ℝ ⊤ bumpEx` (via `Real.smoothTransition.contDiff`), hence
  `bumpExFunction_contDiff`.
- `bumpExFunction_hasCompactSupport` : support inside `[-1,1]` (`IsCompact.of_isClosed_subset`
  on `isCompact_Icc`; `bumpEx_ne_zero_imp_mem_Icc` from the support-zero lemma).
- `bumpSchwartz`, `bumpPlateauTest : CompactLogTest`, `bumpPlateauOwner : SelectedWeilSquareOwner`.
- `bumpA := Re F(0)`, `bumpA_eq_integral_normSq`, and
  `bumpA_ge_nine_fifths : 9/5 ≤ bumpA` (plateau `[-9/10,9/10]` gives `2*(9/10)=9/5`),
  `bumpA_pos`.

## Positive: the near band is now downstream of ONE provable slope constant
`g = plateauArchG = 2(e^{y/2}F − A)/den`, `F(0)=A`, `0≤F≤A`, `den≥2y` (proven).  On `(0,1]`,
if `|e^{y/2}F−A| ≤ c·A·y` then `|g| ≤ c·A` and `|∫_{(0,1]} g| ≤ c·A`.
Budget: near `c·A` + mid `1.40A` + tail `0.28A` ≤ `C≈3.10` ⇒ `c ≤ 1.43` suffices.

Guard decomposition (clean steps):
`X := e^{y/2}F − A = A(e^{y/2}−1) + e^{y/2}(F−A)`, so
- upper `X ≤ A·(e^{y/2}−1) ≤ A·(e^{1/2}−1)·y` (ratio ≤ ~0.6487 on [0,1]);
- lower `X ≥ A·(y/2) − e · (A−F)`.

So `|X| ≤ C·A·y` with `C = max(0.6487, 2.72·(A−F)/(A y))`.  A slack enough C ≤ 1.43 is
immediate once  we can bound `(A−F(y)) ≤ 0.5·A·y` on `[0,1]` (then C ≤ max(0.6487,
2.72·0.5/1) = 1.36).  `A−F` is `O(y²)` at 0 (F is even + smooth), so it is true; the
remaining work is a quantitative wall estimate.

## Next attacks (in priority order)
1. Prove `A−F(y) ≤ 0.5·A·y` on `[0,1]` for the explicit bump, using the explicit
   `bumpEx` values on the thin wall `(9/10,1)`; equivalently bound `F'(y)` via
   `F' = f*f'` (even `f`, `|f'| ≤ M` on the wall) or `F = smooth` second-difference.
2. Prove `e^{y/2}−1 ≤ (e^{1/2}−1)·y` on `[0,1]` (convexity / monotone ratio).
3. Assemble `|∫_(0,1] g| ≤ C·A`, then near/mid/tail ≤ C1+Cmid+Ctail, `3<C`,
   feed `bumpPlateauOwner` through `Wall14ArchSufficiency` +
   `archimedeanTerm_ne_zero_of_lead_pos_and_integral_bound`, full build + audit.

## Rules / hygiene
- Windows repo is the only source of truth; WSL mirror `a WSL build sandbox`
  is a build sandbox only (its `git rev-parse` escapes to `the WSL home` — never commit/push
  there). `flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build <target>`.
- No sorry/axiom; axioms must be `[propext, Classical.choice, Quot.sound]`.
- Do not touch closed Wall14 sufficiency/reduction/witness layers.