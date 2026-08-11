# 990 — M.2 healthy-ψ sign boundary scan + Lean carrier port

Date: 2026-08-11. Status: numeric evidence + axiom-clean Lean port. **RH NOT claimed.**
Companions: `docs/proofs/990_m2_sign_boundary_scan.py`, `ConnesWeilRH/Dev/M2HealthyPsiPort.lean`.

## 1. Results (open with the sign)

Builds directly on the corrected 989 conv-square. Sweep the two-sided bump window
`(lo, hi)` (`hi > lo`, both sides of the log coordinate) of the finite-vanishing
ortho-residual family. `psi = pole - arch - finite-prime-{2}` on `(g* star g)`.

**Grid (psi sign; `+` if `psi>3e-3`, `-` if `psi<-3e-3`, `0` else):**

```
lo\hi       1.0      1.4      1.8      2.2      2.6      3.0      3.4
-2.6    - -0.0506 - -0.0821 - -0.1337 - -0.2086 - -0.3058 - -0.4206 - -0.5475
-2.2    - -0.0265 - -0.0506 - -0.0821 - -0.1337 - -0.2086 - -0.3058 - -0.4206
-1.8    0 +0.0014 - -0.0265 - -0.0506 - -0.0821 - -0.1337 - -0.2086 - -0.3058
-1.4    + +0.0263 0 +0.0014 - -0.0265 - -0.0506 - -0.0821 - -0.1337 - -0.2086
-1.0    + +0.0289 + +0.0263 0 +0.0014 - -0.0265 - -0.0506 - -0.0821 - -0.1337
-0.6    + +0.0271 + +0.0289 + +0.0263 0 +0.0014 - -0.0265 - -0.0506 - -0.0821
```

Key structural fact: **`psi(lo,hi)` depends only on the window WIDTH `w = hi-lo`,
not on its position** — each anti-diagonal of the grid (constant `w`) is exactly
constant to 5 digits. This is the log-coordinate translation invariance of the
ortho-complement construction: `Span{1,e^{t/2},e^t}` is invariant under
`t -> t + c`, and the healthy functionals (pole / arch / prime-{2} on `(g* star g)`)
transform so that the whole `psi` is position-independent.

**Finer hi sweep at fixed lo (monotone in width):**
- `lo=-1.2`: psi = +0.0159 (w=2.6) -> -0.1049 (w=4.2); zero between w=2.6 and w=2.8.
- `lo=-1.5`: -0.0061 (w=2.9) ... -0.1501 (w=4.5).
- `lo=-2.0`: -0.0385 (w=3.4) ... -0.2545 (w=5.0).

**Width-invariance probe (exact to 5 digits):**

```
w=2.4  lo-2.4:+0.02634  lo-2.0:+0.02634  lo-1.6:+0.02634  lo-1.2:+0.02634  lo-0.8:+0.02634
w=2.8  lo-2.4:+0.00137  lo-2.0:+0.00137  lo-1.6:+0.00137  lo-1.2:+0.00137  lo-0.8:+0.00137
w=3.2  lo-2.4:-0.02648  lo-2.0:-0.02648  lo-1.6:-0.02648  lo-1.2:-0.02648  lo-0.8:-0.02648
w=3.8  lo-2.4:-0.06443  lo-2.0:-0.06443  lo-1.6:-0.06443  lo-1.2:-0.06443  lo-0.8:-0.06443
```

**Sign boundary (bisection at `lo=-2.0`):** a single width threshold
`w* ~ 2.8175`; `psi>0` for `w<w*`, `psi<0` for `w>w*`.

## 2. Interpretation (honest, exposure both signs)

- **Narrow windows (`w<~2.82`) give `psi>0`** — a family in the direction that
  would *contradict* the criterion `weilLocalSum(star g) <= 0` if any of them were
  a valid in-domain test and the bound failed. It is a finite parametric family of
  bump-shaped windows; it is **not** a disproof (the criterion quantifies over all
  `CompactLogTest`, only a subset of which are these windows).
- **Wide windows (`w>~2.82`) give `psi<0`** — the criterion-satisfying direction,
  on the same bump-shaped family, monotone in width.
- Because `psi` is width-only (position-invariant), the negative family is
  **one-parameter**: take any window of width `> 2.82`. This is a much simpler
  analytic target than a general test: prove `psi(bump_w) <= 0` for all
  `w > 2.82` and the specific negative family is closed. The positive `w<2.82`
  family, if any element were a valid criterion counterexample, would be the
  obstruction to `forall g psi(g)<=0` — but it is not a proof either way.
- RH NOT claimed: both signs at finite instances neither prove nor refute the
  `forall` criterion.

## 3. Lean carrier port (M2HealthyPsiPort.lean)

`ConnesWeilRH/Dev/M2HealthyPsiPort.lean` makes the math expressible:

- `twoSidedCarrier : CompactLogTest` = `Dev.Wall14Plateau.bumpPlateauTest`
  (explicit two-sided flat-top bump, support `[-1,1]`, plateau `[-9/10,9/10]`).
  In the 990 width model this is the **width-2** window -> positive-psi side.
- `m2PsiValue : Real` = `C1WeilExplicit.healthyQw twoSidedCarrier`, the exact
  `pole - archimedian - finite-prime-{2}` value on the carrier convolution square,
  which the 989/990 numerics approximate by `pole - arch - term2`.
- Theorems: `twoSidedCarrier_zero` (`carrier.test 0 = 1`, genuinely nonzero),
  `twoSidedCarrier_hasCompactSupport`.

Verified in an isolated WSL build: `lake build ConnesWeilRH.Dev.M2HealthyPsiPort`
(2968 jobs) `#print axioms` = `[propext, Classical.choice, Quot.sound]`,
0 `sorryAx`, no project axiom. RH NOT asserted.

**Honest scope of the port:** it states the carrier and the value; it does *not*
prove the negative-psi bound nor the finite-vanishing of the ortho-residual `{0,1/2,1}`
(the ortho-complement / OLS / Mellin-vanishing step), both of which are open analytic math.
The negative-psi family (`w>2.82`) needs a width-scaled plateau
(support strictly wider than `[-1,1]`) not yet in the module.

## 4. Baseline (this is what Next-1+Next-2 were asked to deliver)

1. **Boundary located:** `psi` flips sign at `w* ~ 2.8175`, monotone in width,
   position-invariant. Negative family = `{w > 2.82}`. **Good / real content.**
2. **Lean carrier:** a `CompactLogTest`-valued handle + healthy-psi value exists
   axiom-clean (this is the negative-psi family is the width-2 shape, so the
   carrier squarely is the positive- side; the negative side is follow-on).

RH NOT claimed. Next: build the width-scaled plateau (`w > 2.82`) as a
`CompactLogTest` and close `psi <= 0` on it (open analytic leaf; the RH-equivalent
step).

## Repro (WSL)
```
cd /mnt/c/Projects/Connes-Weil-RH-Proof
python3 docs/proofs/990_m2_sign_boundary_scan.py   # numeric width scan
# Lean port: isolated WSL build of ConnesWeilRH.Dev.M2HealthyPsiPort (axiom audit above)
```
Requires numpy only.
