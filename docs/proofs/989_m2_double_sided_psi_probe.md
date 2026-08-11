# 989 — M.2: two-sided finite-vanishing healthy-ψ probe (corrected)

Date: 2026-08-11. Status: numeric evidence (WSL numpy). **RH NOT claimed.**
Companion: `docs/proofs/989_m2_double_sided_psi_probe.py`.

> ⚠️ This probe **corrects a mechanical conv-square-layout bug** (found while
> M.2 was being built). Read the "index-layout bug" section first. Precise
> impact: **988's "degenerate A≈0 / psi≈0" verdict is invalidated** (correct
> layout gives that one-sided test `psi=+0.0286`, `A=0.0367=‖g‖²`);
> **987's psi≈+0.86 is essentially unchanged** (0.8446 corrected) because its
> test `f` is even, so `F*F = F·conj(F)` and the healthy conv-square coincides.

## 0. The conv-square index bug in 987/988 (mechanism, fixed here, impact verified)

Previous probes (`docs/proofs/987_healthy_psi_probe.py`, `988_vanishing_probe.py`)
computed the healthy conv-square as:

```python
F = np.fft.rfft(g, nf)
gc = np.fft.irfft(F*F, nf)[:(2*n-1)]        # WRONG
center = (len(gc)-1)//2                      # WRONG index for x=0
A = gc[center]                               # was ~0
```

Two defects:

| defect | mechanism | consequence |
|---|---|---|
| `F*F` (square) vs `F·conj(F)` (power spectrum) | healthy CCM25 conv-square is `(g* ⋆ g)(x) = ∫ conj(g(-t))·g(x-t) dt`, i.e. **cross-correlation**, not plain self-convolution | for **non-even** `g` the center value is not `‖g‖²`. For **988's non-even ortho-complement `g`** this corrupts `A`; for **987's even bump** `F²=|F|²` exactly, so 987 is unaffected |
| center at `index=(2n-2)//2=n-1` | `irfft` layout puts **lag-0 / x=0 at index 0**, not at the middle | 988 read `A` at an out-of-support index → bogus `A≈0, psi≈0`; 987 labels `x=0` back at its own center, so its `A` is genuine |

Correct computation (`989_m2_double_sided_psi_probe.py:convSquare`):

```python
nf = 2**ceil(log2(2*n))
gc = np.fft.irfft(F*np.conj(F), nf)*dx    # x=0 at index 0, Riemann sum
A  = gc[0]                                # = (g* ⋆ g)(0) = ‖g‖² ≥ 0
```

For **real** `g` this is exactly the healthy conv-square, and the identity
`A = ‖g‖²` holds as a sanity assertion (it is `CompactLogConvolution.
convolutionSquare_zero_eq_integral_normSq` in Lean). **Verified impact (this build):** 988's "degenerate" verdict is invalidated — its
one-sided `(0.4,2.2)` test, under the correct layout, gives `A=0.0367=‖g‖²`
and `psi=+0.0286` (non-degenerate, positive), not `A≈0/psi≈0`. 987's
`psi≈+0.86` survives essentially unchanged (`0.8446` corrected): its test is
the even bump `f`, so `F*F = F·conj(F)` and the healthy conv-square
coincides; its irrelevance remains the untouched fact that the raw bump is
**not** in the finite-vanishing domain `{0,1/2,1}`, not a conv-square bug.

## 1. M.2 construction

Same single-lstsq orthogonal residual as 988, but with **two-sided** smooth
bump `q` (support `[lo,hi]`, `lo<0<hi`):

```
g = q − [1,e^{t/2},e^t]·coef ,  coef = OLS restricted to supp q
=> M(g,0)=0, M(g,1/2)=0, M(g,1)=0   (exact to ~1e-14)
```

- `q = smoothTransition((t−lo)/w)·smoothTransition((hi−t)/w)`, `w=(hi−lo)/2`.
- No second orthogonalization: the `e^{|t|}` re-pass (tried mid-build)
  breaks the exact vanish of `M(g,1/2)`, `M(g,1)`; the single lstsq is what
  preserves all three.
- `ψ = pole − arch − term2` with `pole = 2 Re M(gc, i/2)`,
  `arch = C·A + Integral_0^R`, `term2 = (log2)/√2·(gc(2)+gc(1/2))` on
  `gc = (g*⋆g)` — the `C1WeilExplicit.healthyPsi` formula
  (`Dev/C1WeilExplicit.lean`).

## 2. Results (healthier numbers, corrected conv-square)

Resolution-stable (N = 1e4·…·8e4, dom=4), all windows pass `A==‖g‖²` assert:

| window | A=‖g‖² | arch | pole | term2 | **ψ** | vanish M0/Mh/M1 |
|---|---|---|---|---|---|---|
| [-0.5,+1.5] | 0.0444 | −0.0215 | −0.0008 | −0.0082 | **+0.0289** | e-14/e-14/e-14 |
| [-1.0,+1.0] | 0.0444 | −0.0215 | −0.0008 | −0.0082 | **+0.0289** | e-15/… |
| [-1.5,+1.5] | 0.1004 | +0.0014 | −0.0048 | +0.0070 | **−0.0132** | e-16/… |
| [-2.0,+2.0] | 0.1876 | +0.0609 | −0.0162 | +0.0051 | **−0.0821** | e-14/… |
| [-1.0,+2.0] | 0.1004 | +0.0014 | −0.0048 | +0.0070 | **−0.0132** | e-14/… |
| [-1.2,+2.0] | 0.1153 | +0.0078 | −0.0064 | +0.0122 | **−0.0264** | e-14/… |
| [-1.5,+2.0] | 0.1400 | +0.0211 | −0.0094 | +0.0138 | **−0.0443** | e-14/… |
| [-2.0,+2.5] | 0.2424 | +0.1292 | −0.0243 | −0.0035 | **−0.1500** | e-14/… |
| [-1.5,+3.0] | 0.2424 | +0.1292 | −0.0243 | −0.0035 | **−0.1500** | e-14/… |

Resolution scan (N): `[-0.5,1.5]` psi +0.02883→+0.02890;
`[-1.5,2]` psi −0.04451→−0.04444; `[-2,2.5]` psi −0.15017→−0.15015
(5-sig stable across 1e4→8e4).

## 3. Interpretation (honest, no RH)

1. **Correct healthy conv-square is now anchored**: every window has
   `A=(g*⋆g)(0)=‖g‖²` (assert passed), the exact Lean identity. 988's
   "degenerate scale" verdict was a wrong index (plus `F*F` on a non-even `g`)
   in the probe code — it is not a mathematical fact about the criterion.
   987's even-bump `psi≈+0.86` (0.8446) is not affected by the index bug.
2. **The healthy ψ genuinely changes sign** within the finite-vanishing
   domain as the window/mass scales: small symmetric windows (`[-0.5,1.5]`)
   give ψ>0, larger/asymmetric windows (`[-1.5,2]`, `[-2,2.5]`,
   `[-1.5,3]`) give ψ<0. The `∀g` criterion is neither proven nor refuted by
   a finite instance list; but the *sign content* of
   `CC20FiniteVanishingWeilCriterion` is now concrete and measurable.
3. **`pole` stays small** (`≤ 2.5e-2`) while `|arch|` and `|term2|` dominate,
   sharing the 987 observation that the pole term is not the leading
   contribution on these compact finite-vanishing tests.

## 4. Bottom line

- Delivers the missing **correctly-dangled finite-vanishing two-sided test
  family** of `docs/988`'s explicit request, with exact three-Mellin
  vanish and `A=‖g‖²`.
- Fixes a mechanical (index+product) bug that silently corrupted all prior
  987/988 conv-square numerics.
- The healthy C1 clue (`weilLocalSum(star g) ≤ 0`) is now measurably
  **positive on some domain tests and negative on others** — the criterion's
  actual open content (RH-equivalent), not an assembly leaf.
- RH NOT claimed.

## Repro (WSL)
```
cd /mnt/c/Projects/Connes-Weil-RH-Proof
python3 docs/proofs/989_m2_double_sided_psi_probe.py
```
Requires numpy only.

## Next step
1. Use the `ψ<0` family (e.g. `[-1.5,2]`, `[-2,2.5]`) and the `ψ>0` family
   (`[-0.5,1.5]`) to locate the sign boundary, then attempt the analytic
   `ψ(g) ≤ 0` bound on the negative family — this is the real
   RH-equivalent step.
2. Port the negative-ψ test into Lean as a `CompactLogTest` (carrier
   `bumpPlateauTest` pattern already exists) and read
   `C1WeilExplicit.healthyPsi` on it, keeping it as evidence, not closure.