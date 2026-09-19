# 1683 — The phase folds EXACTLY at λ⁻² (= 1633's ξ_c); the Clark-type surrogate is uniform and free on smooth branches; the gate content localizes at the fold and the two-sided structure

Date: 2026-09-19.

Status: one rig (`scripts/phase_clark_surrogate_1683.py`, F61-compliant:
function evaluations and root finding only, no carrier-grid readouts) +
analysis record.  All self-checks green.  No estimate is proved and RH
is not claimed.

## 1. What the rig verifies (all machine-read)

Committed inputs: `Θ(ξ) = e^{4πi(logλ)ξ} m(−ξ)`,
`m(−ξ) = G_ℝ(½+2πiξ)/G_ℝ(½−2πiξ)`, `G_ℝ(z) = π^{−z/2}Γ(z/2)` (1626
pin); continuous phase `γ = Im log Θ`; exact derivative via digamma.

```text
+------------------------------------------------------------------+
| check        | result                                             |
+--------------+----------------------------------------------------+
| FD vs exact  | rel 4e-15 .. 1e-12 (8 rows, 2 λ) — derivative      |
| derivative   | trusted                                            |
| fold         | 25.00004222 (λ=.2), 100.00001055 (λ=.1);           |
|              | ratio fold/λ⁻² = 1.0000017, 1.0000001              |
| asymptotics  | γ′ = 4πlogλ + 2πlogξ + o(1): rel 1e-5 (ξ=10)       |
|              | -> 3e-10 (ξ=1000)                                  |
| smooth-branch| mass density per unit ξ: 0.9974, 0.9998 (λ=.2),    |
| atom mass    | 0.9991, 0.9996 (λ=.1) — the pointwise invariant    |
|              | density × mass = 1 (m≡1 calibration reads 1.0)     |
| fold masses  | π/|γ′| = 0.72 -> 2.74 -> 10.25 as ξ -> λ⁻²         |
| weighted     | far-branch Σ m_k|𝓕h(x_k)|² ~ 1e-9 over a 49-unit   |
| surrogate    | window (C^∞_c bump): Schwartz decay wins           |
+------------------------------------------------------------------+
```

## 2. Verdict

1. **The fold is at ξ = λ⁻².**  The boundary phase of the committed
   symbol degenerates exactly at 1633's collapse frequency ξ_c = λ⁻².
   The kernel-side feature (1633/1634: `K∗h` collapse, position law)
   and the symbol-side feature (phase fold, atom collision) are the
   SAME point of the family seen from the two sides.  This is the
   first quantitative two-sided identification inside the committed
   vocabulary.
2. **The smooth-branch surrogate is FREE.**  On each monotone branch
   the Clark-type atom measure has uniform total mass density
   (measured = 1 per unit ξ, converging from both sides, both λ;
   m≡1 row exact).  Combined with the Schwartz decay of the committed
   test's weight `|𝓕h|²` (theorem-side, C^∞_c class), the smooth-branch
   surrogate total converges — it carries NO gate content.  This is
   the computational confirmation of 1682's trap analysis: any route
   that proves the estimate on the smooth branches proves the free
   inner-side-type bound and nothing.
3. **The content localizes at the fold and the two-sided structure.**
   The surrogate masses diverge at λ⁻² (0.72 -> 10.25 as ξ/fold:
   2 -> 1.05); what the TRUE canonical-system measure does at the fold
   (replace the divergent atoms by concentration of a different type)
   is exactly the analytic question behind 1633's collapse law and the
   1632 ε-gap — now with a precise symbol-side address: ξ = λ⁻².

## 3. Tooling notes (portable)

* `np.polynomial.legendre.leggauss` is O(n²)-scale: leggauss(8000) ≈
  75 s; never instantiate per-point node counts (the first run spent
  >15 min in ~300 node-size variants).  For oscillatory FT points use
  `scipy.integrate.quad` (ms per point).
* wsl.exe one-liners: heredocs (`<< EOF`) break just like `|`; use
  `python3 -c` or copy scripts.  Always run long python with `-u`
  (block buffering hides progress for tens of minutes).
* Transcription hazards caught by the rig's own self-checks (F27/F28
  discipline): the Γ-argument `¼ + πiξ` (not `½`), the `−2πiξ·logπ`
  term of `log G_ℝ`, and the 1631 kernel-side budget `γ′ = −2πlog|ξ|`
  does NOT transfer to the symbol side (correct asymptotics:
  `γ′ = 4πlogλ + 2πlogξ + o(1)`).
* One boundary-slack atom can enter the atom list (validation checks
  the mod-π residual, not window membership at the edges); the
  count-check flags it (65 vs 64).

## 4. Boundary

No uniform annular bound, no carrier nonemptiness, no RH.  The
deliverables are: the fold address ξ = λ⁻², the freeness of the
smooth-branch surrogate, and the localization of the remaining
content — the two-sided measure at the fold and its global
finite-mass structure.
