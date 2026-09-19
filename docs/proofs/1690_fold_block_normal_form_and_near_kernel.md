# 1690 — The fold block in normal form: the counter-chirp near-kernel theorem (unconditional, erfc/truncation race), the no-index law F62, and the exact residual problem — the bone's local layer is complete; the bound itself is global

Date: 2026-09-19.

Status: proof record (paper level, hand-derived from committed
definitions) + one F61-compliant self-check rig
(`scripts/fold_witness_1690.py`, log
`build-logs/1690_fold_witness.log`).  The bone (uniform annular trace
bound) is by the machine-checked 1680 iff EXACTLY the endpoint gate, so
no completion short of RH exists; what this record completes is the
bone's LOCAL layer at the fold.  No uniform bound is proved and RH is
not claimed.

## 1. Theorem A — the fold block's normal form

Committed phase (1683, exact): `γ′(ξ) = 4π logλ − 2π logπ +
2π Re ψ(¼ + πiξ)`, hence `γ″(ξ) = 2π/ξ` and at the fold `ξ₀ = λ⁻²`:

```text
γ′(ξ₀) = 0  (asymptotically exact; 1683 bisection ratio 1.0000017)
γ″(ξ₀) = 2πλ²
```

Near `ξ₀` the committed symbol `Θ(ξ) = e^{iγ(ξ)}` is therefore a unitary
constant, a position shift, and a PURE CHIRP:

```text
Θ(ξ) ≈ e^{iγ(ξ₀)} e^{iπa(ξ−ξ₀)²},   a = λ².
```

The chirp multiplier's convolution kernel is the Fresnel kernel
`F_a(s) = a^{−1/2} e^{iπ/4} e^{−iπs²/a}` (free Schrödinger propagator at
time ∝ a), so the local two-sided block is the chirped Wiener–Hopf
corner

```text
A = P₊ F_a P₊      (cousin of 1673's fixed-half-line K_b P₊ K_b family).
```

Everything is stated in units of λ: the block has no intrinsic scale
(exact y = λŷ covariance — the rig reads BIT-IDENTICAL tables at
λ = 0.2 and λ = 0.1, an independent normal-form check).

## 2. Theorem B — the fold block is never bounded below (constructive)

For every a > 0, over unit vectors of L²(0, ∞):

```text
inf ‖P₊ F_a P₊ b‖ / ‖b‖  =  0.
```

Witnesses (counter-chirped packets, F61-compliant fixed ansatz):

```text
b_{d,w}(y) = e^{−(y−d)²/(2w²)} e^{+iπy²/a} e^{+2πi(d/a)y} 1_{y>0},
```

Proof: the quadratic input factor cancels the kernel chirp EXACTLY —
the remaining y-phase is linear (`−π(x−y)²/a + πy²/a + 2π(d/a)y =
−πx²/a + 2πy(x+d)/a`), so the output is the exact Gaussian FT sheared
to a peak at `x = aq = −d < 0`.  The surviving P₊ mass is bounded by
the RACE of two explicit terms:

```text
r(d,w)²  ≲  erfc(2πwd/a)                    (Gaussian-FT survivor tail)
             +  C a e^{−(d/w)²} / (d w)     (one-sided truncation:
                                               algebraic FT tail of the
                                               y = 0 jump, whose value
                                               is e^{−(d/w)²/2}),
```

and both terms → 0 along `d/w → ∞` AND `wd/a → ∞` (e.g. `d = kλ`,
`w = λ/√k`).  ∎ (paper level)

Rig self-check (F27/F28: the derivation above is the authority; the rig
is the check) — measured depth vs the race calibration, `r ≈ max` of
the two terms:

```text
+--------------------------------------------------------------+
| (d, w) in λ | measured r | race prediction | ratio           |
+--------------+------------+-----------------+----------------+
| (2, 0.5)     | 3.675e-05  | 4.010e-05       | 0.92            |
| (2, 1)       | 1.085e-02  | 1.144e-02       | 0.95            |
| (2, 2)       | 3.567e-02  | 3.625e-02       | 0.98            |
| (4, 1)       | 1.818e-05  | 2.005e-05       | 0.91            |
| (4, 2)       | 5.150e-03  | 5.720e-03       | 0.90            |
| (8, 2)       | 5.493e-05  | 1.003e-05       | 5.5 (transition)|
| (4, 0.5)     | 5.276e-15  | 1.071e-15       | grid floor      |
| (8, 0.5)     | 2.607e-14  | 1.5e-57         | grid floor      |
| (8, 1)       | 8.182e-13  | 5.4e-16         | grid floor      |
+--------------------------------------------------------------+
```

Controls: identity block r = 1; unchirped interior bump r = 1.0000 (no
counter-chirp ⇒ no shear — chirp cancellation is essential, not generic
smallness); q-sweep at (4λ, λ): r(q = +d/a) = 1.000000, r(0) = 0.6966
(= 1/√2 up to truncation — predicted 0.7071), r(−d/2a) = 2.7e-5,
r(−d/a) = 1.8e-5 — the minimum sits at the designed address.  Shape
check: on-grid output vs the algebraic truncation tail correlation =
0.999937 (vs 0.066 against the off-grid Gaussian peak) — the tail
mechanism is confirmed to four digits.

## 3. Law F62 — the committed symbol has NO Wiener–Hopf index

`γ` is odd (`Θ(−ξ) = conj Θ(ξ)`, since `m(−ξ) = conj m(ξ)` on ℝ) and
`γ′(ξ) = 4π logλ + 2π log ξ + o(1)`, so `γ(ξ) ~ 2π(ξ log|ξ| − |ξ|)(±) +
4π logλ · ξ` diverges in BOTH directions: `Θ(ξ)` winds around the unit
circle infinitely often as `ξ → ±∞` and has NO limit in 𝕋.  Hence `Θ`
is not a Wiener–Hopf symbol: the classical index, Fredholm criterion,
and factorization machinery do not apply — at the fold block and a
fortiori to the committed carrier block.  This voids the whole
classical-WH route family in one line (same function as F40 did for the
BM criterion route).  Caveat: generalized "spiraling symbol" theories
are not covered by this law.

## 4. The exact residual problem (self-dual)

The exact face left open by Theorem B is the pure-chirp two-sided
problem: does there exist W ≠ 0 with

```text
W ∈ H²(ℂ₋),   e^{iπaz²} W ∈ H²(ℂ₊)?
```

Patching across ℝ (edge-of-the-wedge with L² control) shows any such W
is ENTIRE; on ℝ both factors are unimodular-weighted, so the problem is
self-dual (W ↔ its own transform-type), and Theorem B says the
approximate version is always solvable at the race rate.  This is the
precise analytic form of "does the fold carry an atom or only a
continuous concentration" in the 1682/1683 two-sided measure picture.
Exact kernel ⟹ atom; kernel-free + race ⟹ concentration below every
fixed-ansatz scale.

## 5. What this does to the two fronts

* Front A (the bone): the uniform annular bound can no longer rest on
  any LOCAL estimate at the fold — the local block is provably never
  bounded below (Theorem B), so any local freeness would be contradicted
  by explicit near-kernel vectors.  The bound, if true, is GLOBAL: it
  must come from the two-sided measure's finite total mass.  The
  1682/1683 localization (content = fold + two-sided structure) is now a
  proved dichotomy at the fold's normal form.
* Front B: 1684's obligation 2b ("P₊U_λ not bounded below") is now a
  THEOREM at the fold's normal form — constructive, with the explicit
  race rate, and with the witness scale identified: packets at height
  d ≳ λ above the edge with w ≲ λ/√k.  The exact face (carrier
  nonemptiness, F33) stays open in the form of §4.

## 6. Boundary

By the machine-checked 1680 iff, this bone is EXACTLY the endpoint gate:
completing it IS proving RH, and no softer sufficient condition exists.
Completed today: the fold's local layer — normal form (Thm A),
unconditional constructive near-kernel theorem with race rate (Thm B),
no-index law F62, and the exact residual problem (§4).  Still open: the
global two-sided finite-mass statement, the §4 exact face, and
everything they are equivalent to.  RH is not claimed.
