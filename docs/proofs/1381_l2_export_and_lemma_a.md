# 1381 — L² export and the global mass bridge bound (N2β component #1)

Date: 2026-09-13. Commissioned by [1380](1380_n2beta_prerequisite_recon.md)
§4 (formalization ledger, item 1): the L² interface export, together with
the first N1d leaf — the [1377] Lemma A bound.

## 1. Preregistered increment (before build)

New leaf `ConnesWeilRH/Dev/C1CompactLogL2Export.lean` (+ paired Audit),
three declarations:

```text
compactLogL2sq (f : CompactLogTest) : Real :=
    Integral[x: Real] ‖f.test x‖^2                  (the norm accessor)

intervalIntegral_cauchySchwarz (hab : a <= b)
    (hu : ContinuousOn u (uIcc a b)) (hv : ContinuousOn v (uIcc a b)) :
    (∫ x in a..b, u x * v x)^2
        <= (∫ x in a..b, u x * u x) * (∫ x in a..b, v x * v x)

laplaceAt_sq_le (f : CompactLogTest) (hab : a < b)
    (hsupp : support f.test ⊆ Ioo a b) (s : ℂ) :
    ‖laplaceAt f s‖^2
        <= (∫ x in a..b, exp(2 * s.re * x)) * compactLogL2sq f
```

`laplaceAt_sq_le` is exactly [1377] Lemma A with the exact-antiderivative
constant in division-free integral form (`s.re = 0` reads `b - a`, the
sigma-line evaluation constant). Acceptance: `lake build` of the two files,
zero errors, `#print axioms` on all three declarations listing only
`propext, Classical.choice, Quot.sound`.

## 2. Proof architecture (preregistered)

1. Triangle: `norm_integral_le_integral_norm` on `laplaceAt f s` unfolded
   to the weighted integral; pointwise `Complex.norm_mul` + `Complex.norm_exp`
   + `Complex.mul_re` reduce the weight to `exp(s.re * x) * ‖f.test x‖`.
2. Window trim: pointwise indicator equality against `Ioo a b` (off-window
   vanishing from the support hypothesis), `integral_indicator`,
   `integral_of_le` (Ioo→Ioc via `setIntegral_congr_set` with the
   null-singleton difference), giving the interval-integral form.
3. Cauchy–Schwarz on the window by the DISCRIMINANT argument — no Lp/MemLp
   API: `∫ (u + t v)^2 >= 0` for all `t`, evaluated at `t = -B/A` with the
   `A = 0` degenerate case handled by a sign contradiction at
   `t = -(C+1)/B`. All side conditions are `ContinuousOn.intervalIntegrable`
   on the compact window closure.

## 3. Outcome

GREEN on try 9 (`Build completed successfully (3476 jobs)`, zero errors,
zero linter warnings on the leaf; audit prints all three declarations
depending only on `propext, Classical.choice, Quot.sound`, zero `sorryAx`).

As built (two deltas from the prereg, both cosmetic):

```text
compactLogL2sq (f : CompactLogTest) : Real :=
    Integral[x: Real] ‖f.test x‖ ^ 2                (norm accessor, unchanged)

intervalIntegral_cauchySchwarz (hab : a <= b)
    (hu hv : ContinuousOn _ (uIcc a b)) :
    (Integral u * v)^2 <= (Integral u^2) * (Integral v^2)
    -- squared integrands in POWER form, not u*u form

laplaceAt_sq_le (f : CompactLogTest) (hab : a < b)
    (hsupp : support f.test ⊆ Ioo a b) (s : ℂ) :
    ‖laplaceAt f s‖^2
        <= (Integral exp(2 * s.re * x)) * compactLogL2sq f
```

`laplaceAt_sq_le` is exactly [1377] Lemma A with the exact-antiderivative
constant in division-free integral form.  The Cauchy-Schwarz lemma is the
discriminant argument formalized from scratch (no Lp/MemLp API): the
`A = 0` degenerate branch by contradiction at `t = -(C+1)/B`, the main
branch by evaluating `∫(u+t v)^2 ≥ 0` at `t = -B/A` and clearing the
denominator with `mul_le_mul_of_nonneg_left` + `field_simp`.

Build-loop trap ledger (v4.30 verified, forwarded to the project AGENTS
§7b): the two-namespace split for `CompactLogTest`/`laplaceAt`;
`intervalIntegral.integral_nonneg` takes `hab` first; `sq_nonneg` is power
form; `Set.Ioc` is LEFT-open right-closed; `rw` across `integral_add`
splits pairs `(h1.add h2, h3)` and needs one `integral_const_mul` per
distinct constant; rewrite patterns must be syntactic subtrees of the
SPLICED hypothesis shape (the leading `C` term groups with `2*t*B`);
`integral_congr_ae` on an inequality goal strands `?G` in a stuck
`NormedSpace` typeclass — route through `le_of_eq` first; beta-redexes on
congruence goals block `rw` (use `beta_reduce`); `TestFunction` coercions
in `have` statements need `(e.test : ℝ → ℂ) x` annotations;
`measurableSet_Ioc` is root-level in v4.30; `push_neg` is deprecated.

## 4. Honesty ledger

No digits; no closure claim; RH NOT claimed. The sharpness direction
([1377] Lemma A-prime) is NOT in this increment.
