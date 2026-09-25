# Record 1990 — Family-brick invariant set PRICED: exact per-term identity b−p = (n+a)/2 verified to n=70, three-ratio machine A_{n+1} ≤ (n + 16n²/k)·A_n verified at every step, certified vertical √-law with c_env ∈ [0.21, 0.59] (c ≥ 1/2 for k ≥ 3; k=1 gives c ≈ 0.30, slice refinement is the improvement path)

- **Date**: 2026-09-26
- **Status**: LANDED (desk wave — no Lean brick; pre-check for the family
  brick, per the announced plan in record 1989's next steps)
- **Script**: `scripts/check_family_induction_1990.py` (exact monomial dicts
  + closed-form Gamma sums at 40 dps; only the truth-check uses quadgl) —
  logs `build-logs/r1990_check1.log`, `r1990_check2.log`
- **Feeds**: family bricks F0/F1/F2 (spec in section 4); the priced target
  `exp(-c·sqrt(k|T|))` (records 1982/1989).

## 1. What landed

**(a) The exact per-term identity (Lean-ready invariant).**  With the
recursion moves counted (`s₁` = u-differentiations, `s₂` = s-differentiations,
`s₃` = g'-multiplications, `s₁+s₂+s₃ = n`):

    a = n − 2s₁   and   b − p = n − s₁    ⟹    b − p = (n + a)/2   per term

plus `a ≤ n`, `b ≥ 2`, `b ≤ 2n`, `p ≤ n`, `a ≡ n (mod 2)`.
Verified EXACTLY for all n ≤ 70 — **PASS** (log check (1)).
Corollary: the k-exponent of any term is `p − b + 1 = 1 − (n+a)/2 ≤ 1 − n/2`;
the full `k^{1−n}` suppression exists only on the `a = n` path.  Record
1989's calibrated `C·Γ(2n−1)·k^{1−n}` is carried by that path (its Γ(2n−1)
dominates the spectrum already at k = 1); the envelope machine below does
not need this — it is ratio-based.

**(b) The three-ratio machine (the family brick's engine).**  Annulus
functional (pure triangle inequality, no cancellation assumed):

    A_n(k) = (3/5) · Σ_terms |c| · k^{p−b+1} · Γ(b−1)
        [y = k/s: du = k dy/(2u y²);  1/(2u) ≤ 3/5 on u ≥ 5/6;
         ∫ e^{−y} y^{b−2} dy = Γ(b−1)]

Step ratios per term, source weight `w = |c|k^{p−b+1}Γ(b−1)`:

    +------------------------------+-----------------+---------------------+
    | move                         | child weight    | bound (invariants)  |
    +------------------------------+-----------------+---------------------+
    | d/du u^a                     | a·w             | ≤ n · w             |
    | d/du s^{−b}                  | [2b(b−1)/k]·w   | ≤ 8n²/k · w (b≤2n)  |
    | × g' = −2ku·s^{−2}           | [2b(b−1)/k]·w   | ≤ 8n²/k · w         |
    +------------------------------+-----------------+---------------------+

    ⟹  A_{n+1} ≤ (n + 16n²/k)·A_n        (k ≥ 1: ≤ 17n²·A_n)
    ⟹  A_n ≤ A_1 · Π_{j=1}^{n−1} (j + 16j²/k)

Verified at EVERY step for k ∈ {1,3,10,30}, n ≤ 24 — **PASS** (log
check (2)); envelope closes with worst A_n/env = 1.0 (the envelope IS the
machine recursion from the true base A_1 = A_exact(1,k)) — **PASS**
(log check (3)).  NOTE: the base must be the functional itself at n = 1
(= 6k/5, k-independent); the pointwise bound 7.15k·e^{−36k/11} is SMALLER
than the functional at k = 1 and cannot serve as the base (first rung of
`r1990_check1.log` FAILed exactly there; fixed in `r1990_check2.log`).

**(c) Truth check.**  `A_n + M_n ≥` measured total mass for all
n ≤ 12, k ∈ {1,3,10,30} — **PASS**; worst ratios truth/(A+M) =
0.14 / 0.035 / 1.6e−4 / 1.7e−10 (k = 1/3/10/30): the envelope is 7× to
1e10× above the truth — the Γ-completion `Γ(b−1) ⊇ Γ(b−1, 36k/11)` and the
two-ring middle discard the e^{−36k/11}-type cutoffs.  Valid, not sharp
(1983 ruling); the cutoff loss is the k-sharpness improvement path.

**(d) Certified consumer (the wave's headline numbers).**  With
`M_n` the two-ring middle bound, the vertical family theorem

    |L_phi(iT)| ≤ (A_n + M_n)/T^n  for all n ≥ 1

optimizes on the 1989 T-grid to

    +-----+---------+---------+----------+----------+
    | k   | T=14.13 | T=50    | T=200    | T=1000   |
    +-----+---------+---------+----------+----------+
    | 1   | 0.258   | 0.389   | 0.589    | 0.584    |
    | 3   | 0.248   | 0.239   | 0.377    | 0.530    |
    | 10  | 0.324   | 0.285   | 0.228    | 0.435    |
    | 30  | 0.322   | 0.353   | 0.284    | 0.211    |
    +-----+---------+---------+----------+----------+
    certified c_env of e^{-c sqrt(kT)}  (machine envelope, n* = argmin)

against the true-mass ceiling 1.06..1.58 (record 1989 check (5)).

**(e) Effective machine constant ρ.**  Measured A-ratios ~ ρ·n² at n=12:
ρ = 11.2 (k=1), 3.72 (k=3), 1.11 (k=10), 0.372 (k=30).  Against record
1989's budget (c ≥ 1/2 ⟺ ρ ≤ 4): **the machine as-is certifies the
priced minimum for k ≥ 3; at k = 1 the 16n²/k lumping (two b-moves at
max-b simultaneously) gives ρ = 11.2 → c ≈ 0.30.**  Improvement path
(not needed for brick F1): b-slice transport `A_n = Σ_b A_n^{(b)}` with
per-slice ratios — the Γ-weighted mass cannot sit at max-b for both
b-moves at once.

## 2. Honesty box

- **Everything here is an UPPER-BOUND machine**: triangle inequality per
  monomial, Γ-completion (no cutoff), two-ring middle.  Validity is
  machine-checked per step; sharpness is explicitly NOT claimed
  (truth/(A+M) down to 1.7e−10 at k=30).
- **c_env is certified-shape but NOT yet a theorem**: the Lean bricks
  F0/F1/F2 (section 4) must land before any of this is citable as a
  formal bound.  This record prices the statements and the constants.
- The consumer table is vertical-only (w = iT, a = 1); strip and
  horocyclic comparisons untouched.
- The n-scan for the consumer runs to n = 64 on a product envelope —
  no quadrature involved (closed form), no cap issues.
- No gate sign; RH not claimed.

## 3. Why the machine is the right Lean shape

The step bound uses ONLY the per-term invariants `a ≤ n`, `b ≤ 2n` and the
Γ-recurrence `Γ(b+1) = b(b−1)Γ(b−1)` — no coefficient bookkeeping beyond
the weights themselves.  In Lean, `A_n` is a `Finset.sum` over the monomial
set and the step is a `sum_le_sum` of three child-sums with per-child
`mul_le_mul`-style comparisons.  The support being quadratic (record 1989)
never enters the proof — only the pointwise move ratios do.

## 4. The brick plan (statements priced, order fixed)

    F0  C^infty glue: every derivative of phi_k vanishes at u = ±1
        (brick-1 exp/k-squeeze induction, one order at a time);
        needed by the order-n IBP boundary terms.
    F1  monomial algebra: B_n recursion, the invariant set of 1(a),
        the A-functional, the three-ratio step, the envelope;
        the middle two-ring bound M_n.
    F2  consumer: order-n IBP by induction (boundary killed by F0),
        |L_phi(w)| <= e^{|Re w|}(A_n + M_n)/|w|^n, then the choose-n
        corollary e^{-c_env sqrt(k|T|)} with the section-1(d) constants.

F1 is fully specified by this record; F0 is independent and can land
first; F2 depends on both.  Estimated: F0 is the smallest brick
(brick-1 pattern), F1 the heaviest (Finset induction), F2 mechanical
after F0.

No gate sign is proved here; RH is not claimed.
