# 1013 — brick (H): global regularized log-derivative identity (design)

Status: DESIGN (2026-08-14). Following the 1012 route ruling, the horizontal
edge bottom is attacked through the canonical-sum lane:

```text
xi'/xi(s) = b + sum over ALL nontrivial zeros rho of m_rho * (1/(s-rho) + 1/rho)
```

where `m_rho = xiMultiplicity rho` (analytic multiplicity, possibly > 1).
This document fixes the target forms, records the multiplicity-critical
design decisions, and lists the Lean theorem queue with dependencies.

## 1. Target forms (cut to Gate 2's needs)

(H1) Constant-difference identity (no explicit recognition of `b`):

```lean
def weightedRegularizedZeroTerm (s : Complex) (rho : sourceNontrivialZeroSet) : Complex :=
  (xiMultiplicity rho : Complex) * regularizedZeroTerm s rho

theorem xi_logDeriv_weightedRegularizedSum_constant_diff
    {s s0 : Complex} (hlo : s ≠ s0) :   -- s0 an ordinary point, e.g. 2
    logDeriv completedRiemannXi s - ∑' rho, weightedRegularizedZeroTerm s rho =
      logDeriv completedRiemannXi s0 - ∑' rho, weightedRegularizedZeroTerm s0 rho
```

(H2) Segment bound (consumer form, assembled in ASM):
`|logDeriv xi s| <= principal O(9^n) + weighted tail (brick G style) + constant`
on each zero-free dyadic horizontal segment.

## 2. Design decisions

D1 (WEIGHTED, not unweighted): the identity must carry multiplicity `m_rho`.
At a zero of order m, `logDeriv xi` has pole `m/(s-rho)`; only the weighted
summand matches it. The unweighted brick-G sums remain the *bounds*, used
with `1 <= m_rho` to inflate.

D2 (CONSTANT-DIFFERENCE, no b-recognition): prove `G(s) = logDeriv xi s -
weightedSum s` is constant by (i) removable poles at every zero, (ii)
polynomial growth + Liouville.  No explicit value of `b` is ever needed by
the ASM assembly (adjacent edges cancel the constant).

D3 (GAMMA ABSORBED): with D1+D2 the Gamma part never appears explicitly:
`logDeriv completedRiemannXi` already contains the Gamma contribution and
the identity absorbs it into `b`.  The 1012 (GAMMA) brick drops from
"required" to "fallback" (used only if the growth leg must go through
Stirling instead of the closed dyadic xi growth).

D4 (WEIGHTED SUMMABILITY IS NEW-ANALYSIS-FREE): the dangerous bound
`m_rho^2 * (2||s|| / 4^n)` (from pointwise multiplicity bound `m <= K 3^n`)
diverges, but the shell mass bound saves it:

```text
sum over shell (m+n0+1) of m_rho * |term|
  <= (sum of shell masses) * max |term|          -- spectralHeightMultiplicity_geometric_bound
  <= (K * 3^(m+n0)) * (||s|| / (2^(m+n0+1) * 2^(m+n0)))   -- regularizedZeroTerm_norm_le
  = (K * ||s|| / 2) * (3/4)^(m+n0)               -- geometric, convergences
```

Total tail <= `2 * K * ||s|| * (3/4)^n0` + finite prefix.  All inputs are
CLOSED or in the verification queue (brick G).

## 3. Theorem queue (dependency order)

```text
( G-OK ) brick-G verification (unweighted sums)          [CLOSED 2026-08-14]
( A-OK ) AnalyticLog verification (local analytic logs)  [CLOSED 2026-08-14]

H-A0 weightedRegularizedZeroSummable (s) : Summable (weightedRegularizedZeroTerm s)
       -- shell mass bound + regularizedZeroTerm_norm_le; ~30 lines, mechanical
H-A1 regularizedSum_analyticOn_ball : AnalyticOnNhd (fun s => ∑' rho, wTerm s rho)
       open ball around any non-zero point
       -- H-A0 + uniform tail bound (regularizedZeroTail_norm_shellSum_le,
       -- |s| bounded on the ball) + Cauchy-Weierstrass
H-A2 removable_pole_at_sourceZero : G.extend analytic at every rho
       -- pole cancellation order m vs weighted term m/(s-rho);
       -- reassembly with AnalyticLog's local-branch technique
H-A3 growth_leg: |G s| <= C*(1+|s|) on growing circles |s| = R_k
       -- log-derivative bound from xi dyadic growth (CLOSED)
       -- + circle-avoids-zeros reconnaissance (dyadic ring, mirrors
       --   BoundaryAvoidsZeros structure) + weighted sum growth
H-A4 liouville_const: G constant
       -- polynomial growth + Cauchy estimates + Differentiable.apply_eq_apply_of_bounded
H-A5 xi_logDeriv_weightedRegularizedSum_constant_diff  (the H1 statement)
       -- A2 + A3 + A4 assembly
H-B  segment bound (H2): principal O(9^n) + weighted tail + constant
       -- CLOSED 1011 principal + H-A0 tail + H1, tension with dyadic tubes
```

Dependencies: H-A0 needs only (G-OK); H-A1/A2 need (G-OK)+(A-OK); H-A3/A4
new analysis of standard shape; H-B is ASM-facing assembly.

## 4. Risks and open points

R1 (REMOVED by the mass-bound argument, see D4): weighted summability would
have needed a sub-exponential multiplicity bound; the shell-mass trick
eliminates that need entirely.

R2 (OPEN, H-A3 shape): the exact dyadic ring for the circle-avoids-zeros
reconnaissance of `logDeriv xi` is not yet pinned; it mirrors the closed
`exists_dyadic_quantitative_xiHeightBoundaryAvoidsZeros_tubes` structure
(radius `T+2` family), and the growth leg must live between the tube radius
and the next shell — the only genuinely new analysis in this brick.

R3 (QUEUE): brick G and AnalyticLog both landed in the WSL mirror
(2026-08-14, both compile, G axiom-clean); H-A0's only dependency (G-OK) is
satisfied and H-A1/A2's (A-OK) too, so the H queue can start.

## 5. Cleanup edges

- The (GAMMA) brick in 1012 remains listed but demoted: pursue only if
  H-A3 provably cannot use the closed dyadic growth.
- `regularizedZeroTail_norm_shellSum_le` is the tail workhorse for both the
  unweighted (brick G) and weighted (H) shells; do not duplicate.

RH is not claimed; Gate-1/3U branches untouched.