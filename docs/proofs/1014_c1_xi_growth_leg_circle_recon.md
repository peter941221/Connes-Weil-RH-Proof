# 1014 — brick (H) growth leg: circle reconnaissance + order-1 minimum modulus (design)

Status: DESIGN (2026-08-15). H-A0, H-A1, and local H-A2 are now Lean-checked.
This document pins down H-A3 of the 1013 brick queue — the only genuinely new
analysis between those closed bricks and the canonical-sum identity.

## 1. Position in the (H) brick

```text
H-A0 weightedZeroSummable            [CLOSED 2026-08-15]
H-A1 analyticOnNhd of weighted sum   [CLOSED 2026-08-15]
H-A2 removable poles of G            [CLOSED 2026-08-15]
H-A3 growth leg  |G s| <= C(1+|s|) log(2+|s|) on circles |s| = R_k
       <-- THIS DESIGN; it is not a boundedness conclusion
H-A4 affine-growth consequence       (not yet constant)
H-A4b slope-zero / boundedness        <-- separate missing input
H-A5 constant-difference identity (H1)
H-B  segment bound (H2)
```

Critical constraint: **H-A3 must not use the identity** (H-A5 is downstream).
So both legs of `G(s) = logDeriv xi s - weightedSum s` are bounded from
closed inputs only.

## 2. The weighted-sum leg (closed)

Split the weighted sum at dyadic height `n0`, on the circle `|s| = R_k`:

```text
prefix (shells <= n0): finite principal part, O(9^n0)      CLOSED (1011)
tail   (shells >  n0): geometric (3/4)^n0, weighted        CLOSED
                       (brick G tail + 1 <= m_rho, H-A0)
```

The 1011 principal-bound structure applies verbatim to the concentric
circle (`C1XiQuantitativePrincipalBound` works on both tube boundaries),
and the tail is `regularizedZeroTail_norm_shellSum_le` inflated by the
multiplicity factor.  No new analysis in this leg.

## 3. The log-deriv leg: the boundary between closed and new

`|logDeriv xi(z0)|` on `|z0| = R_k` splits into:

```text
       numerator       |xi'(z0)| <= C1 * exp(C2 * R_k log R_k)
                       from xi's dyadic growth (CLOSED, Jensen sphere bound)
                       + Cauchy integral on the unit disc around z0

       denominator     |xi(z0)| >= exp(-C3 * R_k log R_k)      <--- NEW
                       order-1 minimum modulus on a zero-free circle
```

The denominator statement is new.  It is the classical minimum-modulus
theorem for entire functions of finite order (Titchmarsh 3.9; Pólya-Szegő),
made quantitative on dyadic circles — no mathlib counterpart exists in
v4.30 (the 1012 ruling correctly identified min-mod on the *tube center*
as unavailable; the *circle* version is a different, provable theorem: it
never needs a minimum at an arbitrary interior point, only on a circle that
can be chosen to avoid the zero lattice).

## 4. New theorem: order-1 minimum modulus on dyadic zero-free circles

The Lean statements mirror the closed tubes theorem
`exists_dyadic_quantitative_xiHeightBoundaryAvoidsZeros_tubes`
(`C1XiQuantitativeHeight.lean:408`) — same dyadic window, new geometry
(concentric circles instead of vertical tubes):

```lean
/-- Reconnaissance: every dyadic scale has a radius in the next unit window
whose circle avoids the zero lattice — the circle avatar of the closed
tubes theorem.  Count-bound + arc-measure, mirrors
`exists_dyadic_quantitative_xiHeightBoundaryAvoidsZeros_tubes`. -/
theorem exists_dyadic_quantitative_circleBoundaryAvoidsZeros (n : Nat) :
    ∃ R : Real, (2 : Real) ^ (n + 2) < R ∧
      R < (2 : Real) ^ (n + 2) + 1 ∧
      circleBoundaryAvoidsZeros R := by ...
  -- circleBoundaryAvoidsZeros R := ∀ z, ‖z‖ = R → completedRiemannXi z ≠ 0

/-- Order-1 minimum modulus on the free dyadic circle: the same R carries
an explicit lower bound, from Poisson's formula + the closed dyadic upper
growth + shell counts.  C3 is explicit in `spectralMultiplicityConstant`,
`log|xi(0)|` (closed computable value), and dyadic constants. -/
theorem dyadicXi_circle_minmod (n : Nat) :
    ∃ R : Real, (2 : Real) ^ (n + 2) < R ∧
      R < (2 : Real) ^ (n + 2) + 1 ∧
      (∀ z, ‖z‖ = R → ‖completedRiemannXi z‖ >=
        Real.exp (-(3 : Real) * (R + 1) * Real.log (R + 2))) := by ...
  -- C3 := 3 is the placeholder constant; the proof fixes its explicit value
  -- (K-factors + log|xi(0)|); the growth leg only needs "some C".

/-- Growth leg output (assembly; H-A3):  polynomial growth of
`G = logDeriv xi - weightedSum` on the circle family. -/
theorem growth_leg_polynomial_bound :
    ∃ C : Real, 0 < C ∧
      ∀ k : Nat, -- R_k from the two theorems above (same window)
        ∀ z, ‖z‖ = R_k →
          ‖logDeriv completedRiemannXi z - weightedRegularizedZeroSum z‖
            <= C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by ...
```

Proof skeleton (paper):

1. **Reconnaissance (circle-avoids-zeros)**.  A zero on the annulus
   `{R-1 <= |s| <= R+1}` has `dyadicShellIndex |Im rho| >= n0 - c`, so the
   count of such zeros is bounded by the closed shell mass
   `spectralHeightMultiplicity_geometric_bound` summed over ~2 shells.
   Each such zero rules out an arc of angular measure
   `<= 4 / (R * gap)`; with the mass bound this arc union has measure
   `< 2π` once

   ```text
   K * 3^n0 * (4 / R_k) < 2π/2,        R_k = 2^(n0 + c)
   ```

   which holds for all large `n0` (3/2 < 4/2 scale).  This mirrors the
   closed tubes theorem verbatim: same counting (dyadic window + mass
   bound → free boundary), new geometry (angular arcs on |s| = R instead
   of height intervals).

2. **Minimum modulus on the free circle** (the core step).  With a
   zero-free circle `|s| = R_k`, Jensen's formula on the disc (closed dyadic
   form in `C1XiQuantitativeHeight`) and the shell counts bound
   `log|xi(z0)|` below: Poisson's formula for `log|xi|` reproduces the
   point value from the circle values plus the zero correction; the
   correction is bounded by the count × log terms, and the circle values by
   the CLOSED dyadic upper growth.  The constant `C3` is explicit in
   `K`, `log|xi(0)|` (a closed computable value), and the dyadic constants.

3. **Compose** with Cauchy on `|xi'|` (section 3) to get
   `|logDeriv xi(z0)| <= C4 * R_k * log R_k`, then add the weighted leg
   (section 2): `|G(s)| <= C5 * (1 + |s|) log (2 + |s|)` on the family —
   affine-growth territory, not a Liouville constant conclusion.

## 5. Lean work list for H-A3

```text
( closed  ) 1011 principal O(9^n) on the circle        [mirror, CLOSED]
( closed  ) brick-G tail + H-A0 inflation              [CLOSED 2026-08-14]
( closed  ) Cauchy for xi' from dyadic growth          [new assembly of closed items]
( NEW     ) exists_dyadic_quantitative_circleBoundaryAvoidsZeros
            -- reconnaissance relabeled; mirrors the tubes theorem
( NEW     ) dyadicXi_circle_minmod : order-1 minimum modulus, dyadic quant.
            -- the one hard theorem; paper steps in 1013 R2 + section 4
( new-lite) growth_leg_polynomial_bound via composition (section 3 step 3)
```

Dependencies: H-A1 (analyticity of the weighted sum off the zero set, now
closed) is needed by H-A2 (removable poles) but NOT by the growth leg; the
leg only uses the closed xi growth + H-A0 tail + the two circle theorems
above.  H-A3's reconnaissance is structurally independent of H-A1/A2.

## 6. Fallbacks if minmod blocks

- **(GAMMA) brick revival** (1013 §5 demoted): if the circle min-mod cannot
  be Lean'd in reasonable time, bound `|logDeriv xi|` on the segment
  through Stirling/digamma — restores the original route with the Gamma
  part explicit.  It is heavier in algebra but contains no order-1
  minimum-modulus theorem.
- **Borel–Carathéodory on zero-punctured discs**: equivalent content, worse
  shape (requires local logs everywhere on the circle; A-OK provides them,
  but the bookkeeping doubles).  Not recommended as first choice.

## 7. Status snapshot

| item | status |
|---|---|
| G patch (consumer-form norm helpers) | CLOSED (2026-08-14, commit 9ab36f2 + c2ca0f6) |
| H-A0 module (weighted summable + norm bound) | CLOSED (2026-08-14, commit c2ca0f6, axiom-clean) |
| A-OK (AnalyticLog) | CLOSED (2026-08-14, axiom readback `[propext, Classical.choice, Quot.sound]`) |
| H-A1 analyticOnNhd (weighted sum off the zero set) | CLOSED (2026-08-15, WSL2 verified) |
| H-A2 local removable-pole extension | CLOSED (2026-08-15, WSL2 verified) |
| 1014 design (+ circle statement skeleton) | this document (updated 2026-08-15) |

RH is not claimed; Gate-1/3U branches untouched.
