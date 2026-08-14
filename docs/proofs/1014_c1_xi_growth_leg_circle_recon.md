# 1014 — brick (H) growth leg: circle reconnaissance + order-1 minimum modulus (design)

Status: DESIGN (2026-08-14). This document pins down H-A3 of the 1013 brick
queue — the only genuinely new analysis between the closed bricks and the
canonical-sum identity.

## 1. Position in the (H) brick

```text
H-A0 weightedZeroSummable            (written 2026-08-14, WSL build in flight)
H-A1 analyticOnNhd of weighted sum   [after G-OK + A-OK]
H-A2 removable poles of G            [after A-OK]
H-A3 growth leg  |G s| <= C(1+|s|) on circles |s| = R_k   <-- THIS DESIGN
H-A4 Liouville: G constant
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

```lean
-- target statement shape (design only; names pending)
theorem exists_dyadic_minmod_circle
    {C : Real} (hC : 0 < C) :
    ∃ k : Nat, -- radius R_k = 2^k * scale with R_k -> infinity
      CircleZeroFree R_k ∧                        -- no zero on |s| = R_k
      ∀ z0, |z0| = R_k ->
        ‖completedRiemannXi z0‖ >= Real.exp (-C * (R_k + 1) * Real.log (R_k + 2))
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
   closed `exists_dyadic_quantitative_xiHeightBoundaryAvoidsZeros_tubes`
   structure (1011), re-based from vertical tubes to concentric circles —
   the same counting, new geometry.

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
   polynomial growth, Liouville territory (H-A4).

## 5. Lean work list for H-A3

```text
( closed  ) 1011 principal O(9^n) on the circle        [mirror, CLOSED]
( closed  ) brick-G tail + H-A0 inflation              [verification queue]
( closed  ) Cauchy for xi' from dyadic growth          [new assembly of closed items]
( NEW     ) circle_avoids_zeros_rk : dyadic reconnaissance relabeled
            -- count-bound + arc-measure, mirrors BoundaryAvoidsZeros
( NEW     ) minmod_dyadic_circle : order-1 minimum modulus, dyadic quant.
            -- the one hard theorem; paper steps in 1013 R2 + section 4
( new-lite) growth_leg via composition (section 3 step 3)
```

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
| H-A0 module (weighted summable + norm bound) | written; WSL build in flight (2026-08-14) |
| G patch (consumer-form norm helpers) | written; in the same build |
| A-OK (AnalyticLog) | compile-green in mirror; axiom readback pending |
| 1014 design | this document (2026-08-14) |

RH is not claimed; Gate-1/3U branches untouched.