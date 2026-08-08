# Proof-717 analytic target: the exact operator identity behind Gate 3U

Date: 2026-08-07. Status: **exact target located; open (analytic).**

## 0. Why this exists

Gate 3U at unit scale reduces (axiom-clean Lean) to one open premise
`hright = sum_i |right (sourcePhysicalCoframeLeakage) (basis_i)|^2 <= fixedMajorant`.
The library `boundedPrecomp_right_tsum_le_of_norm_le_one`
(`CCM24FiniteSFixedQuotientContractionBound:96`) reduces it to needing
`|sourceSoninCoframeLeakage| <= 1`. `CCM24FiniteSEndpointContractionGuard`
pins that this is equivalent to the collapse `D_S == J`.

## 1. The exact operators (all axiom-clean defs, verified by full build)

Metric dual coframe
`D = finiteEulerMetricCoframe = (T_dag T) o J o G^{-1}`,
where `G = J^dag (T_dag T) J` is the source-Gram and `J` is the Sonin inclusion;
biorthogonal: `J^dag D = I`
(`sourceInclusionAdjoint_comp_metricCoframe`), so `|D| >= 1`.

Forward actual-band coframe
`F = sourceActualBandForwardCoframe = P_band o (normalizedInverse) o J`,
with `J^dag F = 0`
(`sourceInclusionAdjoint_comp_sourceActualBandForwardCoframe_eq_zero`).

Combined endpoint coframe
`D_S = sourceActualBandForwardEndpointCoframe = F + D`.
It is the biorthogonal right-inverse frame: `J^dag D_S = I`, and its
source-Sonin compression is exactly `J`
(`sourceSoninProjection_comp_sourceActualBandForwardEndpointCoframe`).

Off-Sonin leakage
`L = sourceActualBandCombinedCoframeLeakage = (I - R_S) o D_S = D_S - J`.
`J^dag L = 0` (`sourceInclusionAdjoint_comp_sourceActualBandCombinedCoframeLeakage_eq_zero`).

## 2. Gate 3U / Proof-717 is exactly `L == 0` (equivalently `|L| <= 1`, `D_S == J`)

- `|D_S| >= 1` because `J^dag D_S = I` (right inverse of a norm<=1 adjoint).
- `|D_S| <= 1 <-> L == 0` (EndpointContractionGuard principal equivalence);
  then `D_S == J`, i.e. the collapse.
- Hence the `hright` premise holds exactly iff
  `F + D == J`  (the compression equality).

Single analytic operator identity to resolve:

```
  sourceBandProjection o (normalizedInverse) o J   +   D   ==   J
```

## 3. Component numeric evidence (vetted probes 815-824, §8c hygiene)

The only probe channels the repo trusts are ones free of the (unreachable)
Sonin intersection; that is the OUTER channel `(I - R_S) o D`. Across
resolution (n:200..6000) and interval (L:4..32) it PLATEAUS to a positive
constant (floor >= 0.369, ~0.62 on the transported frame) and never decays.
So the raw metric coframe is genuinely not `J` off the Sonin band.

What remains open is whether the forward term `F` cancels that off-Sonin part
in the full sum `F + D == J`.

## 4. Honest status

- ALGEBRAIC: everything above is axiom-clean and committed.
- ANALYTIC: the identity `F + D == J` is OPEN. It mixes (i) the source-band
  compressed first-order kernel and (ii) the biorthogonal metric coframe.
  No Lean rearrangement forces it.
- NUMERIC: the outer channel alone never decays, so the simple part of the
  leakage is nonzero; the only way `D_S == J` survives is if `F` cancels the
  metric off-Sonin channel exactly (a genuine analytic cancellation, which a
  finite grid cannot confirm nor rule out honestly).

## 5. Minimal remaining check (for a future attack)

(1) Outer: prove `|(I - R_S) o D|` has a positive lower bound (then the raw
    leakage is big); numerics say TRUE.
(2) Cancellation: settle whether `F` cancels that; the exact question is
    `L == 0 <-> F == -D + J`.
(3) If (2) is flat FALSE for a concrete in-library carrier, that is a genuine
    counterexample (negates the route); otherwise it must be proven.

Status: OPEN (analytic). Not closed by Lean rearrangement; numerics lean
negative for the outer channel but do not decide the full sum.

## 7. What is ALREADY proven vs the ONE missing content (2026-08-08 re-audit)

All algebraic pieces of `D_S = J` are already in Lean (axiom-clean):

    J^+ (F+D) = I   (J^+F = 0 and J^+D = I, both proven)    # co-domain (dual) side
    P (F+D)    = J  (P F = 0 and P D = J, both proven)      # P-side is automatic

where P = sourceSoninProjection = J J^+ on its range.  Neither forces the
ORTHOGONAL-to-source component.

Exact reduction (from the already-proven envelope identities):

    L := D_S - J          (sourceActualBandCombinedCoframeLeakage)
       = (F + D) - J = F + (D - J) = F + sourceSoninCoframeLeakage    [proven]

    Gate-3U <=> |L|<=1 <=> L = 0 <=> F = -(D-J).

Decompose into P-component and (I-P)-component.  By construction:
    P F = 0   (proven: sourceSoninProjection_comp_sourceActualBandForwardCoframe_eq_zero)
    P (D-J) = P D - P J = J - J = 0   (P D = J and P J = J, both proven)

So the P-component of `F + (D-J)` is 0 automatically.  The ENTIRE content of Gate-3U
is the (I-P)-component:

    (I - P)(F + (D - J)) = 0     <==>     (I-P) F = -(I-P) D      (*)

because (I-P)(D-J) = (I-P)D (since (I-P)J = 0).  The identity (*) on the
(range P)^-perp is the ONE open analytic component; nothing above it (in the
rank-P direction) remains to be proven in Lean algebra.

Status: the single off-Sonin component (*) is the whole remaining Proof-717
cancellation.  Numeric 824/884 measure (I-P)D (its magnitude ~0.61), not (*);
closing (*) needs the exact forward band coframe F evaluated on (range J)^perp
- beyond a finite grid (an analytic operator identity).
## 8. Family-search result (2026-08-08): only the nil family closes; reachable nonempty leak

Q (option 1): does any *test family* satisfy `(*)` `(I-P)F = -(I-P)D`?

Lean: (*) holds iff L = 0 (leakage zero).  The only family Lean proves closes is the nil
family (`visiblePrimes = []`, degenerate carrier) via
`sourcePhysicalCoframeLeakage_eq_zero_of_visiblePrimes_nil`.  For any nonempty finite prime
family, L is a genuine off-Sonin operator no route theorem annihilates.  Numeric 815-824 and
the scale sweep 884 show the D-side `(I-P)D = D-J` is nonvanishing (floor ~0.6) on every
reachable carrier and never zeroed by a nonzero family.

Conclusion: no nonempty family is known on which (*) holds; the nil family is degenerate and
unusable.  A positive outcome for any nonempty family requires the exact infinite operator
(P on the full Sonin intersection), beyond any finite grid -- equal to the open analytic
gap itself, not a family selection.
