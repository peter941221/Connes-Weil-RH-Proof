# 995 - Gate-3U `(*)` reduced to `F = J - D`; the refutation target is band-mass of `(J-D)`

Date: 2026-08-11. Status: analytic reduction from repo-verified defs; the concrete
nonempty-family counterexample step stays computed-but-not-formal. No Lean edit (mirror is
dirty), no sorry, no axiom. RH NOT claimed. See docs/872, 872b, 861, 928.

## 0. The objects (repo-verified, axiom-clean defs)

- J = sourceInclusion lambda : sourceSoninCarrier ->L finiteSCarrier (the Sonin inclusion)
- S = sourceSoninProjection lambda : finiteSCarrier ->L finiteSCarrier, IsStarProjection,
     S J = J, S(metric-Cofr)Data = J  (S D = J)
- R0 = radialSupportProjection lambda (radial compact band), IsStarProjection
- B = sourceBandProjection = R0 - S  (the annular band R0 minus Sonin subspace)
- N = normalizedFiniteEulerInverse family = c_S * (finiteEulerInverseOperator family)
- F = sourceActualBandForwardCoframe = B o N o J     [F lands in range B]
- D = finiteEulerMetricCoframe = E_gram o J o G^{-1}  (J-dagger D = I, biorthogonal)

## 1. The Gate-3U / Proof-723 condition (channel split, repo theorem)

    ||sourceActualBandForwardEndpointCoframe|| <= 1
      <==>  sourceActualBandForwardCoframe + sourcePhysicalCoframeLeakage = 0
      <==>  Outer + Forward + BandMetric = 0                (single equation, not split)
           (CCM24FiniteSPhysicalCancellationChannelSplit)

docs/2 872/872b further reduce to ONE off-Sonin component:

    (*)  (I - S) F = -(I - S) D     on the source carrier

## 3. New reduction: Gate<-> F = J - D   (from SF=0, SD=J, SJ=J)

- S (F + D - J) = S F + S D - S J = 0 + J - J = 0           (P-component automatic)
- (I - S)(F + D - J) = (I - S) F + (I - S)(D - J)
       = F              (since S F = 0  => (I-S)F = F)
       + (D - J) - S(D - J)
       = F + (D - J)                                     (since S(D-J) = J - J = 0)
  So gate <-> F = -(D - J) = J - D.                       (operator equality on carrier)

Hence THE single object:
   [Gate]  F = B o N o J  ==  J     -   D     =  (I - (J^? ..))...
i.e.  B o N o J = J - (E_amb o J o G^{-1}).

## 3. Necessary (and refutable) condition: (J - D) has no mass outside band B

F maps into range(B) (B = sourceBandProjection = R0 - S), so:
   Gate  =>  (I - B) (J - D) = 0,
   i.e.  (I - (R0 - S)) (J - D) = 0   <=>   (J - D) lands wholly in the band B.

This is a clean, family-dependent, POSITIVE-code refutation target:
   if   || (I - (R0 - S)) (J - D) ||  /=  0   on any non-empty carrier,
   the Gate FAILS for that family (route-refutation).

## 4. Why previous numerics cannot decide this, and what would

SYMBOL WARNING (2026-08-11 audit, cross-checked against docs/815/884 + AGENTS s2 Apex):
in this doc, `R0 = radialSupportProjection` (compact band, COMPUTABLE) and
`S = sourceSoninProjection` (the unreachable exact Sonin).  docs/815/884 and AGENTS
name the SAME computable radial projection `R` (OuterChannel = (I-R) o D), so `S` here
and `R` there are THE SAME operator.  The probe 824/884 measures `|(I-R_radial) o D|`,
NOT `|(I-Sonin) o D|`.

- Outer probe (824/884) measures `|(I-R0) o D| = |D - R0(D)| ~ 0.6`, flat in
  log-lambda in [-2,2].  Per 815 the GATE's OUTER channel is exactly this
  `(I-R0_radial) o D`, so it is the honest, computable off-band leak.  It is
  NOT `D - J`: that identity holds for the SONIN projection `(I-S)D = D-J`, and
  the probes never touch Sonin S.
- The DECISIVE second quantity `(I-(R0-S))(D-J)` (band-cancel mass of D-J) needs the
  exact off-band projection of D - J, i.e. exactly S (the unreachable Sonin
  intersection AGENT 818/819).  So numerics cannot rule the band-cancellation in/out.
  It is exactly the previously-flagged open bottom (docs/872 F == J - D cancellation).
- A PROOF that (J-D) has any off-band nonzero component (e.g. from the support non-decay,
  docs/927: ||Support(B)|| does not decay in B, so E_amb J G^{-1} - J cannot stay in the
  compact radial band) would CONCRETELY refute Gate for non-empty families, i.e. resolve
  the route with a counterexample instead of a missing lemma.  The ALREADY-computable
  route is the OUTER channel (docs/997): one nonzero image of `(I-R0_radial) o D`
  suffices (channels orthogonal, docs/815).

## 5. Route-decision (documented, docs/928 remains standing)

- canonical deliverable = finite-band Route-A bandTerminalGate (already closed, sorry-free).
- The infinite-carrier Gate reduces to the SINGLE equality F = J - D, whose value for a
  non-empty family is the last firewall.  The refutation check is the projection
  (I - (R0 - S))(J - D) != 0, and the evidence (support non-decay docs/927, outer 0.61
  scale-robust 884) is collectively negative, i.e. leans toward REFUTATION of the
  infinite-carrier gate for non-empty families - but that is NOT yet a formal Lean proof.

## 6. Hand-off (if a next session wants to close it)

Precisely: prove or refute, for a NON-empty finite-prime family with carrier lambda,
the projection condition

    (I - B)(J - D) = 0 is FALSE

i.e. exhibit u with  || (I - B) (J u - D u) || > 0, where B = R0 - S.
This localizes the whole Proof-717 to one concrete, family-specific "off-band mass" estimate.

RH not claimed. No new axiom/sorry.
