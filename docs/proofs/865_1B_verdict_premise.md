# 865 - 1B verdict: the single unproven premise for the infinite Gate trace is `hfactor` (= trace-class of the prolate remainder); it is not in-library and not degenerate-trivial

Status: structural verdict (no new Lean lemma). Date: 2026-08-07. Lane: 1B (analytic trace bound on the true Gate carrier).
Prereq: 860 (tail-trace block), 863 (1A vs 1B), 864 (decision brief). Follows the 1B-first recommendation.

## What 1B must produce (single line)
On the true Gate carrier `sourceSoninCarrier`, with `rho` infinite:

    |(ordinaryTraceAlong b (inverseLowerFactorPhysicalRenewalTailResponse ...)).re| <= bound

The whole-finite-S and prolate machinery (CCM24FiniteSFixedPhysicalEnergyBound, CCM24SourceProlateTrace)
can convert operator-norm bounds into trace bounds IF AND ONLY IF one premise is supplied:

## The one premise
The entire prolate trace-class pipeline is threaded through:

    hfactor : Summable fun i => ||sourceProlateHilbertSchmidtFactor lambda (globalBasis i)||^2

Every theorem in `CCM24FiniteSFixedPhysicalEnergyBound.lean` takes `hfactor` as an ASSUMPTION
(`(hfactor : Summable ...)` at :49,66,85,105,122,...). It is never proved there. The only route to
`hfactor` is `sourceProlateHilbertSchmidtFactor_summable_of_isTraceClassAlong` (CCM24SourceProlateTrace:74),
which requires

    hremainder : PositiveTrace.IsTraceClassAlong globalBasis (sourceProlateRemainder lambda)

`sourceProlateRemainder lambda = E_radial comp Q_fourier comp E_radial - sourceSoninProjection lambda`
(CCM24FiniteSProjectionTrace:155). So 1B collapses to producing:

    TraceClassAlong (some concrete globalBasis) (sourceProlateRemainder lambda)

is not a theorem in the repository: `sourceProlateRemainder_isTraceClassAlong ...` is the ONLY
declared name and it is NEVER used/applied anywhere in Source/Dev (grep: zero call-sites). `hfactor`
is carried as an open hypothesis into every downstream energy and Gate statement.

## Unit-scale reduction (what the remainder actually is)
At `lambda := unitSoninScale` (log lambda = 0), `CCM24UnitScaleProlateAlignment` proves
`sourceProlateRemainder unit = cc20TransportedProlateRemainder Hinf`
(unitScale:152). And `cc20TransportedProlateRemainder U` (GlobalLogSoninProjection:231) is

    P_posHalfLine comp (TrHaloP comp P_posHalfLine) - TrSonin   (U)

with `P_posHalfLine = cc20PositiveHalfLineProjection` (classical positive-halfline), and the
rest the transported Sonin/halfline projections. Via `cc20TransportedProlateRemainder_eq_complement_conjugation`
it is a positive quadratic `B'B` with `B = (P - TrSonin) comp ...`; it is IsPositive/IsSelfAdjoint.

## Why it is not trace-class for free
The factor `P - S` (or `P - Tr`) is a difference of TWO projections onto infinite-dimensional
closed subspaces of the infinite L2 carrier. A difference of projections is only finite-rank /
trace-class when the two ranges are commensurate; for the half-line vs the archimedean Sonin band
this is generically false (infinite-rank difference). So `IsTraceClassAlong (sourceProlateRemainder)`
cannot be produced from Summable operator-norm decay (the exponential tail) alone, and it is not
in the library. It is a GENUINELY NEW analytic Schatten/Hilbert-Schmidt certificate on the true
Gate carrier.

## Verdict
1B to close the infinite Gate needs ONE new object: trace-class (Hilbert-Schmidt summability) of
`sourceProlateRemainder lambda` on a concrete Hilbert basis of the finite-S carrier (unit reduces
it to the transported prolate remainder). That object is absent from the library, is not free, and
is the same analytic-wall the numeric probes 819-824 described. This does NOT prove it impossible;
it states the exact single certificate that must be supplied for 1B to close. If it can't be, 1B
stays open and the carrier re-point (1A) with the readout-invariance review is the alternative.

## What a next attempt should try (in order)
1. Prove `hremainder` at unit scale: `IsTraceClassAlong (some explicit basis) (TransportedProlateRemainder)`
   - needs a concrete basis of the half-line log-L2 that diagonalizes P vs S to a summable tail.
2. If 1 proves false (difference of projections on the infinite band generically not traceable),
   record the negative and move to 1A with the explicit Gate-readout-invariance re-review.
3. Keep the finite-band route (RouteATailBandBound, 861) as the current honest closed edge while 1B
   is assessed.

no fake theorem added: this file only records the exact open premise and its location.

## Decisive analytic closing (why the certificate is not merely missing but unreachable here)
At unit scale the remainder is P (U P U-dagger) - S on the L2 half-line: the halfline operator PQP minus the
Slepian intersection S. P and Q are infinite-rank projections with generically non-summable sample overlap,
so PQP is not of finite Schatten class. A difference of projections is trace-class only when the ranges are
commensurate; the archimedean half-line vs the Slepian/Sonin band is not (consistent with numeric probes
819-824, where the Son transport never decays). Hence IsTraceClassAlong(sourceProlateRemainder) fails on the
full L2 carrier; it would hold only under a finite/banded cutoff - which the carrier-stage would have to
impose, i.e. a carrier change (1A), not a theorem on the present one.

## Bottom line for 1B
1B as an analytic trace bound on the true infinite Gate carrier is blocked: the needed Schatten/Hilbert-
Schmidt certificate of the prolate remainder either does not exist or is not finite-rank on the infinite
carrier. It is not merely a Lean gap. To reopen the infinite Gate, the deciding move is 1A - re-point the
Gate carrier to a Hilbert-Schmidt / finite-rank basis and re-verify the Gate readout under the swap (owner-
invariance review). 1B stays recorded here as the confirmed open wall, with the exact premise and reason.
