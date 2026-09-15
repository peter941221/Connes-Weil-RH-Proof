# 014 — R3 doubled-shift Sonin transport and the moving-scale trace bridge

**Date:** 2026-09-15
**Status:** supporting route candidate; unit-scale base, T1 closed-subspace
transport, T1 projection transport, and actual source-side moving-scale
commutator trace legality are FORMAL; G8 cutoff transport/readback remain OPEN.
**Consumer:** the healthy-CompactLog, B5-shaped statement “0 <= C1SameOwnerWeil.qw g” for the exact tower-selected detector, followed by the existing same-detector contradiction and SourceRH wrapper.

This record refines [012](012_g8_same_owner_readback_rh_reachability.md) and [013](013_r3_sonin_detector_commutator_cancellation.md). It is not a new route authority, does not reopen B1, and does not claim RH. The source-side moving-scale trace witness is now formal; the remaining work is the cutoff/readback connection.

## 1. Review verdict

The candidate is logically RH-reachable but analytically unproved.

Positive evidence:

1. The exact source identity couples the second-support/prolate remainder to the Sonin commutator and the two outer branches.
2. The half-line compact-smooth model is trace class on paper; see [1429](../proofs/1429_r3_sonin_commutator_halfline_model.md).
3. The source already proves sourceThreeBranchCommutator_unit_isTraceClassAlong for the fixed unit scale and every named global basis, using sourceSoninCommutator_eq_threeBranch.
4. The selected detector commutes with every global logarithmic translation.

The negative evidence rules out the tempting shortcut: the radial and Fourier/Hardy projections move in opposite directions. Therefore the moving Sonin projection is not automatically a single unitary conjugate of the unit Sonin projection. The new problem is a doubled-shift intersection problem, not a relabeling of the unit theorem.

Current status:

    half-line boundary model              PAPER PASS
    unit-scale coupled trace legality     FORMAL PASS
    T1 closed-subspace transport         FORMAL PASS
    T1 projection transport              FORMAL PASS
    moving-scale source commutator        FORMAL TRACE LEGALITY
    source same-basis trace witness       FORMAL
    G8 cutoff/readback identification     OPEN
    R3                                   OPEN
    RH                                  not claimed

## 2. Formal facts already available

The following are committed source facts, not proposed premises.

    sourceSoninCommutator_eq_threeBranch
      exact Sonin commutator = three-branch commutator

    sourceThreeBranchCommutator_unit_isTraceClassAlong
      unit-scale three-branch commutator is trace class along every named basis

    radialSupportProjection_eq_translation_conjugation
      E_lambda = U_(-b) E_1 U_b, b = log(lambda)

    sourceFourierSupportProjection_eq_scale_conjugate_of_zero_defects
      Q_lambda = U_b Q_1 U_(-b), after the formal zero-defect theorem

    detectorOperator_comp_translation
      D U_b = U_b D

    doubledShiftHardy_involutive
      (U_(2*b) H)^2 = identity

Evidence locations:

- [CCM24UnitScaleStrictAngle.lean](../../ConnesWeilRH/Source/CCM25Concrete/CCM24UnitScaleStrictAngle.lean)
- [CCM24FiniteSGramResponse.lean](../../ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSGramResponse.lean)
- [CCM24RadialBoundaryPairTransport.lean](../../ConnesWeilRH/Source/CCM25Concrete/CCM24RadialBoundaryPairTransport.lean)
- [C1G8R3ZeroDefectClosure.lean](../../ConnesWeilRH/Dev/C1G8R3ZeroDefectClosure.lean)
- [C1G8R3DoubledShiftNormalForm.lean](../../ConnesWeilRH/Dev/C1G8R3DoubledShiftNormalForm.lean)
- [C1G8R3DoubledShiftSoninTransport.lean](../../ConnesWeilRH/Dev/C1G8R3DoubledShiftSoninTransport.lean)
- [1430 T1 verification record](../proofs/1430_r3_doubled_shift_sonin_transport_t1.md)

The unit theorem is a real advance over the original paper model, but its
source comment limits it to the fixed source endpoint. The new all-scale
source-side theorem supplies the moving-scale trace witness directly rather
than inferring it from abstract unitary invariance; see
[029](029_r3_moving_scale_source_commutator_trace_legality.md) and
[1466](../proofs/1466_r3_moving_scale_source_commutator_trace_legality.md).

## 3. Why naive scale transport is false

Let U_b denote global logarithmic translation, E_1 the unit radial half-line projection, and Q_1 the unit Fourier/Hardy support projection. The formal scale laws have opposite orientations:

    E_lambda = U_(-b) E_1 U_b
    Q_lambda = U_b Q_1 U_(-b)

where b = log(lambda). The actual Sonin projection is the orthogonal projection onto

    Ran(E_lambda) intersect Ran(Q_lambda).

A common-conjugacy claim would require the same orientation in both lines; it is therefore unavailable. Pulling the intersection back by U_(-b) gives the candidate normal form

    U_(-b) Ran(P_lambda)
      = U_(-2*b) Ran(E_1) intersect Ran(Q_1).

Equivalently, one may pull it back by U_b and place the doubled shift on the Fourier side. The existing K_b = U_(2*b) H involution is the Hardy-side organizer for this relative motion. It is not itself a trace estimate or a positivity theorem.

Because D U_b = U_b D, the commutator has the formal shape

    [P_lambda, D] = U_b [R_b, D] U_(-b),

where R_b is the projection onto U_(-2*b) Ran(E_1) intersect Ran(Q_1). This reduces the problem to a fixed detector and a doubled-shift family of intersections. It does not reduce it to the solved b = 0 member.

## 4. New mathematical target

### T1 — twisted intersection projection

Define Rspace(b) as the closed subspace

    U_(-2*b) Ran(E_1) intersect Ran(Q_1).

Prove, first at the continuous-operator level,

    P_lambda = U_b starProjection(Rspace(b)) U_(-b).

The closed-subspace transport and projection equality are now formal:

    map U_b Rspace(b) = Ran(E_lambda) intersect Ran(Q_lambda)

by `doubledShiftSoninClosedSubspace_map_eq_source` and
`doubledShiftSoninProjection_map_eq_source` in the Dev leaves. The latter uses the
committed star-projection API and the two opposite scale laws; see proof record
[1431](../proofs/1431_r3_doubled_shift_projection_transport.md).

### T2 — doubled-shift Hankel/Sonin trace estimate

The actual source-side commutator now has the required trace-class conclusion
at every selected scale. The direct theorem is for `sourceSoninProjection`
and `detectorOperator` on the source carrier; it does not separately estimate
each doubled-shift branch or claim an isolated leakage bound.

Acceptable outputs are:

- an explicit nuclear-kernel estimate;
- two genuine Hilbert–Schmidt factors for every trace term;
- a signed cancellation estimate for the complete commutator/remainder.

The estimate must be independent of any qw sign, RH, healthy-detector proposition, or universal Weil positivity.

### T3 — repository-level trace witness

The project uses PositiveTrace.IsTraceClassAlong along a named basis. Unitary
conjugation does not automatically preserve this predicate along the same
arbitrary basis. Record 1466 now proves the required witness directly for the
actual source commutator at every selected scale, without relying on abstract
unitary invariance. It also gives the exact same-basis ordinary-trace split
into the outer pair and coupled source remainder; see
[029](029_r3_moving_scale_source_commutator_trace_legality.md). This still
does not identify that trace with the G8 response.

### T4 — reconnect to R3

Use the transported signed trace together with the existing outer-pair identity to identify the exact G8 finite-cutoff remainder and its limit. Only then can the result produce G8SameOwnerReadbackData for the canonical owner.

## 5. Generation card

    candidate/id
      R3-SC2 / doubled-shift Sonin transport

    target
      P_lambda = U_b R_b U_(-b)
      R_b = projection onto U_(-2*b) Ran(E_1) intersect Ran(Q_1)
      plus a basis-compatible trace-class estimate for [R_b, D]

    novel move
      Treat opposite translation orientations as the source of a doubled
      relative shift, rather than erasing them by a false common-conjugacy claim.

    sign source
      signed commutator cancellation and Sonin antiresonance only;
      no universal positivity assertion.

    consumer
      0 <= C1SameOwnerWeil.qw g for the same tower-selected healthy detector.

    cheap falsifier
      Derive T1 from the two exact scale laws. If the intersection pullback
      does not type-check, kill the transport idea before trace estimates.
      Then test the doubled-shift half-line/Hardy model for a uniform S1 bound
      as |b| grows.

    anti-circularity
      No qw sign, RH, healthy-detector field, all-test gate, or external
      trace-formula dictionary may enter T1–T3.

## 6. Staged work and stop rules

    014-A  formalize the two opposite scale laws in one operator notation
    014-B  prove the closed-subspace pullback and T1                 FORMAL PASS
    014-B' prove transport of starProjection from the T1 range identity
             FORMAL PASS (batch 1431)
    014-C  derive the doubled-shift commutator identity
    014-D  prove source-side moving-scale trace legality       FORMAL (1466)
    014-E  build the named-basis IsTraceClassAlong witness    FORMAL (1466)
    014-F  identify the signed limit with the exact G8 ledger
    014-G  produce G8SameOwnerReadbackData and invoke the existing wrapper

The weighted two-projection attack coordinate remains documented in
[015](015_r3_weighted_two_projection_trace_bridge.md), with no uniform
Friedrichs-angle gap assumed. The immediate R3 obligation after the source
trace theorem is instead the exact source/G8 cutoff compatibility and signed
remainder limit.

The current formal result extends T1 with the conjugated orthogonal
projection
`doubledShiftSoninProjection b = U_b R_b U_(-b)`, proves it is a star
projection, and states its equality with the source projection at
`b = log lambda`.  The paired audit module now builds with zero errors and
only the three standard axioms; see proof record
[1431](../proofs/1431_r3_doubled_shift_projection_transport.md).  This closes
the projection-transport sub-obligation. Record 1466 separately proves the
actual source commutator trace witness at every selected scale. Neither result
identifies the signed trace limit with the G8 cutoff or proves G8 readback.

Record 1467 supplies an additional source-side trace owner: the exact
canonical finite-Euler corner is trace class at every selected scale and has
an ordered renewal readback along the named global basis. It still does not
identify that trace with the G8 cutoff ledger or its `qw` limit; the T4
source/G8 comparison remains open. See
[030](030_r3_canonical_finite_euler_corner_trace.md).

Kill the candidate if:

1. T1 needs a common conjugacy contradicting the opposite scale laws.
2. The doubled-shift model has an explicit non-summable trace tail.
3. The only estimate is one-sided Hilbert–Schmidt control with no second
   factor, nuclear kernel, or signed cancellation.
4. The proof changes the detector, owner, basis, visible prime family, or
   source cutoff.
5. Trace legality is proved but the signed limit cannot be identified with the
   G8 same-owner response.

## 7. RH reachability, precisely stated

If 014-A through 014-F are proved, they can discharge the commutator part of R3. If the remaining G8 endpoint and source/cutoff compatibility obligations also close, map 012 supplies:

    R3 readback
      -> G8SameOwnerReadbackData
      -> 0 <= qw g for the tower-selected detector
      -> contradiction to the formal detector qw g < 0
      -> SourceRH
      -> project RH output

Therefore this is a genuine RH-reaching subroute, but it is not yet a proof
of RH or a complete R3 proof. The exact remaining bottleneck is the signed
same-owner source/G8 cutoff identification and its vanishing remainder limit.
