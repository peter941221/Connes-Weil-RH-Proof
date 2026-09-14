# 014 — R3 doubled-shift Sonin transport and the moving-scale trace bridge

**Date:** 2026-09-14
**Status:** supporting route candidate; formal unit-scale base, moving-scale transport OPEN.
**Consumer:** the healthy-CompactLog, B5-shaped statement “0 <= C1SameOwnerWeil.qw g” for the exact tower-selected detector, followed by the existing same-detector contradiction and SourceRH wrapper.

This record refines [012](012_g8_same_owner_readback_rh_reachability.md) and [013](013_r3_sonin_detector_commutator_cancellation.md). It is not a new route authority, does not reopen B1, and does not claim RH. It states the next new mathematics after the half-line model and the fixed unit-scale trace theorem have both been checked.

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
    moving-scale Sonin transport          OPEN
    basis-compatible trace witness        OPEN
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

The unit theorem is a real advance over the original paper model, but its source comment limits it to the fixed source endpoint. It cannot be used as a moving-scale theorem without a transport proof.

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

This must use the committed star-projection API and the two opposite scale laws. It may not assert the conclusion by unfolding a desired formula.

### T2 — doubled-shift Hankel/Sonin trace estimate

Prove a uniform or summable estimate for [starProjection(Rspace(b)), D] using the half-line Hankel pieces plus the Hardy transport represented by K_b.

Acceptable outputs are:

- an explicit nuclear-kernel estimate;
- two genuine Hilbert–Schmidt factors for every trace term;
- a signed cancellation estimate for the complete commutator/remainder.

The estimate must be independent of any qw sign, RH, healthy-detector proposition, or universal Weil positivity.

### T3 — repository-level trace witness

The project uses PositiveTrace.IsTraceClassAlong along a named basis. Unitary conjugation does not automatically preserve this predicate along the same arbitrary basis. The proof must either:

1. prove a basis-compatible transport lemma for the exact witness; or
2. construct an explicit transported BasisHilbertSchmidtPairData and prove its two square-summability fields in the target basis.

“Schatten class is invariant under unitaries” stated abstractly is not enough for the current Lean API.

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
    014-B  prove the closed-subspace pullback and T1
    014-C  derive the doubled-shift commutator identity
    014-D  prove the S1/nuclear or two-HS estimate
    014-E  build the IsTraceClassAlong/BasisHilbertSchmidtPairData witness
    014-F  identify the signed limit with the exact G8 ledger
    014-G  produce G8SameOwnerReadbackData and invoke the existing wrapper

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

Therefore this is a genuine RH-reaching subroute, but it is not yet a proof of RH and it is not even a complete R3 proof. The exact new bottleneck is now smaller and sharper: a doubled-shift Sonin intersection with a basis-compatible trace witness.
