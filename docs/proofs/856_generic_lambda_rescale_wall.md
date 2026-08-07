# 856 - Why generic-lambda prolate HS is not rescaling-reachable (source-verified) and why 855 neither fills the route sign slot

Date: 2026-08-08 . Status: source-verified structural verdict (no new build needed; each claim is a named repo def/theorem).

This round audited Gate-3U's single open premise (generic-lambda hfactor =
Summable ||sourceProlateHilbertSchmidtFactor lambda (basis i)||^2, per 844) with the
dilation/translation-conjugation rescue in hand, because the carrier is L2(R) in the LOG
coordinate and lambda only enters as t < log lambda.  The verdict: the rescue fails at
exactly one place, and it is real.  This sharpens 840/845.

    naive rescue : translate the lambda-carrier onto unit, then trade the lambda-HS from the
                   unit-HS theorem (unitSoninScale, 839 / UnitScaleProlateTraceReduction).
    actual fact  : the RADIAL piece IS log-translation covariant, the FOURIER/SONIN piece
                   is NOT, so the whole factor is not a fixed unitary conjugate of the unit one.

## 1. The radial piece IS log-translation covariant

ccm24LogRadialSupportClosedSubspace lambda = { u | forALL t, t < log lambda -> u t = 0 }
is the half-line of the log variable below log(lambda)
(Source/CC20Concrete/CCM24LogRadialSupport.lean:34-56).  cc20GlobalLogTranslation (-log lambda)
(t -> t - log lambda) is an isometric, invertible, additive operator on cc20GlobalLogCrossingL2
(Source/CC20Concrete/GlobalLogCrossing.lean:140), so it shifts the cutoff log lambda -> 0 = log 1,
mapping the lambda-radial-support subspace onto the unit one.  That half of the factor is reducible.

## 2. The Fourier/Sonin piece is NOT covariant, and it is the only obstruction

ccmArchimedeanFourierSupportClosedSubspace=lambda is the full pre-image of
ccmLogRadialSupportClosedSubspace(lambda) under the archimedean Hardy-Titchmarsh operator
(Source/CC20Concrete/CCM24HardyTitchmarsh.lean:355-366).  In the Fourier readback that operator
multiplies the transform by the scattering phase Gamma(1/2-2 pi i xi )/Gamma(1/2+...) after a
log-spectral reflection.  The Sonin space is the intersection of the radial and Fourier support
(CCM24HardyTitchmarsh.lean:376-382).

For the whole lambda operator to be a fixed-unitary conjugate of the unit one, the SAME
log-translation must also conjugate the Fourier/Sonin branch, i.e. it must intertwine the
Hardy-Titchmarsh scattering transform.  It does not: a log-coordinate translation t -> t - alpha
is a dilation x -> e^-alpha x in the original coordinate, and the archimedean scattering phase
is precisely NOT log-translation invariant (840.s scattering-phase non-invariance; 845 pinned
it at the non-mobile radial cutoff).  The Fourier/Sonin side needs the actual analytic
scattering, which has no dimensionless rescaling for arbitrary lambda.

  => The rescale-to-unit route is dead with the hardened 845 verdict: no structural
     conjugation/dilation/transport path exists from the unit-scale HS theorem to a generic-lambda
     gate.  The generic-lambda HS needs a genuine analytic family lambda -> ||remainder lambda||^2
     that no existing repo operator realizes.

## 3. 855 closes the CC20 TRACE-MODEL contract, NOT the finite-vanishing WEIL slot

855 (and 852-854) close CC20TraceModel: Gate -> trace-class, 0 <= positiveTrace = ||-||^2,
ordinary support-square, and the Mellin product law, all on the re-typed Hilbert log carrier.
That is real and verifier-checked CC20-trace-object satisfaction, but it is NOT the same slot as
the route-need WeilPositivityInput.fullWeilPositivity : Sort 1 (Basic.lean:421-429).

    CC20-trace contract :  0 <= positiveTrace = supportSquareTrace      (CLOSED by 854/855)
    finite-vanishing gate:  weilLocalSum (starConvolution g) <= 0        (refuted on additive model)

These are different functions.  855 supplies a non-negative diagonal trace of the carrier; the
finite-vanishing criterion needs a pole-pairing half-density weilLocalSum <= 0.  No >= 0 trace
statement fills that <= 0 Weil slot by itself.  So the 852-855 line removes the empty/True
producer for the trace contract but does NOT move the sign/Weil floor.

## 4. Honest bottom after 856

| item | state |
| generic-lambda prolate HS (only 3U premise) | OPEN; no translation/dilation/conjugation/transport bridge |
| 854/855 trace-model on Hilbert carrier      | CLOSED (axiom-clean) |
| fullWeilPositivity sign weilLocalSum(g*g) <= 0 | OPEN (separate; detector >0 proven, <=0 universal not) |
| per-F rows tripleVanishingMatchesMellin / finiteSetDisjoint | OPEN arithmetic (848) |
| RH | NOT proven |

No RH is claimed.  This is a ledger sharpening so a later session does not re-try the
rescaling-of-unit or the trace-closure-equals-sign-closure confusion.

## Repro (read only)

Source/CC20Concrete/CCM24LogRadialSupport.lean:34-56,104-,124   radial half-line + log-translation isometry
Source/CC20Concrete/GlobalLogCrossing.lean:140-160              cc20GlobalLogTranslation isometry/additive
Source/CC20Concrete/CCM24HardyTitchmarsh.lean:355-382           Fourier/Sonin subspaces; HT Fourier readback
Source/CCM25Concrete/CCM24UnitScaleProlateTraceReduction.lean:514-522 unit-only HS theorem
Source/CCM25Concrete/CCM24SourceProlateTrace.lean:33-40         factor = Q_lambda(E_lambda - R0_lambda)
Basic.lean:421-429                                             WeilPositivityInput.fullWeilPositivity : Sort 1
