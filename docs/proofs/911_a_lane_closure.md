# 911 — A-lane closure: unit-lambda is CLOSED, the generic-lambda gate is the only wall

Date: 2026-08-09. Status: reconciliation verdict (no new build; each claim is a named
repo theorem + the 910 numeric output already committed b5c0860).

This doc honestly closes the A-lane (generic-lambda prolate spectral-sum) after probe 910's
numeric "negative". The reconciliation is neither "910 is a pure artifact" nor "the A-lane
is dead". It is the precise two-part truth:

    (i) the UNIT-lambda instance is ALREADY closed, axiom-clean (868 / CCM24UnitScaleStrictAngle);
    (ii) the ONLY remaining A-lane gate is the GENERIC-lambda prolate HS summability, and
         910 shows the finite-grid route will never witness it: the grid operator is close
         to `E Q E`, which is not a decaying family for the scatter-phase Q.

## The operator 910 measures (unit-lambda, log lambda = 0)

    R     = radial log-support proj = diag over t >= 0            (E)
    Q     = arch Fourier-support proj = orth-proj onto range(H-dag E)   (H = HT, scattering phase)
    R0    = Sonin proj = orth-proj onto range(R) cap range(Q)
    B     = band = R - R0
    remain = B Q B                          (= factor-dag * factor)
    A     = j-dag Q j , j = band inclusion   (band-Fourier compression)

The Lean probe `ELambdaFactorSplitProbe.lean` (commits 8a79c1d + 70a5933, axiom-clean)
proved, for every `CCM24SoninScale lambda`:

    factor_lambda = Q_lambda circ B_lambda                       factor_eq_band_comp
    ||factor_lambda|| <= 1                                    factor_norm_le_one
    remainder_lambda = B_lambda Q_lambda B_lambda              remainder_eq_band_comp_band
    j-dag (B Q B) j = j-dag Q j                               step1 band_compression_eq
    A = j-dag Q j  is self-adjoint                      step2 band_FourierCompression_selfAdjoint

and the generic-lambda `Summable` gate reduces exactly to "A is trace-class along range B"
(for self-adjoint A : `sum_i sigma_i(A)` summable).

## 910's numeric result (committed b5c0860)

    n       rank(B)  rank(Q)  dim(RnQ)  tail-sum sum sigma(A)   leading 8
    192       96       96        0          61.0                1 1 1 1 1 1 1 1
    384       --       --        0         149.9                --
    768       --       --        0         287.2                --
    1536      --       --        0         473.4                --

Three signals, all consistent:

    * tail-sum = sum_i sigma_i(A)  grows LINEARLY in n   (61 -> 474 as n: 192 -> 1536);
    * the top 8 eigenvalues are ALL EXACTLY 1, with multiplicity growing ~linearly in n;
    * dim(R cap Q) = 0 on EVERY grid -> R0 ~ 0 -> B = R - R0 ~ R.

## Reconciliation: this is the SAME discretization collapse as 837/838, not a statement about the operator

838 established that finite-grid `dim(R cap Q) = 0` is a LATTICE fact, not an operator fact:
on a finite cyclic grid the radial-support `range(R_n)` and the discrete-Fourier-support
`range(Q)` miss each other, so the Sonin intersection `R0` collapses to 0. 910 reproduces
that: `dim(R n Q) = 0` on every grid -> R0 = 0 -> finite band B = R.

With R0 = 0 the finite remainder collapses:

    remainder = B Q B  ~  (since B ~ R)   R Q R   (a corner of R, not Q R Q).

For the scattering `Q = H-dag E H` this corner `R Q R` is NOT a time-band localization pair
of the Slepian / Landau-Pollack kind (that decaying family needs both projectors
log-translation-covariant). Because the archimedean scatter-phase H is NOT log-translation
invariant (840, 845, 856), the pair (R, Q) is not a translate of a translation-invariant
energy/app pair. So the finite operator has NO provable exponential spectral decay, and the
tail-sum is not bounded: hence the linear tail of 910.

=> 910's negative is a RE-PROJECTION, on grids, of the fact that this (R, Q) pair is not a
translation-invariant localization pair. It does NOT contradict the continuum unit-lambda
statement below.

## The continuum unit-lambda HS IS CLOSED (868)

`CCM24UnitScaleStrictAngle.lean` (lines 1483-1522), axiom-clean
`[propext, Classical.choice, Quot.sound]`, no sorry:

    norm_unitProlateFactor_lt_one
    sourceProlateRemainder_unit_isTraceClassAlong
    sourceProlateHilbertSchmidtFactor_unit_summable      (unit hfactor CLOSED)
    sourceThreeBranchCommutator_unit_isTraceClassAlong

the continuum `H = cc20GlobalLogCrossingL2` HAS the Sonin closed subspace non-empty,
||unitProlateFactor|| < 1 strict, and the remainder trace-class. So the UNIT-lambda
Summable/TraceClassAlong lane is DONE at the source level on the continuum carrier, even
though a finite grid fails to see it (838, 911).

## The honest A-lane gate after 909

The entire A-lane reduces to ONE query:

    Summable i, ||sourceProlateHilbertSchmidtFactor lambda (globalBasis i)||^2 ?   (generic hfactor)

    * unit-lambda instance : CLOSED (868).
    * generic-lambda instance : OPEN, pinned at the scatter-phase break (856/840/845), not a placeholder.

910 contributes the sharp negative: on ANY finite grid the compression A is close to
`R Q R ~ E Q` (R0 = 0), whose Q is not a time-band localization, so no grid decay of A is
observable and the tail is not summable on the grid set. That says the generic-lambda sum
(over the infinite band carrier) cannot be witnessed through the finite-grid eigenvalue
tail; the honest door is infinite-dimensional spectral decay over the classical
prolate-spheroidal eigenbasis inside `range B`, not a finite-grid matrix.

    | item                                            | state |
    | unit-lambda hfactor (868)                       | CLOSED, axiom-clean |
    | factor=Q circ B, ||factor||<=1, remainder=B Q B | CLOSED (910 Lean)   |
    | band_compression_eq, A self-adjoint             | CLOSED (910 Lean)   |
    | 910 grid decay                                  | tail ~ linear (838 collapse) |
    | generic-lambda hfactor                          | OPEN (the only A-lane wall) |
    | RH                                             |  NOT proven |

## Verdict

The A-lane is now fully decomposed into exactly one wall that is an honest analytic
question (generic-lambda `hfactor`), and this doc records why grid probes (esp. 910)
cannot decide it: the finite operator is not in any provably-decaying translation family.
The door that remains is either (a) true lambda-analysis / a spectral-family bound for
`B_lambda Q_lambda B_lambda` on the infinite band carrier (the lambda-monotone family work
850/851 keeps pointing at, but which needs projected eigen-structure, not just subspace
inclusion), or (b) turn to the B-lane: construct the finite-vanishing `FullWeilPositivity`
witness (849: that is the actionable open). Next doc: 912-B.

No RH is claimed and this doc introduces no new axiom/sorry.