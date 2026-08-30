# 1063 - F1 crux: exact operator model, numerical probe, and operational verdict

Date: 2026-08-30. Follows 1056 (F1 reclassification), 1059 (2b revoked, R1/R2
posture), 1062 (alpha convention corrections). Companion probes:
`docs/proofs/1063_f1_target_angle_probe.py` (raw angle sums),
`docs/proofs/1063b_f1_weighted_probe.py` (detector-weighted candidate F1').
The original raw-F1 `sorry` has since been removed from the Dev leaf.  The
leaf now carries F1' as an explicit analytic contract and contains a proven
active-order algebraic reduction; no analytic trace-class proof is claimed
here.

Question put by Peter: is the semilocal crux F1 attackable ("打通") or
provably-not ("确定打不了")? This record answers it for the RAW statement and
opens the numerics for the weighted restatement.

## 0. Operational verdict up front

```text
(1) RAW F1 IS REJECTED AS A PROOF TARGET, NOT FORMALLY NEGATED.
    The finite-grid angle statistic grows with its frequency window over
    xi_max = 12.8 -> 102.4 for every tested nonempty family, while the source
    anchor stays O(1).  The strongest resolution check is {2,3,5} at xi_max
    51.2: 20.8779 versus 20.8784 after quartering dt (0.003%).  This is strong
    evidence against pursuing the raw theorem, but it is not a Lean theorem
    that the continuum operator is non-compact or non-trace-class.

(2) THE PHASE-TWIST EXPLANATION IS A MODEL-LEVEL HYPOTHESIS.
    The derived transported phase m_S = m * mu_S / conj(mu_S) explains the
    observed persistent nonmeet band.  No essential-spectrum theorem, no
    principal-angle-to-Lean-trace equivalence, and no formal negation of raw
    F1 has been proved from it.

(3) F1' IS A CANDIDATE, NOT A CLOSED BRICK.
    The weighted finite-dimensional statistics plateau for the tested Gaussian
    multipliers.  They motivate smoothing, but they do not prove
    `IsTraceClassAlong basis (D oL K_S)`: that Lean predicate is a summability
    statement for a named basis (PositiveTrace.lean:32-39), while D oL K_S is
    generally non-self-adjoint.  In particular, finite-dimensional trace
    cyclicity may not be imported into the named-basis continuum series.

(4) THE PROVEN NEW ALGEBRAIC ENTRY USES THE ACTIVE OPERATOR ORDER.
    With K_S = A† A and D = C† C, the Dev leaf now proves
      D K_S = C† K_S C + C† [C, K_S]
            = (A C)† (A C) + C† [C, K_S].
    Thus no cyclic trace readback is assumed: S1 is the honest positive
    active-order sandwich, while S2 is the explicit root-commutator remainder.
    A second Lean theorem expands S2 into its concrete signed four-branch
    `E/Q_S/R_S` ledger.
```

## 1. Historical raw F1 and the finite-grid model

The removed raw theorem was (unit scale lambda = 1, any global basis):

```lean
theorem targetProlateRemainder_unit_isTraceClassAlong
    (family : FinitePrimePowerFamily) {ι} (basis : HilbertBasis ι ℂ finiteSCarrier) :
    IsTraceClassAlong basis (targetProlateRemainder unitSoninScale family) := by sorry
```

Pinned definitions (Lean file:line):

```text
H    = cc20GlobalLogCrossingL2 = L2(R, Lebesgue dt)        GlobalLogHaar.lean:30
E    = radialSupportProjection unitSoninScale
     = multiplication by chi_{t >= log 1} = chi_{t >= 0}   CCM24LogRadialSupport.lean:67-69
HT   = f^{-1} . M_m . R . f,  m(xi) = GR(1/2-2pi i xi)/conj(...)   CCM24HardyTitchmarsh.lean:43-45, 331-365
     (unitary, self-adjoint, involutive; Q_0 = HT E HT)    CCM24HardyTitchmarsh.lean:349-373
T_S  = prod_p (1 - p^{-1/2} Shift_{-log p})                CCM24EulerTransport.lean:182-206
HT_S = T_S.trans HT ...; Q_S = HT_S E HT_S                 CCM24SemilocalFourierSupport.lean:31-83
R_S  = E wedge Q_S (Gram-corrected meet)                   CCM24FiniteSProjectionTrace.lean:145
K_S  = E Q_S E - R_S >= 0                                  CCM24FiniteSProjectionTrace.lean:161-166
K_S = A^* A,  A = Q_S E (E - R_S)                          Dev leaf:76-107
```

The probe represents the nonmeet spectrum of the discretized `E Q_S E` by
principal-angle mass.  That is a useful diagnostic model of raw F1, not a Lean
lemma identifying its finite-grid sum with
`IsTraceClassAlong basis K_S`.  The latter is defined as a named-basis complex
diagonal series in `PositiveTrace.lean:32-39`.

KEY DERIVATION (not yet a Lean lemma; the probe stands or falls with it):
since every shift becomes a frequency multiplier, f T_S f^{-1} = M_{mu_S} with
mu_S(xi) = prod_p (1 - c_p e^{-2 pi i xi log p}), so

```text
HT_S = f^{-1} M_{mu_S} M_m R M_{mu_S}^{-1} f
     = f^{-1} M_{m mu_S(xi)/mu_S(-xi)} R f        (mu_S(-xi) = conj mu_S(xi))
     = f^{-1} M_{m_S} R f,   m_S = m . mu_S / conj(mu_S).
```

Because |m_S| = 1 and m_S(-xi) = conj m_S(xi), the intended continuum model
makes HT_S a self-adjoint unitary involution.  The probe checks the corresponding
finite matrices: HT^2 - I and HT - HT^* are below 3e-12 and phase reflection
symmetry is below the stated gate.  Those are implementation gates, not a
formal continuum proof.

Quantifier note (1059 lesson): F1 is per-family (`family.terms : Finset`), so
no uniformity across families is required - and the probe shows it fails even
per-family, so this rescue does not apply.

## 2. Why the raw statistic grows (unproved analytic mechanism)

The two projections are (chi_{t>=0}, HT_S chi_{t>=0} HT_S). Conjugating by f,
E becomes the Hardy space H2_+ and HT_S becomes multiplication by the phase
e^{2 i arg m_S( xi)} followed by the reflection R.  It is plausible that a
non-decaying almost-periodic phase twist produces the observed persistent
finite-grid angle band.  Turning this into an essential-spectrum statement
would require a separate theorem about the relevant truncated Fourier/Hankel
operator; no such theorem is present in this repository.

The transported phase adds 2 arg mu_S(xi), a quasi-periodic function with
spectrum in the lattice Z-span{log p : p in S}.  The probe sees new nonmeet
eigenvalues in the same finite-grid magnitude band as the window grows.  This
is evidence consistent with a non-decaying tail; it is not a Weyl law and does
not establish that K_S is non-compact in Lean's continuum model.

## 3. The probe and its gates (AGENTS 7c discipline)

Script: `docs/proofs/1063_f1_target_angle_probe.py` (deterministic; run in a
Linux-side scientific environment and keep generated logs outside the repo).

```text
Grids:      N x T with ODD N (even N drops Nyquist, breaks m(-xi)=conj m(xi),
            destroys the involution - observed 8e-1 gate failure vs 3e-12).
            (1025,20) (2049,20) (4097,20) (2049,40) (4097,40) and 8193 pair.
Phase:      scipy loggamma anchored against mpmath dps-50 at xi=0.25,1,4
            (max diff 4.6e-15).
Gates:      HT^2 = I < 1e-8; HT self-adjoint < 1e-8; phase reflection
            symmetry < 1e-10; positivity lambda_min(M_S) > -1e-6 (hard stop).
Anchor:     S={} must reproduce the proven source summability -> it does.
Split:      meet = first gap > 0.02 block; banded sums threshold-robust.
```

Decision table, finite-grid nonmeet statistic (the recorded `SUMMARY` lines):

```text
+----------+---------+---------+---------+---------+---------+
| S        | 12.8    | 12.8    | 25.6    | 51.2    | 102.4   |
|          | N1025   | N2049   | N2049   | N4097   | N8193   |
|          | /T20    | /T40    | /T20    | /T20    | /T20    |
+----------+---------+---------+---------+---------+---------+
| src {}   |  3.179  |  3.247  |  3.433  |  3.121  |  2.474  | FLAT [anchor PASSES]
| {2}      |  4.070  |  4.079  |  5.157  |  6.829  |  7.399  | growth ~xi_max^0.27-0.4
| {2,3}    |  7.777  |  7.883  | 11.339  | 13.212  | 16.831  | growth ~xi_max^0.4-0.5
| {2,3,5}  | 10.212  | 10.284  | 15.177  | 20.878  | 28.275  | growth ~xi_max^0.4
+----------+---------+---------+---------+---------+---------+
per-octave ratios {2,3,5}: 1.49 / 1.38 / 1.35 - no bend toward saturation at
4 octaves; top nonmeet angle 0.378/0.412/0.391/0.735 - PINNED away from 0,
which is evidence against a decaying raw tail in this discretization.

dt-invariance pairs (same xi_max, finer dt):
  12.8:  1025/T20 vs 2049/T40 (halve):      src 3.179/3.247  {2,3,5} 10.212/10.284
  25.6:  2049/T20 vs 4097/T40 (halve):      src 3.433/3.517  {2,3,5} 15.177/15.191
  51.2:  4097/T20 vs 8193/T40 (QUARTER):    src 3.121/3.150  {2,3,5} 20.8779/20.8784
                                            {2} 6.829/6.842  {2,3} 13.212/13.182
The 51.2 pair quarters dt with 0.003% agreement: within this model, the
observed growth follows the frequency window rather than this grid refinement.

meet block: src 42/117/303/746 (Landau-type growth) - the Sonin intersection
IS infinite-dimensional: the 1055 lambda~1 block, now measured at unit scale.
```

## 4. What this does and does not prove

```text
IT DOES: provide a high-quality operational guard against spending proof effort
    on raw F1.  The source-side anchor, resolution sweep, interval sweep, and
    algebraic finite-matrix gates all pass.  Under the project's pre-flight
    rule, raw F1 is retired as the next analytic target.
IT DOES NOT: prove a continuum negation, identify the principal-angle statistic
    with Lean's named-basis `IsTraceClassAlong`, establish an essential spectrum,
    or prove any detector-weighted trace theorem.  The continuum operator and
    the required trace rearrangements remain analytic work.
IT ALSO DOES NOT: touch 1055's freeze, the 2b revocation, or alpha/beta/gamma/
    delta (GATE 1 mainline is unaffected; this is the C1 Dev-leaf thread).
```

## 5. The candidate repair: active-order smoothing plus a root commutator

The current consumer still asks for the explicit F1' contract

```lean
IsTraceClassAlong globalBasis
  (detectorOperator owner ∘L targetProlateRemainder unitSoninScale family)
```

but the probe does not prove that proposition.  In particular,
`detectorOperator owner = C† C` and `K_S = A† A`, so the requested operator
is `C† C A† A`: it is generally non-self-adjoint.  The finite-grid value
obtained by weighting eigenvectors of a discretized positive overlap is a
useful diagnostic, not a proof of the named-basis diagonal series above.

The recorded four-octave finite-grid statistics are nevertheless informative:

```text
WEIGHTED, S={2,3,5}      xi=12.8   xi=25.6   xi=51.2   xi=102.4
  k=0.3                    4.376     4.396     4.405     4.410
  k=1.0                    1.4020    1.4058    1.4077    1.4085
  k=3.0                    0.5340    0.5353    0.5359    0.5362
```

They support the hypothesis that high-frequency smoothing is relevant.  They
do not establish convergence for every owner, because the observed exponent
and the bridge from the finite-grid angle statistic to the continuum kernel
are both still unproved.

The honest active-order reduction is:

```text
D K_S = C† K_S C + C† [C, K_S]
      = (A C)† (A C) + C† [C, K_S].
```

Both identities are Lean-proved in
`C1ProlateResponseTraceLegalityUnitScale.lean` as
`targetProlateDetectorRightSmoothingFactor_adjoint_comp_self` and
`detectorTargetProlate_eq_rightSandwich_add_rootCommutator`.  The next two
obligations are now separate, exact, and in the same operator order as the
consumer:

```text
S1. Prove Summable_i ||(A C)(globalBasis i)||².
    This gives trace legality of C† K_S C = (A C)† (A C) through a genuine
    two-Hilbert--Schmidt owner.

S2. Prove trace legality of C† [C, K_S].  The proved four-branch identity is
    C† [C, K_S]
      = -C†( E Q_S [E,C] + E [Q_S,C] E + [E,C] Q_S E - [R_S,C] ).
    The signed second-support/Sonin part may require a coupled estimate; it
    must not be replaced by an unlicensed cyclic trace step.
```

The existing `CCM24RadialBoundaryPairTransport` proves a detector-level
half-line commutator for `D = C† C`; it does not prove any root-level term in
S2.  Connes--Consani Lemma D.1 proves that its specific quantized differential
`[H,f]` is trace class for Schwartz `f`; it supports the *shape* of a
half-line/Schwartz commutator argument, but is not a producer for the finite-S
Fourier or Sonin branches above.  Source: Connes--Consani, Lemma D.1,
arXiv:2006.13771, https://arxiv.org/abs/2006.13771.

## 6. Consequences for the Dev leaf and the thread

```text
DECIDED:
- The raw theorem `targetProlateRemainder_unit_isTraceClassAlong` and its
  false-looking reduction have been removed.  The numerical guard retires it
  as a proof target; this is not a formal theorem of negation.
- `targetProlateRemainderDetectorWeightedTraceLegality` is now an explicit
  F1' PROP contract consumed by the response.  It has no producer yet.
- The leaf now proves the active-order reduction
    D K_S = (A C)† (A C) + C† [C, K_S]
  and the exact four-branch expansion of its commutator remainder.  This is
  valid algebra in the requested operator order; it does not supply either
  analytic trace-class producer.
- NEXT ANALYTIC TARGETS:
    (S1) produce the named summability of A C;
    (S2) build a legal pair owner for the signed root-commutator ledger.
  Both targets must be established in Lean or reduced to explicit analytic
  contracts.  Neither may be discharged by the 1063 finite-grid data.
- If S1 or S2 fails, the honest fallback is still the compression side only:
  F2 remains an independent target, while the prolate side stays conditional
  with no false raw premise.
```

## 5b. Superseded hypotheses of this session

```text
S1-old (collapse: R_S = {0} by a Privalov-type argument): the growing
   finite-grid meet block argues against this route, but is not a formal
   refutation of the continuum claim.
S3 (D-smoothing absorbs everything, so the raw statement was moot): PARTLY
   ruled out as a bypass: D does not commute with the meet, and smoothing has
   not yet produced a legal readback to the original response.
2b (perturbation of the source through the transport): already REVOKED by
   1059; nothing here resurrects it.
```

## 7. Sources

```text
ConnesWeilRH/Dev/C1ProlateResponseTraceLegalityUnitScale.lean
ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSProjectionTrace.lean:145-220
ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSBandTrace.lean:35-47
ConnesWeilRH/Source/CCM25Concrete/CCM24RadialBoundaryPairTransport.lean:470-850
ConnesWeilRH/Source/CC20Concrete/PositiveTrace.lean:32-39, 270-287, 520-575
ConnesWeilRH/Source/CC20Concrete/ThreeBranchCommutatorLedger.lean:27-71
ConnesWeilRH/Source/CC20Concrete/CCM24HardyTitchmarsh.lean:43-126, 331-380
ConnesWeilRH/Source/CC20Concrete/CCM24SemilocalFourierSupport.lean:31-83
ConnesWeilRH/Source/CC20Concrete/CCM24EulerTransport.lean:182-206
ConnesWeilRH/Source/CC20Concrete/GlobalConvolutionCrossing.lean:22-25
ConnesWeilRH/Source/CC20Concrete/GlobalLogHaar.lean:30
docs/proofs/1063_f1_target_angle_probe.py, 1063b_f1_weighted_probe.py
Connes--Consani, "Weil positivity and Trace formula, the archimedean place",
  Lemma D.1, arXiv:2006.13771, https://arxiv.org/abs/2006.13771
Generated probe logs are intentionally unversioned in the Linux-side
verification environment.
docs/proofs/1056, 1059 (posture), 1055 (freeze; the lambda~1 block = our meet)
```
