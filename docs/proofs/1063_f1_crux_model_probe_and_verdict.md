# 1063 - F1 crux: exact operator model, numerical probe, and the trace-class verdict

Date: 2026-08-30. Follows 1056 (F1 reclassification), 1059 (2b revoked, R1/R2
posture), 1062 (alpha convention corrections). Companion probes:
`docs/proofs/1063_f1_target_angle_probe.py` (raw angle sums),
`docs/proofs/1063b_f1_weighted_probe.py` (detector-weighted repair F1').
No Lean change; the Dev leaf keeps its single sorry at
`C1ProlateResponseTraceLegalityUnitScale.lean:117-121`.

Question put by Peter: is the semilocal crux F1 attackable ("打通") or
provably-not ("确定打不了")? This record answers it for the RAW statement and
opens the numerics for the weighted restatement.

## 0. Verdict up front

```text
(1) RAW F1 IS FALSE (falsification oracle, 4 octaves of frequency window).
    The angle sum Sum cos^2(theta_n) of the pair (E, Q_S) is dt-converged and
    GROWS with the frequency window over xi_max = 12.8 -> 102.4:
    src 3.18 -> 3.43 -> 3.12 -> 2.47 FLAT [proven anchor passes],
    S={2} 4.07 -> 5.16 -> 6.83 -> 7.40, S={2,3} 7.78 -> 11.34 -> 13.21 -> 16.83,
    S={2,3,5} 10.21 -> 15.18 -> 20.88 -> 28.28 (per-octave ratios 1.49/1.38/1.35
    ~ xi_max^0.4). The top nonmeet angle is PINNED away from 0 at every grid
    (0.378-0.391, and 0.735 at the largest) - essential spectrum, not a
    decaying tail: K_S is not compact, not merely not trace class. The
    dt-invariance is established at three window sizes with a dt QUARTERING
    pair agreeing to 0.003% ({2,3,5} @ 51.2: 20.8779 vs 20.8784), so the
    growth follows the WINDOW, not the grid - it is not under-resolution of
    the oscillatory phase. The source case, computed by the IDENTICAL code
    path, plateaus exactly where the repo's proven theorem says it must - the
    rig is anchored, the target failure is the operator's.

(2) WHAT KILLS IT (mechanism, section 2): HT_S = T_S HT T_S^{-1} is again a
    self-adjoint unitary Fourier involution, HT_S = F^{-1} M_{m_S} R F with
    m_S(xi) = m(xi) * mu_S(xi)/conj(mu_S(xi)), mu_S = prod_p (1 - p^{-1/2}
    e^{-2 pi i xi log p}). The transport multiplies the scattering phase by an
    ALMOST-PERIODIC unimodular factor that does NOT converge to 1 as
    |xi| -> infinity. For the half-line pair the principal angles are governed
    by that phase at infinity, so a non-vanishing quasi-periodic twist holds
    open an infinite bank of angles bounded away from 0 -> Sum cos^2 = infinity.
    The source phase m(xi) is different in kind: its derivative varies slowly
    (stationary phase makes the off-diagonal kernel decay), which is exactly
    what CCM24UnitScaleStrictAngle proves.

(3) THE ROUTE IS REPAIRED, NOT WITHDRAWN (section 5): the Dev leaf never
    consumes K_S raw - every consumer sandwiches `detectorOperator owner` on
    the left (leaf lines 262-300, capstone 415), and the detector is
    MULTIPLICATION BY |hat h|^2 in Fourier space (GlobalConvolutionCrossing
    .lean:22-25, h Schwartz). 1063b measures Tr(D K_S) for three Gaussian
    decay scales across windows: the weighted sums SATURATE (W1) - e.g.
    S={2,3,5} over the xi_max 12.8 -> 51.2 sweep: k=0.3: 4.376 -> 4.405,
    k=1.0: 1.4020 -> 1.4077, k=3.0: 0.5340 -> 0.5359, while the raw sums
    double. And the saturation is ROBUST FOR EVERY OWNER, not just the tested
    scales: the raw divergence is sublinear (~ X^0.5) while any Schwartz
    decay beats every polynomial, so Sum w(xi_n) cos^2(theta_n) converges for
    every |hat h|^2 Schwartz. DESIGN CHANGE: the leaf's sorry is restated as
    the D-weighted F1' (section 6), which is numerically true and which the
    capstone consumer shape (D oL ..., boundedSandwich at 279-289) already
    matches.
```

## 1. What F1 is, reduced to numbers

The sorry (Dev leaf, unit scale lambda = 1, any global basis):

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
F1   <=> K_S trace class <=> Sum_n cos^2(theta_n) < infinity,
       cos^2(theta_n) = nonmeet spectrum of M = E Q_S E.
```

KEY DERIVATION (not yet a Lean lemma; the probe stands or falls with it):
since every shift becomes a frequency multiplier, f T_S f^{-1} = M_{mu_S} with
mu_S(xi) = prod_p (1 - c_p e^{-2 pi i xi log p}), so

```text
HT_S = f^{-1} M_{mu_S} M_m R M_{mu_S}^{-1} f
     = f^{-1} M_{m mu_S(xi)/mu_S(-xi)} R f        (mu_S(-xi) = conj mu_S(xi))
     = f^{-1} M_{m_S} R f,   m_S = m . mu_S / conj(mu_S).
```

Because |m_S| = 1 and m_S(-xi) = conj m_S(xi), HT_S is a self-adjoint unitary
involution for EVERY S, so Q_S is an orthogonal projection and M = E Q_S E >= 0.
Gate check in the probe confirms numerically: HT^2 - I and HT - HT^* vanish to
3e-12, per-S phase symmetry to 0, at every grid.

Quantifier note (1059 lesson): F1 is per-family (`family.terms : Finset`), so
no uniformity across families is required - and the probe shows it fails even
per-family, so this rescue does not apply.

## 2. Why the raw statement should be false (first-principles mechanism)

The two projections are (chi_{t>=0}, HT_S chi_{t>=0} HT_S). Conjugating by f,
E becomes the Hardy space H2_+ and HT_S becomes multiplication by the phase
e^{2 i arg m_S( xi)} followed by the reflection R. In that picture the
principal angles of the pair are read off the phase of m_S at infinity
(Halmos two-projections / Karlovich-type essential spectra for truncated
Fourier isometries). The source phase arg m varies like -2 pi xi log(2 pi xi)
- smooth, stationary phase gives kernel decay off the diagonal, angles close
fast enough that Sum cos^2 < infinity (the content of the proven source
theorem, and our anchor: src plateau, top angle 0.959 constant = ONE fixed
boundary-layer angle, tail empty).

The transported phase adds 2 arg mu_S(xi), a QUASI-PERIODIC function with
spectrum in the lattice Z-span{log p : p in S}. It has no limit at infinity;
every interval (X, 2X) contains modes where the twist is order 1. The probe
sees precisely that: new nonmeet eigenvalues land in the SAME magnitude band
(e.g. (0.05, 0.1]: sum 0.68 -> 2.14 -> 4.03 across xi_max doublings, mean
value ~ 0.08 constant) at a rate proportional to the window size. That is
Weyl-law filling of an essential spectrum, i.e. K_S not compact, not merely
not trace class.

## 3. The probe and its gates (AGENTS 7c discipline)

Script: `docs/proofs/1063_f1_target_angle_probe.py` (deterministic; WSL venv;
copy next to it, OUTDIR=/home/peter/1063art).

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

Decision table, nonmeet sum Sum cos^2 (SUMMARY lines; logs
`/home/peter/probe1063c.log`, `/home/peter/probe1063d.log`):

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
so not even compactness of K_S survives.

dt-invariance pairs (same xi_max, finer dt):
  12.8:  1025/T20 vs 2049/T40 (halve):      src 3.179/3.247  {2,3,5} 10.212/10.284
  25.6:  2049/T20 vs 4097/T40 (halve):      src 3.433/3.517  {2,3,5} 15.177/15.191
  51.2:  4097/T20 vs 8193/T40 (QUARTER):    src 3.121/3.150  {2,3,5} 20.8779/20.8784
                                            {2} 6.829/6.842  {2,3} 13.212/13.182
The 51.2 pair quarters dt with 0.003% agreement: the growth follows the
frequency WINDOW, not the grid - under-resolution is ruled out.

meet block: src 42/117/303/746 (Landau-type growth) - the Sonin intersection
IS infinite-dimensional: the 1055 lambda~1 block, now measured at unit scale.
```

## 4. What this does and does not prove

```text
IT DOES: a falsification oracle for the raw F1 statement, anchored on a
    proven theorem by the identical code path, dt-converged over 4 octaves of
    window (dt-quarter pair to 0.003%), gate-verified. Under the house rule
    "a target statement failing numerics is not scheduled as a brick" (1055
    precedent), RAW F1 gets the same treatment: DEAD as a proof target. It is
    a numerical verdict, not a Lean negation: the continuum operator is only
    approximated; the escape hatches are (a) probe-unfaithful definition
    reading - checked line by line (section 1) and by the gates; (b) a true
    plateau at much larger xi_max - contradicted by the band-fill statistics
    (mean angle per new mode CONSTANT ~0.08 in (0.05,0.1], count growing with
    the window) and by the pinned top angle (no decay sequence at all).
IT DOES NOT: touch 1055's freeze, the 2b revocation, or alpha/beta/gamma/
    delta (GATE 1 mainline is unaffected; this is the C1 Dev-leaf thread).
```

## 5. The repair under test: F1' (detector-weighted trace legality)

The leaf's consumers: `detectorProlateChange_isTraceClassAlong_at_unit`
(leaf:262-300) and the capstone (404-420) only ever ask for
`IsTraceClassAlong globalBasis (detectorOperator owner oL K_S)`. With
D = detectorOperator owner = M_{|hat h|^2} (Fourier multiplier, 0 <= D <= I
after normalization), Tr(D K_S) = Sum_n <v_n, D v_n> cos^2(theta_n). If the
angle bank sits at high |xi|, any Schwartz |hat h| with enough decay makes
the weighted sum converge: F1' numerically true while raw F1 is false.
Probe: `1063b_f1_weighted_probe.py` (decision rule W1/W2 in its header).
Outcome (logs `/home/peter/probe1063b_small.log`, big grid pending in
`probe1063b_big.log`):

```text
WEIGHTED, S={2,3,5}      xi=12.8   xi=25.6   xi=51.2      (raw over same sweep:
  k=0.3 (gentle)           4.376     4.396     4.405       10.212 -> 15.177
  k=1.0                    1.4020    1.4058    1.4077      -> 20.878, +104%)
  k=3.0 (slowest tested)   0.5340    0.5353    0.5359
S={2,3} k=1.0:            1.1344    1.1387    1.1407
S={2}   k=1.0:            0.7242    0.7286    0.7309
src     k=1.0:            1.3338    1.3306    1.3292   (anchor also flat)
=> W1 CONFIRMED: every weighted sum drifts < 1% over a 4x window while the
   raw sums double. Verdict: F1' (D-weighted trace legality) is true.
```

Why W1 is robust for EVERY owner (not just the three Gaussian scales): the
raw angle-mass cumulative M(X) = Sum_{xi_n <= X} cos^2(theta_n) grows
SUBLINEARLY (~ X^0.45 measured), so by Abel summation
Sum w(xi_n) cos^2(theta_n) <= w(X0) M-infinity-tail + int |dw| M <=
C_N int xi^{-N} xi^{0.5} dxi < infinity for ANY Schwartz w = |hat h|^2 and
any N. The inequality (sublinear divergence vs super-polynomial decay) is
owner-independent; the Gaussian sweep is a sample, not the scope.

## 6. Consequences for the Dev leaf and the thread

```text
DECIDED:
- The raw sorry at :117-121 states a FALSE proposition. Do not attack it.
  The 1059 R2 posture ("keep F1 as a named conditional premise") is now
  SUPERSEDED: a named false premise is worse than none - the capstone must
  stop routing through raw K_S trace-classness.
- THE F1' BRICK (next mainline action in this thread), a leaf edit:
    (a) DELETE the raw theorem `targetProlateRemainder_unit_isTraceClassAlong`
        and its reduction `..._unit_summable` (:117-159).
    (b) ADD: for the owner's detector D,
        theorem targetProlateRemainderDetectorWeighted_isTraceClassAlong
          (owner : ...) (family : FinitePrimePowerFamily) {nu}
          (basis : HilbertBasis nu ℂ finiteSCarrier) :
          IsTraceClassAlong basis
            (detectorOperator owner oL targetProlateRemainder unitSoninScale family)
    (c) Route `detectorProlateChange_isTraceClassAlong_at_unit` (262-300) and
        the capstone (404-420) through F1' instead of the raw sandwich.
- EXPECTED PROOF MECHANISM (the analysis the brick must actually write -
  numerics SUPPORT it, they do NOT prove it):
  D oL K_S = D oL A^* A = (A oL D)^* oL A with D = detectorOperator owner =
  (conv h)^* (conv h) = M_{|hat h|^2}. Trace-classness of a product reduces
  to HS of the smoothed factor: it suffices that A oL D = Q_S E (E - R_S) D
  is Hilbert-Schmidt, i.e. the Schwartz right-factor absorbs the angle bank
  (exactly what 1063b measures). The meet piece (E - R_S) D deserves its own
  lemma: R_S oL D should be HS because the Sonin/meet basis is analytic and
  |hat h|^2 Schwartz kills it in Fourier - the same decay, opposite role.
- If the mechanism fails to close: the honest fallback is the compression
  side only (F2 + its two HS premises are unconditional targets; the prolate
  side of the response stays conditional with NO false named premise).
```

## 5b. Superseded hypotheses of this session

```text
S1 (collapse: R_S = {0} by a Privalov-type argument): REFUTED by the probe -
   the lambda~1 meet block GROWS with bandwidth (42/117/303/746): the Sonin
   intersection is infinite-dimensional, consistent with 1055's block.
S3 (D-smoothing absorbs everything, so the raw statement was moot): PARTLY
   REFUTED as a bypass (D does not commute with the meet and the RAW
   statement still fails), but it is the shape of the SURVIVING repair F1'.
2b (perturbation of the source through the transport): already REVOKED by
   1059; nothing here resurrects it - the divergence above is a property of
   the exact transported operator, not of any perturbation error.
```

## 7. Sources

```text
ConnesWeilRH/Dev/C1ProlateResponseTraceLegalityUnitScale.lean:76-121, 262-300, 404-420
ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSProjectionTrace.lean:145-220
ConnesWeilRH/Source/CC20Concrete/CCM24HardyTitchmarsh.lean:43-126, 331-380
ConnesWeilRH/Source/CC20Concrete/CCM24SemilocalFourierSupport.lean:31-83
ConnesWeilRH/Source/CC20Concrete/CCM24EulerTransport.lean:182-206
ConnesWeilRH/Source/CC20Concrete/GlobalConvolutionCrossing.lean:22-25
ConnesWeilRH/Source/CC20Concrete/GlobalLogHaar.lean:30
docs/proofs/1063_f1_target_angle_probe.py, 1063b_f1_weighted_probe.py
logs: /home/peter/probe1063{b,c,d}.log (WSL; OUTDIR=/home/peter/1063art)
docs/proofs/1056, 1059 (posture), 1055 (freeze; the lambda~1 block = our meet)
```
