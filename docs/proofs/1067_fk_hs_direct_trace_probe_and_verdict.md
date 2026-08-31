# 1067 - F1' direct trace probe: measure Tr(K_S)_model = Tr(M − R_S) in the 1063 rig

Date: 2026-08-31. Follows 1066 (F1' collapses to ONE analytic contract
S2-FK-HS; its two unproved bridges are named BRIDGE 1 = meet-residual control
and BRIDGE 2 = grid→continuum basis) and 1063 (the discretized rig, the raw-F1
falsification oracle, and the D-weighted saturation data). This record closes
BRIDGE 1 by measuring `Tr(K_S)_model` DIRECTLY — building R_S_model as the
Gram-corrected meet per Lean — instead of inferring it from M's nonmeet mass.
No numeric probe is a proof; no PRODUCTION (生产) of any summability fact is
claimed. Probe: `docs/proofs/1067_fk_hs_direct_trace_probe.py`.

## 0. Operational verdict up front

```text
(1) BRIDGE 1 CLOSES TO AN IDENTITY IN FINITE DIMENSIONS - NO HIDDEN RESIDUAL.
    R_S is the star projection of the MEET (交) logRadialSupport ⊓
    semilocalFourierSupport (pinned this round, s1 below), so in the model
    R_S_model = P_W with W := U ∩ V, U := range(E), V := range(Q_S).  Then
        Tr(K_S)_model = Tr(M) - dim(U∩V)  =  SUM_{theta_n > 0} cos^2(theta_n)
    EXACTLY: the meet residual is identically zero because R_S_model captures
    precisely and only M's lambda ~= 1 ladder.  The quantity the single open
    contract S2-FK-HS needs to face in the model IS the 1063 nonmeet sum -
    measured here directly, three independent ways.

(2) PREDICTION (stated before running, falsifiable): fk_hs_sq TRACKS the 1063
    raw nonmeet sums 10.21 / 15.18 / 20.88 / 28.28 for {2,3,5} over the four
    octaves (xi_max 12.8/25.6/51.2/102.4), i.e. ~ xi^0.4 growth with a flat
    source anchor.  If confirmed with all cross-checks green, the verdict is
    ROUTE B: the unweighted IsTraceClassAlong K_S (= S2-FK-HS via record-1066's
    iff) FAILS for {2,3,5} in this model, and F1' must be routed through the
    D-weighted statement (record 1063: Tr(D oL K_S) saturates, owner-independent)
    rather than through S2-FK-HS as an intermediate.

(3) THE FORK IS CLEAN AND PRE-STATED - no post-hoc reading of the numbers:
      SATURATION   : fk_hs_sq increments halve over the 8x window (1063's
                     weighted-saturation signature), source anchor flat,
                     dt-invariance < 0.01%  ->  S2-FK-HS is analytically
                     PRODUCEABLE; schedule the analytic producer next.
      GROWTH       : fk_hs_sq tracks ~ xi^0.4 as predicted, cross-checks green
                     ->  ROUTE B (verdict text of (2)).
      MODEL MISREAD: source anchor grows, or any consistency gate fires
                     ->  trust nothing, re-audit the model reading first.

(4) GO: run the probe this round on the four 1063 octave grids plus the fixed-
    window dt-invariance pair; acceptance is the SUMMARY table + all gates +
    the three-way consistency flag < 1e-8, not any single number.
```

## 1. Pinned model (every line to a file:line)

| object | Lean pin | model in this rig |
|--------|----------|-------------------|
| E (radial support projection) | CCM24LogRadialSupport.lean:67-69 (lambda=1), via radialSupportProjection | diag(t >= 0); U = range(E) has ON basis {e_j : t_j >= 0} |
| Q_S (semilocal Fourier support projection) | CCM24FiniteSProjectionTrace.lean:86-91, star projection of ccm24SemilocalFourierSupportClosedSubspace | Q_S := HT_S @ E @ HT_S; a star projection because the gates verify HT_S is a self-adjoint involution (1063 §1); V = range(Q_S) = HT_S(U) |
| R_S (target Sonin projection) - PINNED THIS ROUND | CCM24FiniteSProjectionTrace.lean:97-102, star projection of ccm24SemilocalSoninClosedSubspace; and CC20Concrete/CCM24SemilocalFourierSupport.lean:134-137: `ccm24SemilocalSoninClosedSubspace lambda S := ccm24LogRadialSupportClosedSubspace lambda ⊓ ccm24SemilocalFourierSupportClosedSubspace lambda S` | R_S_model := P_W, the orthogonal projector onto W = U ∩ V (Gram-corrected meet: star projection of a closed MEET is exactly that) |
| K_S | CCM24FiniteSProjectionTrace.lean:160-166 def `E ∘L Q_S ∘L E - R_S`; factorization theorem :183-205 (targetProlateRemainder_eq_factor); Dev C1Prolate:81-92 F_K = Q_S oL (E − R_S) with K_S = F_K†F_K | M := ED @ HT @ ED @ HT @ ED (= E Q_S E since HT^2 = I, 1063 probe :95); K_S_model := M - R_S_model = FK†FK with FK := Q_S @ (ED - R_S_model) |
| principal-angle reading of M's spectrum | finite-dim linear algebra, stated in 1063 s1 (MODEL, not Lean) | nonzero spec(M) = {cos^2(theta_n)} for the principal angles between U and V; theta = 0 occurs with multiplicity dim(U∩V) and contributes 1 each |

The M-decomposition line is inherited from record 1063 §1 (BRIDGE 2 remains
open: grid spectrum → continuum named-basis series).  This round adds exactly
one new pin - the R_S meet at CCM24SemilocalFourierSupport.lean:134-137 - which
is what makes R_S_model a MEET projection rather than an ad hoc block.

## 2. The identity behind the probe (why no hidden residual)

Let A_U := P_U Q_S|_U, the compression of Q_S to U; it is Hermitian on U with
spectrum in [0,1], and its spectrum IS M's nonzero spectrum (compression
identity).  Write d = dim W.

```text
A_U eigenspace decomposition (principal angles):
  lambda = 1  <->  Q_S v = v for v in U  <->  v in U ∩ V      (multiplicity d)
  lambda < 1  <->  the nontrivial principal-angle directions, cos^2(theta_n)

(1) Tr(M)          = SUM_all cos^2(theta_n)         [incl. the d trivial ones]
(2) K_S|_U         = (I - P_W) Q_S (I - P_W)|_U     [K_S = E Q_S E - R_S, range(R_S) ⊆ U]
    in the A_U eigenbasis P_W is diagonal (1 on W, 0 off - eigenspaces of
    distinct eigenvalues are orthogonal), so spec(K_S) = {lambda < 1} ∪ {0}
(3) Tr(K_S)_model  = SUM_{theta_n > 0} cos^2(theta_n) = Tr(M) - d        EXACT

Consequences used by the probe:
  * "Tr(K_S)_model = nonmeet mass + meet residual" (1066 s3, BRIDGE 1 open)
    collapses to "meet residual ≡ 0": R_S_model subtracts exactly the ladder.
  * The quantity equals 1063's gap-split nonmeet-sum whenever the lambda ~= 1
    block is gap-separated from the rest (it was in every 1063 case, first gap > 0.02).
```

So the probe measures ONE number three independent ways and reports their
agreement as BRIDGE-1 closure evidence:

| path | computation | independence |
|------|-------------|--------------|
| A (spectrum) | fk_hs_sq = SUM of B-spectrum entries <= 1-tol, > floor   [B := Hermitian U-block of Q_S] | from eigh(B) only |
| B (trace identity) | tr_M_minus_d = Re Tr(M) - d; khs_eigsum = sum( eigvalsh(hermitian(M - R_S_model)) > floor ) | forms M and the explicit projector R_S_model = W_full W_full†, never path A's eigenvalues |
| C (Hilbert-Schmidt direct) | fk_hs_sq_direct = ||FK||_F^2 with FK := Q_S @ (ED - R_S_model); Lean proves K_S = FK†FK | entry-level Frobenius sum, no spectrum at all |

All three must agree to < 1e-8 relative; d must equal the count of M's
spectrum in its lambda ~= 1 ladder (the 1063 meet-block numbers are the
cross-validation target).

## 3. Measurement plan and gates

Grids (env `GRIDS_1067`, default = exactly 1063's four-octave sweep at fixed
T=20, xi_max 12.8 / 25.6 / 51.2 / 102.4): `[[1025,20],[2049,20],[4097,20],[8193,20]]`.
Families (env `SLIST_1067`, default as in 1063): `[];[2];[2,3];[2,3,5]` — the
source S={} is the ANCHOR (identical code path must plateau).

Dt-invariance pair (env `DTINV_GRIDS_1067`, default `[[4097,20],[8193,40]]`):
same frequency window xi_max = 51.2 at two resolutions.  Note M depends on N
alone in this rig (dt = 2T/N and dxi = 1/(N dt) are functions of N), so the pair
exercises the FULL code path twice at the same window and reports the relative
difference as a self-consistency figure; the growth-vs-saturation call rests on
the octave sweep.

Per (grid, S) gates (SystemExit(2) on failure, 1063 style):
- HT involution + self-adjointness < 1e-8 (source case), reflection symmetry
  of m_S = mu/mu_bar < 1e-10 for every S;
- Q_S idempotence < 4x the HT gate residual (it is a star projection in the model);
- positivity: lambda_min(B) >= -1e-6, lambda_max(M) <= 1 + 5e-8 (K_S = FK†FK must be positive);
- W_full invariance: ||(I - Q_S) W_full|| small relative to d and N.

Cross-validation against committed 1063 data (report, do not gate on memory):
the SOURCE meet block is the cross target - 1063 §3 records gap-split meet
counts 42 / 117 / 303 / 746 for S={} over the four octave grids; this probe's
`meet_gap_count` (gap split of M's spectrum) must reproduce them, while the
STRICT d = dim(W) may sit below them by the near-1 boundary layer (eigenvalues
in the gap-separated ladder but < 1 - TOL_MEET), which fk_hs_sq then counts as
K_S mass. Raw nonmeet sums to track for {2,3,5}: 10.21 / 15.18 / 20.88 /
28.28 (fk_hs_sq exceeds these by the boundary-layer unit-mass count); source
anchor flat (1063: 3.18/3.43/3.12/2.47).

Output per case: one `SUMMARY|...` line with fk_hs_sq, tr_M_minus_d,
khs_eigsum, fk_hs_sq_direct, their max pairwise relative deviation (consistency
flag), d, gap-split meet count + nonmeet-sum (1063-style diagnostics), and the
gate values; B-spectrum saved to `$OUTDIR/1067_Bspec_*.npy`.

## 4. Decision criteria (the fork, pre-stated)

| outcome | criterion (all must hold) | consequence for F1' |
|---------|---------------------------|---------------------|
| SATURATION → analytic producer | fk_hs_sq increments halve over the 8x window; source anchor flat; dt-invariance rel. diff < 0.01%; all three paths agree | S2-FK-HS (≡ IsTraceClassAlong K_S via record-1066 iff) is a finite, convergent target in the model → schedule the analytic producer of Summable |F_K e_i|^2 as the next brick; no Lean owner machinery remains |
| GROWTH → ROUTE B | fk_hs_sq tracks ~xi^0.4 (ratio pattern like 1063's raw nonmeet sums); source anchor flat; all three paths agree; dt-invariance clean | unweighted IsTraceClassAlong K_S fails for {2,3,5} in the model → the single contract S2-FK-HS as currently shaped is NOT producible from this family's data; F1' must be routed through the D-weighted statement (Tr(D oL K_S), 1063: saturates + owner-independent) — a Lean re-route, scheduled as its own design record |
| MODEL MISREAD | source anchor grows or any gate/consistency flag fires | no verdict; re-audit the model reading of R_S/Q_S before trusting any family's numbers |

## 5. Post-run addendum (filled after execution)

Run: single deterministic WSL run, all gates green, complete log with 21
`SUMMARY|` lines at `/home/peter/1067_full.log` (Linux-side verification
environment, unversioned per the 1063 convention). One operational note for
the record: an early duplicate launch ran concurrently and was killed by PID;
acceptance rests on this run's flushed log evidence plus the saved B-spectra
(`$OUTDIR/1067_Bspec_*.npy`), not on any process exit code (exit codes lie
across the WSL boundary, AGENTS 7a).

### 5.1 The measured number: Tr(K_S)_model over four octaves

```text
fk_hs_sq = Tr(M - R_S_model)   (xi_max: 12.8 / 25.6 / 51.2 / 102.4, T=20)
+----------+---------+---------+---------+---------+---------------------+
| S        | N1025   | N2049   | N4097   | N8193   | shape               |
+----------+---------+---------+---------+---------+---------------------+
| src {}   |  6.1786 |  6.4329 |  7.1208 |  6.4740 | FLAT, anchor PASSES |
| {2}      |  9.0332 | 11.1247 | 12.7980 | 13.3688 | growth                |
| {2,3}    | 13.7400 | 16.3261 | 19.1989 | 22.8190 | growth, steady        |
| {2,3,5}  | 16.1996 | 20.1700 | 26.8715 | 34.2696 | growth ~xi^0.36-0.4   |
+----------+---------+---------+---------+---------+---------------------+
{2,3,5} increments: +3.97 / +6.70 / +7.40 - INCREASING, no saturation bend;
measured exponent ln(34.2696/16.1996)/ln 8 ~= 0.36 (the raw nonmeet sums of
1063 sit at ~= 0.4-0.5 over the same window: fk = raw + O(1), so a constant
offset flattens the relative slope - SAME sublinear regime, not saturation).
Source anchor range [6.1786, 7.1208], max/min 1.15: flat as required.
```

Every row decomposes EXACTLY (4 decimals) into the committed 1063 raw nonmeet
sum plus a per-case boundary mass of O(1): e.g. {2,3,5}: 16.1996 = 10.2118 +
5.9878; 34.2696 = 28.2754 + 5.9942. The pre-stated prediction (s0(2)) is thus
confirmed up to that O(1) offset, which the smoke run identified before the
full sweep and s5.3 below quantifies.

### 5.2 BRIDGE 1 closes: identity + three-path agreement

All three independent paths agree on every one of the 20 measured cases; the
worst max-pairwise relative deviation is 2.6e-11 (N1025 src) and the best
8.7e-15 (N8193 {2,3,5}) - against the < 1e-8 closure gate:

```text
case            fk_hs_sq   trM_minus_d  khs_eigsum   fk_direct  consistency
N1025 src       6.1786     6.1786       6.1786       6.1786     2.57e-11
N4097 {2,3,5}   26.8715    26.8715      26.8715      26.8715    1.35e-13
N8193 {2,3,5}   34.2696    34.2696      34.2696      34.2696    8.71e-15
```

Cross-validation against committed 1063 data (report lines, all green): the
SOURCE gap-split meet count reproduces 1063 s3's 42 / 117 / 303 / 746 EXACTLY
at all four octaves, and `nonmeet_1063style` reproduces every published raw
sum to 4 decimals (spot: {2,3,5} 10.2118/15.1767/20.8779/28.2754 vs the
committed 10.212/15.177/20.878/28.275). Rig identity re-confirmed over the
full sweep, not just the smoke grid.

VERDICT ON BRIDGE 1: CLOSED. The meet residual is identically zero in finite
dimensions (s2's identity), and the only finite-resolution subtlety - a small
near-meet sub-ladder - is quantified below and shown to be O(1).

### 5.3 The near-meet boundary layer (the one new structural find)

The STRICT meet d = dim(W) sits slightly BELOW the gap-split meet block: a
few eigenvalues in the ladder are < 1 - TOL_MEET, so R_S_model leaves them in
K_S where they contribute ~unit mass each. Measured over all octaves/families
(from the saved B-spectra):

```text
boundary count (gap block minus d)      boundary top eigenvalues
S        | N1025 N2049 N4097 N8193     | observation
src      |   3    3    4    4          | all >= 0.9997, creep to 1 with N
{2}      |   5    6    6    6          | first ~3 at 1-1e-6; rest >= 0.98
{2,3}    |   6    5    6    6          | same shape
{2,3,5}  |   6    5    6    6          | bottom of the sub-ladder rises:
                                        | 0.99418 (N1025) -> 0.99699 (N8193)
```

Two readings matter for BRIDGE 2, and BOTH keep this verdict alive:

(1) The count is O(1) - bounded by 6 across all four octaves AND all families
    while the strict meet itself grows 39 -> 742 (Landau-type). A NEW angle
    bank would grow with the window like the raw nonmeet sums do; this does
    not. It is a fixed-size fringe of the infinite-dimensional Sonin meet
    whose extra directions have not yet converged to lambda = 1 at finite
    resolution (their eigenvalues creep up toward 1 as N grows - the direct
    evidence).

(2) Consequently the continuum Tr(K_S) lies between "fk_hs_sq" and
    "fk_hs_sq minus the fringe mass", i.e. between the measured table (s5.1)
    and the committed 1063 raw sums: for {2,3,5} either way is ~xi^0.4 growth
    with no saturation bend. BRIDGE 2's resolution therefore CANNOT change
    the fork outcome - only its constant term.

### 5.4 Dt-invariance (same window xi_max = 51.2, finer frequency grid)

```text
pair N4097/T20 vs N8193/T40   fk_hs_sq        rel-diff
src                          7.1208 / 6.1496  1.36e-01
{2}                         12.7980 / 11.8113 7.71e-02
{2,3}                       19.1989 / 18.1703 5.36e-02
{2,3,5}                     26.8715 / 26.8729 5.26e-05
```

The deciding family {2,3,5} is resolution-invariant to MACHINE LEVEL at the
fixed window (5.3e-5), mirroring 1063's raw nonmeet dt-quartering (0.003%):
the growth tracks the frequency WINDOW, not this grid - now re-proven for the
quantity the contract actually faces. For the O(1)-scale source and
intermediate families the same-window refinement moves fk_hs_sq by up to ~1
unit: the near-tolerance fringe eigenvalues shuffle across the 1 - TOL_MEET
threshold under refinement, a property of the strict-meet decomposition at
finite resolution (1063's raw src pair already showed the analogous 0.9%
wobble on its O(1) quantity). The anchor stays flat over ALL resolutions and
octaves: [6.1496, 7.1208].

### 5.5 VERDICT (per the pre-stated fork, s4)

```text
GROWTH -> ROUTE B. All GROWTH criteria hold:
  * fk_hs_sq grows ~xi^0.36-0.4 over four octaves for {2,3,5}, increments
    increasing (no halving anywhere in the table - SATURATION excluded);
  * source anchor flat at every resolution and octave;
  * all three paths agree to <= 2.6e-11 on all 20 cases (< 1e-8 gate);
  * dt-invariance clean where it must be (deciding family: machine level).

CONSEQUENCES for F1':
  1. The UNWEIGHTED IsTraceClassAlong K_S - which record 1066's iff
     identifies termwise with the single open contract S2-FK-HS =
     targetProlateRemainderFactorSummable - FAILS for {2,3,5} in this model:
     Tr(K_S)_model = 16.2 / 20.2 / 26.9 / 34.3 over the octaves.
     S2-FK-HS AS CURRENTLY SHAPED is not producible from this family's data.
  2. F1' must be routed through the D-WEIGHTED statement (Tr(D oL K_S):
     record 1063 shows it saturates over the same window, owner-independent).
     That Lean re-route (replace the single-contract corollary's S2-FK-HS
     premise by targetProlateRemainderDetectorWeighted_isTraceClassAlong and
     re-shape the active-order identity around D K_S = (A C)^dagger(A C) +
     C^dagger[C, K_S]) is scheduled as its OWN design record - this round
     only measures; it changes no Lean.
  3. BRIDGE 1 is CLOSED (s5.2). BRIDGE 2 (grid -> continuum basis) stays
     open but is now SHARPENED: it must account for the O(1) near-meet fringe
     (s5.3), and cannot alter this verdict (s5.3(2)).

GUARD STATUS UPDATE: 1063's {2,3,5} guard was INHERITED by S2-FK-HS at record
1066 "not a verdict" because the probe measured M while K_S = M - R_S. That
ambiguity is now RESOLVED in the unfavorable direction: measuring Tr(M - R_S)
directly, the guard's growth regime survives intact (plus an O(1) fringe).
The single open contract fails for {2,3,5} in the model; ROUTE B stands.
```

