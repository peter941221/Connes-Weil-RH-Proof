# 1069 - LINE (5) detector coverage: idea ledger and the first decisive probe

Date: 2026-08-31. LINE (5) ("no off-line zero escapes the detector net") is
iff-RH and has ZERO design on the table (RH_ROUTE_MECHANISM view (a)/(c);
record 1050: the detector-selected semilocal step IS the RH-level gate).
This record converts the 2026-08-31 brainstorm session into a ledger: seven
idea families, their prerequisite questions, and - the actual purpose - a
FIRST DECISIVE PROBE (1069_coverage_tension_probe.py) with a pre-stated
fork, run before any design commitment. No idea below is a proof sketch of
RH; the output standard is: testable signatures, layer-able proof
obligations, and design vocabulary.

## 0. The logical shape (what any LINE (5) solution must do)

```text
LINE (1) supplies:   q(D) >= 0  for every detector D in the family F
LINE (5) must flip:  "∀ D ∈ F nonneg"  =>  "every zero is on the line"
Favorable structure: D = positive convolution  =>  zero-weight ĥ_D(ρ) ~
|c_D(ρ)|² >= 0, so q(D) is a POSITIVE-vs-POSITIVE inequality: Gram/frame
structure, not arbitrary linear functionals.
Known hard core: coverage needs |Im ρ| -> ∞ UNIFORMITY in the zero.
```

## 1. The seven idea families (A-G), prerequisites first

```text
A. PARSEVAL FRAME (working name: zeros-as-vectors, family-as-frame)
   Formulation: zeros {ρ_i} = vectors z; each D_(S,k) gives coordinates
   c_S,k(ρ_i). LINE (1) = upper frame bound; LINE (5) = LOWER frame bound
   Σ_D |c_D(ρ_i)|² >= c‖z‖² (no zero vector orthogonal to the family).
  咬合: the rig's cos²θ_n ARE principal angles = frame defects; the meet
   = redundancy; CC20 exceptional directions + rank-one repair = frame-
   operator finite-section perturbation. The vocabulary already fits.
   PREREQ (before any theorem): a Weil-functional-level numeric model of
   c_D(ρ) - i.e. LEVEL-1 below. Without it "frame" is a metaphor.

B. FINITE-SECTION EXCEPTIONAL DIRECTION AS ZERO SHADOW
   Speculation: λ* ≈ 1.05158 (CC20 paper scale) is a spectral shadow of
   zero data (Hilbert-Pólya flavored). Coverage = "every off-line zero
   creates a λ(ρ)>1 exceptional direction the rank-one repair cannot fix".
   PREREQ: build T(λ) from the landed eq-115 table (scripts/cc20_eq115/),
   validate λ*, then test responsiveness to zero data. CHEAP TO KILL.
   Structural caveat: the eq-115 side is arithmetic+archimedean only -
   zeros enter nowhere by construction, so any encoding would be a
   deep transfer statement, not a side effect.

C. STONE-WEIERSTRASS CLOSURE OF THE DETECTOR FAMILY
   Log line = LCA group; if span(F) is a point-separating self-adjoint
   convolution-closed algebra, its closed span is everything; q >= 0 on F
   + continuity of q extends LINE (1) to ALL admissible tests => Weil.
   PREREQ: in which topology is q continuous, and do the triple-vanishing
   conditions survive the closure? Unanswered => route sketch only.

D. DE BRANGES DICTIONARY
   Detectors = reproducing kernels K(·,w) of a de Branges space H(b);
   coverage = totality of the semilocal family in H(b); the CC20 operator
   T as a compression/colligation matrix. PREREQ: a translation pilot for
   ONE object (e.g. reproduce the eq-115 kernel as an H(b) kernel).
   Risk: de Branges' own failure point (expansion hypothesis) is exactly
   a coverage statement.

E. NYMAN-BEURLING / BAEZ-DUARTE DENSITY, SEMILOCAL ANSATZ
   The canonical "coverage as density" template. REOPENING DISCIPLINE:
   Nyman is SCREENED OUT in the archive with a named density/domain
   obstruction; re-entry must answer that obstruction text-first. The
   {μ_S} finite Euler-product sieve family is a new ansatz, but the
   audit of the named obstruction PRECEDES any probe.

F. KESTEN / AMENABILITY SIGNATURE
   Off-line zeros <=> convolution spectral radius > 1 on some generated
   semigroup; coverage <=> non-amenability of the S-exhaustion. Far from
   the rig; recorded for completeness.

G. CONSTRUCTIVE DUAL HUNTER
   Contrapositive: an off-line ρ forces q(D) < 0 for some D ∈ F; find it
   by making Hahn-Banach explicit: an (S, λ)-parameter net as a partition
   of the off-line strip; the detector whose cell contains ρ must flip.
   Requires: margin analysis m(D) = q(D) (how close to 0 does LINE (1)
   leave us) vs single-zero weight ĥ_D(ρ). This is LEVEL-1 again.
```

Ranking by (fit with existing machinery, cheapest falsifiable test,
modularity): A > B > G > C > D > E > F, with E gated by the archive audit
and B likely dead-on-arrival-but-cheap (structural caveat above).

## 2. The coverage-positivity tension (the thing the probe measures)

```text
Coverage pull:  to see a zero of height γ  (rig coordinate ξ_γ = γ/2π),
                the Gaussian root needs k = O(1/ξ_γ) - flatter and flatter.
Positivity pull: the detector is ~UNWEIGHTED below ξ ≈ 1/k, so the
                saturated D-weighted quantities are expected to inherit the
                raw semilocal mass at window 1/k. 1067 measured raw
                Tr(K_S) ~ Ξ^0.4, so the tension predicts
                    t_tr1(k)  ~  C · k^(-0.4)   as k ↓ 0.
                If the GATE-1 certificate constants are fixed (one-shot
                architecture), a k^(-0.4) blowup means the family cannot
                cover unboundedly high zeros - LINE (5) dies IN THIS
                SHAPING and forces the frame/multiscale redesign (A/G).
This tension is measurable TODAY in the 1068 rig by sweeping k.
```

## 3. LEVEL-2 probe (this round): design, gates, pre-stated fork

Probe: `1069_coverage_tension_probe.py` - reuses the 1068 rig verbatim
(build_context + measure_k, all identity gates stay live). Sweep
k ∈ {0.3, 0.2, 0.1, 0.05, 0.02} (plus the committed 1.0 values for
reference) on grids {1025, 2049, 4097}, families {src, {2,3,5}}; zero
heights from mpmath `zetazero(j)`, j = 1..30; report the coverage matrix
w_k(ξ_j) and the log-log slope b of t_tr1(k) at the largest grid.

```text
FORK (stated before running):
  H1 (tension REAL):   b ≈ -(0.3..0.5), i.e. t_tr1 ~ k^(-0.4±0.1), and the
     w_k(ξ_j) matrix shows coverage requires k ~ c/ξ_γ.
     => VERDICT: the D-weighted one-shot shaping CANNOT be LINE (5)'s
     mechanism; escalate to A/G redesign; record the exponent as the
     design constraint.
  H2 (tension WEAK):   t_tr1 stays <= ~2x its k=1.0 value down to k=0.02
     (the semilocal growth lives at LOW frequencies, absorbed by moderate
     k).  => VERDICT: B/G stay live in this window; schedule LEVEL-1.
  H3 (non-monotone / erratic): no verdict; investigate the rig reading.

LEVEL-1 (next substantial probe, designed here, NOT run this round):
  implement qw at Weil-functional level for the selected test/convolution
  family: archimedean + finite terms and Σ_ρ ĥ_D(ρ) over the first N
  zeros; validate q(D) >= 0 (LINE-1 sanity), then measure the hunting
  ratio r(D, γ) = ĥ_D(β+iγ) / q(D)-margin over the family and heights.
  r >= c > 0 uniformly => the family hunts (G lives). r -> 0 => A's
  adaptive-frame redesign is forced. Preconditions: pin CC20's exact
  test conventions from 1057's tex map (intro-vs-final vanishing sets).
```

## 4. Acceptance

All 1068 identity gates stay green at every k (measure_k asserts them);
t_tr1/l_tr1 via the same SVD path; the zero table from mpmath is
authoritative; acceptance = the SUMMARY table + slope fit + coverage
matrix, not any exit code.

## 5. Post-run addendum (filled after execution)

Run: one deterministic WSL sweep (28/28 expected SUMMARY lines, full log
`/home/peter/1069_probe.log`, Linux-side verification environment, unversioned
per the 1063 convention). Acceptance on the flushed log, not exit codes: zero
error/traceback/FAIL/NUL; every in-`measure_k` identity gate stayed live and
green (res1/res2/res3 <= 5e-14 everywhere); the k = 1 {2,3,5} anchor
reproduced the committed 1068 s5.1 table digit-for-digit (3.7836/3.7527/3.7376)
and src fk_unw = 6.1786 with strict meet d = 39 reproduced 1067 exactly.

### 5.1 The measured fork table

```text
{2,3,5}, t_tr1 = ||D_k K_S||_1 at the LARGEST window measured per k
(kxi = k*xi_max at that point; all kxi >= 6.4 so the detector is effectively
compact on the window and these are f(k) readings, not window artifacts):
+--------+---------+-------+-------------------------------------------+
| k      | t_tr1   | kxi   | step ratio (per k-halving)                |
+--------+---------+-------+-------------------------------------------+
| 1.0    |  3.7319 | 102.4 |  (1068 committed, N8193)                  |
| 0.5    |  5.7711 |  51.2 |  1.547   (local slope log2 = 0.63)        |
| 0.25   |  8.5088 |  25.6 |  1.474   (0.56)                           |
| 0.125  | 11.9801 |   6.4 |  1.408   (0.49)                           |
+--------+---------+-------+-------------------------------------------+
Pooled log-log fit over the 11 asymptotic points (k*Xi >= 6.4):
  b = -0.569 (all), b = -0.536 (k <= 0.5 subset, max residual 0.017).
Ray test (constant k*Xi = 12.8, Xi = 12.8 -> 51.2): 3.78 -> 5.77 -> 8.50,
max/min = 2.25 - grows ~1.5x per Xi-doubling; H2 predicted flatness.
src anchor: b = -0.261 (all) / -0.188 (k <= 0.5), mild growth consistent
with its own FLAT raw plateau (~6.5) - the anchor does what its raw does;
no MODEL MISREAD.
```

### 5.2 VERDICT: H1 confirmed - the coverage-positivity tension is REAL

Per the pre-stated fork s3: the continuum detector-mass function blows up as
k ↓ 0 with NO saturation bend over the measured octave k in [0.125, 1]:

```text
  f(k) = lim_Xi t_tr1(k, Xi)  ~  amp * k^(-0.54 +- 0.03),  amp(1) ~ 3.7-4.0.
```

The measured exponent is STEEPER than the pass-band prediction -0.4 (the
Gaussian soft edge is worse than a sharp cutoff), and just outside the
pre-stated H1 band [-0.5, -0.3] on the steep side. Structural refinement the
fork did not anticipate: the ENTIRE blowup lives in the positive sandwich leg
p_hs_sq = Tr(C_k K_S C_k) (t_tr1 ~= p_hs_sq + O(1) at every point), while the
root-commutator leg is scale-robust (l_tr1 = 1.23-1.73 across the whole sweep,
s_tr1 <= 0.91). So 1067 (k = 0 grows ~Xi^0.4), 1068 (k = 1 flat in Xi), and
1069 (f(k) ~ k^-0.55) are ONE consistent picture: Tr(C_k K_S C_k)(Xi) ~
min(Xi, c/k)^alpha with alpha ~ 0.4-0.55; the S2 pairData route is scale-
robust, and the S1'/1066-iff quantity is the one that carries the tension.

```text
CONSEQUENCES (design constraints, per s2-s3):
  1. The ONE-SHOT UNIT-SCALE shaping of LINE (5) is dead as a mechanism:
     covering zero #j needs k_j = 1.177*2pi/gamma_j -> 0, and the certificate
     mass grows f(k_j) ~ gamma_j^0.55 without bound (measured: f(0.125)/f(1)
     = 3.2x over one octave; extrapolated f(0.031) ~ 25 for zero #100,
     f(7.4e-6) ~ 2.5e3 for gamma = 1e6).
  2. ARCHITECTURAL NUANCE (refines fork consequence 1): the route's
     certificates are PER-DETECTOR (record 1050 detector-selected semilocal),
     so a polynomially-degrading constant is a schedule/structure cost - the
     entire GATE-1 alpha machinery is unit-scale and would have to be
     re-proved per scale k with degrading constants - not an immediate
     logical contradiction. What fails logically is the fixed-constant
     one-shot reading, exactly as pre-stated.
  3. The redesign vocabulary is A/G (frame / dual hunter): EITHER a
     multiscale detector net with one cell per height band (per-cell
     constants, no uniformity obligation), OR a proof that the LEVEL-1
     hunting ratio stays bounded below as k -> 0 - which is precisely the
     next measurement.
```

### 5.3 Which path (the answer to "should we walk which path")

```text
PRIMARY: G (constructive dual hunter) via LEVEL-1 - implement the Weil
  functional q(D_k) numerically for the Gaussian detector family
  (archimedean + finite terms + sum_rho h_D(rho) over the first N zeros),
  validate q >= 0 (LINE-1 sanity), then measure the hunting ratio
  r(D_k, gamma) = h_Dk(beta+i gamma) / (q margin) on the (k, gamma) grid.
  This single number decides between:
    - r >= c > 0 as k -> 0: a scale-parameterized one-shot family with
      polynomial constants survives; write the per-scale design record
      (schedule cost, accepted).
    - r -> 0: the adaptive frame (A) is forced; the exponent -0.55 is the
      budget constraint the frame must beat.
  Preconditions: pin CC20's test conventions from the 1057 tex map; the repo
  has NO qw implementation today (recon 2026-08-31: the former root-level
  Lean generator was private scratch code, while
  scripts/scratch_nyman_block.py contains only digamma/Gram parts).
SIDE (cheap, one session): B (lambda* ~ 1.05158 as zero shadow) - build
  T(lambda) from the landed eq-115 table and test responsiveness to zero
  data; the structural caveat (arithmetic+archimedean only, zeros enter
  nowhere) predicts DEAD, but the kill is cheap and permanently informative.
AFTER LEVEL-1: A (Parseval frame) supplies the redesign vocabulary with the
  cos^2 theta / meet / rank-one-repair machinery already banked; its own
  prerequisite is LEVEL-1's c_D(rho) model, so it cannot go first.
UNCHANGED: E stays gated by the Nyman archive audit; C, D, F unchanged.
```

### 5.4 New probe-fidelity law (banked in AGENTS 7c (17))

A fixed-grid parameter sweep cannot see a continuum blowup: at fixed window
the observable saturates (D_k -> I as k -> 0 is FINITE on the grid), so the
H1/H2 fork is invisible to it. The discriminating design is the
constant-product ray k*Xi = kappa0 (here kappa0 = 6.4, 12.8, 25.6, 51.2),
which keeps the detector's effective cutoff and the window marching together:
along the ray H1 predicts growth ~Xi^alpha, H2 flatness. Same family as law
(15) (constant window, quarter dt) with the roles of the two knobs exchanged.
