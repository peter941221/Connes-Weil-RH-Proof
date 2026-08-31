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
