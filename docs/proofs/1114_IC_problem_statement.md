# 1114 - I-C (the Q-F2 function-class gap): exact statement, diagnosis, prescribed bridge, literature front

Date: 2026-09-03 (night, post-1112, concurrent with 1113).

Status: PROBLEM-STATEMENT record (the "shape" deliverable requested by the
standing order). No proof is claimed here. Companion:
1114_IC_recon_preregistration.md + 1114_IC_recon_probe.py (quantitative
gap tables; model-declared, not certificates). RH NOT claimed; no map
change keyed.

## 0. The two sides, with citations

### 0a. What is CERTIFIED (the window side)

The certified class is the 5-dimensional quotient

    V(a, K) = span{ phi_k : k = 1..K } / {triple vanishing},
    phi_k(u) = P_{k-1}(u/a) * exp(-1/(1-(u/a)^2)) on |u| < a, 0 otherwise,

with K = 8 and vanishing moments s in {0, 1/2, 1} (rows R of the 1112
machinery: docs/proofs/1112_true_interval_whitened_probe.py:49,69-77,
build_class :136ff). For each test g in V(a,K) the gate value

    GATE(g) := archimedeanTerm(g* * g) + finitePrimeSum(g* * g)

is uniformly bounded above by a certified negative constant:

    sup_{g in V(a,K)} GATE(g) <= top(A+P)|_{V(a,K)} <= -pin(a) < 0

certified at three radii by the 1112/1113 dependency-safe true-interval
mechanism:

    a=2  top <= -1.0423774e-06      (1112)
    a=3  top <= -1.204049e-08       (1113, PASS-IV38, min slack +0.9785)
    a=4  top <= -5.9993e-11         (1112)
    a=5  STRADDLE: no certificate; float pin(5) = 4.4251564e-13,
         3.8x BELOW the registered extrapolation band.

The identity branch
A+P = -Z on V is confirmed numerically at four radii to absolute 6.4e-11
(a=2, GL-256) / 1.54e-14 / 1.56e-14 / 2.04e-14 (a=3,4,5; 1105/1108/
1110/1113), so -pin(a) = -lambda_min(Z|_V) to that precision.

### 0b. What must DISCHARGE the gate (the detector side)

The Lean gate (record 1089, pushed):

    orbitWindowSemiLocalGate g :=
      C1SameOwnerWeil.archimedeanTerm g.convolutionSquare
        + C1SameOwnerWeil.finitePrimeSum g.convolutionSquare <= 0
      (ConnesWeilRH/Dev/C1OrbitWindowSemiLocalGate.lean:57-59)

with the one-line bridge

    (CC20VanishesOn cc20TripleFiniteVanishingSet g) ->
    (orbitWindowSemiLocalGate g -> 0 <= qw g)
      (same file :63-72, via qw_eq_neg_archimedeanTerm_sub_finitePrimeSum
       _of_vanishesOn_cc20Triple)

and the pinned headline

    (rho : sourceNontrivialZeroSet) (hoff : re rho <> 1/2)
      (hright : 1/2 < re rho) ->
    exists g, exists n : Nat,
      HealthyYoshidaDetectorData rho g
      & support g <= Ioo(-(n+2), n+2)
      & forall q in globalPrimeIndexSet g.convolutionSquare,
          q < exp(2*(n+2))
      (same file :126-134; visible-prime readback :103-119)

constructed by the D1 assembly at baseLower=-1, baseUpper=1, lower=-1,
upper=1, epsilon=1, T = dyadic tail start of rho's height, and

    R = 2^(n0+1) + 2 + dist(2, rho),   2^n0 < |im rho| <= 2^(n0+1)-ish
      (same file :142-144, exists_dyadic_tail_start_... :142-143)

The support radius is n+2, where n is produced inside the assembly lemma
(ConnesWeilRH/Source/CC20YoshidaConvolution.lean:1026-1048) by
exists_convolutionIterate_convolution_distance_bound_lt (:1059-1062):
n must satisfy 2^(-n) * C < epsilon, where C is the quadratic-decay
constant of the correction that INTERPOLATES (targets at rho, exact
zeros at every node of sourceNontrivialZerosInClosedBallFinset rho R
(:1037-1041), ball of radius R around rho). So n = n(R, C(B(rho,R)),
T, epsilon): the detector window radius a_det(rho) = n+2 grows with the
number and tightness of the visible zeros near rho.

## 1. The gap, stated exactly

    I-C / Q-F2:  the detector class { g : HealthyYoshidaDetectorData
    rho g } is NOT covered by any certified window class. For every
    certified radius a (a = 4 today, horizon a = 5 at 1113's registered
    prediction) and every zero rho off the line:

    (G1 support)   a_det(rho) > a_max  ->  no V(a_max, 8) certificate
                   applies to the detector's gate value. The certified
                   statement quantifies over V(a,K); the gate obligation
                   quantifies over the detector square g* * g whose
                   support is Ioo(-(n+2), n+2).
    (G2 content)   the detector is built to violate positivity WHERE
                   rho sits: its Laplace side carries the target value
                   at rho (height |im rho| >= gamma_1 = 14.13...) and
                   forced zeros at all ball nodes; the certified window
                   analysis is dominated by lambda_min(Z|_V), the
                   FEWEST-zero low-frequency corner of the spectral
                   side. The two classes are spectrally disjoint:
                   measured quantitatively in 1114b as the fraction of
                   model-detector spectral energy inside the certified
                   low band.
    (G3 horizon)   pin(a): 1.4433774e-06, 1.6140489e-08, 2.5999281e-10,
                   4.4251564e-13 at a = 2, 3, 4, 5 (1112/1113). The
                   two-point geometric fit (r = 1.342e-02/unit) held
                   2->4 (realized 1.12e-02, 1.61e-02) and COLLAPSED at
                   4->5 (realized 1.70e-03): the certified margin decays
                   SUPER-geometrically (1113 §3b booked falsifier), so
                   brute-force window certification degrades FASTER than
                   exponential while a_det(rho) >= 5 grows only
                   logarithmically in |im rho|. At a = 5 the machine
                   already STRADDLES (DELTA wider than realized pin,
                   HRAD ~ 5e-12 >> pin(5)); no a >= 6 cell is even
                   attempted. The gap is wider than the (2,4)-pair
                   suggested.

Consequences: the 1089 gate Prop for the pinned detector is an
RH-strength obligation (its truth on the detector square is what the
bridge needs, and the gate on V is proven without RH only because V is
spectrally tiny). The class gap is the proof's last structural mile.

## 2. Prescribed bridge (two stages; what "dominance" must formalize)

Stage A - RH-free finite input (literature-grade, to be imported):
  * gamma-floor: RH + simplicity verified up to height 3*10^12
    (Platt-Trudgian, "The Riemann hypothesis is true up to 3*10^12",
    Math. Comp. 90 (2021)); zero locations become FINITE explicit data
    below the floor;
  * sigma-ceiling: Ford zero-free region / density: 1 - sigma >=
    c (log t)^(-2/3) (log log t)^(-1/3) (O. Ford 2002) - the off-line
    zeros the detector could sit on are confined;
  * compact reparametrization: (sigma, u = gamma * a) makes the
    detector window a compact parameter domain over the Dirichlet cell
    cover of the ball B(rho, R).

Stage B - the owed lemma (NOT in the literature; this is the core):
  LOCAL-ZERO-CONFIGURATION DOMINANCE: for each zero configuration in
  the ball B(rho, R) consistent with Stage-A data, the detector gate
  value GATE(g* * g) is bounded above by the max of GATE over an
  effectively enumerable finite window family (a certificate-compatible
  convex/geometric domination: e.g. g* * g <= combination of V(a_i, K)
  squares in the pencil order + a remainder whose gate contribution is
  controlled by the zero-free region). Schematically the missing item
  is:

    GATE(detector) <= sup { GATE(w) : w in window family covering B }
                    + error(floor, density)        < 0.

  Everything after that is bookkeeping against the 1089 bridge
  (vanishing + headline support + visible primes already formalized).

## 3. Literature front (2026-09-03 scout; in-house per standing directive)

* arXiv:2608.24827 (2026-08-25) "Weil positivity in compact windows: a
  finite reduction, certified two-sided bounds, and a Landau-Widom
  decay law" - CLOSEST external object: a pointwise envelope for the
  Weil symbol + a Weyl-optimal comb constant converting WINDOW
  positivity into PSD of ONE finite matrix (complex tests support 1.6;
  simple even ground state = spectral hypothesis of the
  Connes-Consani-Moscovici-van Suijlekom program). It STOPS INSIDE the
  window: the finite reduction is exactly our V(a,K) theorem-side;
  the bridge OUT to per-zero detector classes is not its object.
  Its certified two-sided bounds + decay law are independent-style
  confirmation of our pin(a) geometric-decay observation.
* arXiv:2606.09096 screw-function Weil form; arXiv:2607.02828 finite
  Guinand-Weil dictionary + archimedean tail order; arXiv:2607.24830
  Suzuki-operator numerical realization - supporting cast for the
  finite-window machinery (none crosses G1/G2/G3).
* arXiv:2106.01715 tiny eigenvalues of the Weil form on fixed-support
  windows - the small-eigenvalue phenomenology our DELTA/pin budget
  is the certificate of.
* arXiv:2306.04799, 2503.15449, 2501.14545 Montgomery pair correlation
  (rigorous partial results); arXiv:2412.15481 rigorous zero-spacing
  knowledge falls far short of conjecture - the Stage-A input ceiling
  and why the dominance lemma must be configuration-local, not
  statistical.

## 4. What counts as shape (眉目) delivered by this record

  (1) The exact two-sided statement with file:line anchors (§0-1) -
      done here.
  (2) Quantified gap: a_det model table (zeros k=1..34, ball radii
      R=2..32, n_model, a_det = n_model+2 vs certified a_max = 4 and
      horizon 5) and spectral-disjointness fraction table
      (1114_IC_recon_probe.py).
  (3) The dominance-lemma skeleton with its inputs/outputs pinned
      (§2 Stage B) and the literature confirmed to stop short.
  Not claimed: any discharge, any RH consequence, any map change.
