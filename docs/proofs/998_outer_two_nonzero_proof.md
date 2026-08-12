# 998 - OUTER channel: nonzero radial-complement of the metric coframe on the {2} family

Date: 2026-08-11. Status: rigorous analytic witness (coordinate-exact, one constructive
Sonin-band lemma signposted); the companion obligation module now BUILDS axiom-clean on WSL,
but the closed Sonin-band witness (the theorem) is still OPEN.
RH NOT claimed. See docs/815, 872, 827, 884, 993, 995, 996, 997.

## 0. Goal

For a NON-EMPTY finite-prime family - concretely `visiblePrimes = [2]` - prove

    || (I - R_radial) o D ||  >  0

where (repo-verified defs, all in `CCM25Concrete`):
  R  = radialSupportProjection lambda          = projection onto `t >= log lambda`
       (= starProjection of ccm24LogRadialSupportClosedSubspace lambda, functions
       vanishing on `t < log lambda`;  CCM24FiniteSProjectionTrace.lean:76)
  D  = finiteEulerMetricCoframe lambda family  = Ambient o J o GInv
     = (T^dag T) o J o finiteGramInv           (CCM24FiniteSCoframeResponse.lean:37)
     ambient carrier: L^2(on Re, log-coordinate) = cc20GlobalLogCrossingL2.

Because the two channels (Outer=(I-R)D and Band=(R-Ro)D+forward) live on orthogonal
subspaces (docs/815), Outer != 0 alone REFUTES the canonical infinite-carrier Gate for
that family.  We show Outer != 0.

## 1. The exact coframe action near the band edge (rigorous, coordinate)

The finite Euler transport is the ordered product of the factors (`rho = exp t`)

    (T_p f)(t) = f(t) - c_p f(t - log p),        c_p = p^{-1/2},  log p > 0
    (T_p^+ f)(t) = f(t) - c_p f(t + log p)        (adjoint, shift UP)

(`ccm24PrimeEulerTransportEquiv_coeFn`, CCM24EulerTransport.lean).  For {2},
T = (1 - c_2 U_{-log 2}), T^dag = (1 - c_2 U_{log 2}), c_2 = 2^{-1/2}, and
Ambient = T^dag T.  For any x with x = 0 on `t < log lambda` (x in the radial
band, e.g. x = J (GInv w) with w in the source Sonin carrier):

   T x   : (t) = x(t) - c_2 x(t - log 2)            (stays supported on t>=log)
   T^dag(T x)  = (T^dag T) x
   (T^dag T x)(t)
     = (Tx)(t) - c_2 (Tx)(t + log 2)
     = [x(t) - c_2 x(t-log 2)] - c_2 [x(t+log 2) - c_2 x(t)]
     = (1+c_2^2) x(t) - c_2 x(t-log 2) - c_2 x(t+log 2).

On the open strip  log-l2 < t < log-lambda  (below the band edge):
   x(t) = 0  and  x(t - log 2) = 0   (both < log-lambda), so
   (T^dag T x)(t) = - c_2 @ x(t + log 2).            [EXACT]

Hence, for w in the source Sonin carrier V_S at scale lambda, with x := J(GInv w):

   ((I - R) D w)(t)  =  (T^dag T x)(t)  =  -2^{-1/2} @ x(t + log 2)
                        for almost every  t  in  (log-lambda - log 2, log-lambda).

So the outer leakage is NONZERO as soon as x has nonzero L2-mass on the shifted
window  (log-lambda, log-lambda + log 2)  (because t -> t + log 2 is a bijection of
(log-lambda - log 2, log-lambda)  onto  (log-lambda, log-lambda + log 2)).

## 2. The single Sonin-band witness lemma (the analytic leaf)

CLAIM (constructive, the one honest leaf): the archimedean Sonin carrier
  V_S = ccm24ArchimedeanSoninClosedSubspace lambda
        = (functions=0 on t<log)  AND  (Hardy--Titchmarsh conjugate vanishing on t<log)
contains a nonzero element whose value is nonzero somewhere on (log-l, log-l + log 2).

WHY: it is classically the Paley-Wiener/Titchmarsh model of the half-line -- the Hilbert
space of L2 functions on (log-lambda, oo) whose analytic conjugate is also supported there --
an infinite-dimensional closed Hilbert subspace of L2(log (log-lambda, oo)).  The finite-Euler
transport `T` is a continuous-linear equivalence onto the semilocal Sonin space
(`ccm24FiniteEulerTransport_maps_sonin`, SemilocalFourierSupport.lean), so `V_S` has the full
richness of the radial band and carries non-zero open sets/elements on every non-empty window,
including (log-lambda, log-lambda+log 2).  Picking any such element and pulling it back by `T`
gives the witness.  In Lean this existence is the ONE real analytic leaf to exhibit explicitly;
it is not an assembly of existing identities.
Assumption table:
- Proven, repo: D = Ambient o J o GInv, GInv bijective on V_S,
  J isometry, radial projection geometry, the family structure, J^dag D = I.
- This doc PROVES the coordinate depletion stripe above.
- THE REAL ANALYTIC LEAF: existence of the nontrivial V_S element nonzero
  on (log-lambda, log-lambda+log 2).  Its Lean sealing needs the bisomorphism
  V_S ~ V_semilocal (already in library as a cL equiv) transferred to an
  explicit element; that is the last, honest, non-assembled step.

## 3. Choosing w completes the bound

Given any u0 in V_S (a carrier element) nonzero on the window, take the input vector
w := finiteEulerGram u0  (the inverse of finiteEulerGramInv, so that
finiteEulerGramInv w = u0).  Then x := J (finiteEulerGramInv w) = J u0 = u0 in V_S is
nonzero on the window.  By the strip-exact identity (1), ((I-R) D) w equals
-2^{-1/2} * (u0 shifted right by log 2) almost everywhere on
(log-lambda-log2, log-lambda) -- a nonzero L2 element, since t -> t+log2 is a bijection
there.  Hence (I-R)D is nonzero on the source vector w, so its operator norm > 0.

Numeric cross-check: docs/884 reports ||(I-R) o D|| ~ 0.62 on log-l in [-2,2]; this
proof establishes the positive lower bound via an exact, coordinate-computed nonzero image.

## 4. Status and next Lean step

- The coordinate identity above is exact; the obligation module
  `Dev/OuterTwoNonzeroObligation.lean` (`twoOuterNonzeroObligation`, with `twoFamily`
  carrying the prime term `(2,1)` and `twoFamily_memTerm`) now BUILDS axiom-clean on WSL
  (`lake build ConnesWeilRH.Dev.OuterTwoNonzeroObligation`: 3315 jobs, exit 0; `#print axioms`
  on all four decls = `[propext, Classical.choice, Quot.sound]`).  Isolated mirror
  `/home/peter/verify/cwr-998outer` created per AGENTS s8 (persistent mirror dirty, untouched).
- Still OPEN: the constructive Sonin-band witness of section 2 - an explicit nonzero element
  of `V_S` nonzero on `(log-lambda, log-lambda+log 2)`, pulled back through the
  finite-Euler semilocal-Sonin equivalence.  This is the real analytic leaf; closing it
  transcribes the proof of the positive lower bound into a theorem of the nonzero operator norm.

RH not claimed. No new axiom/sorry.

## 5. Honest status: the Sonin-window witness is a real analytic leaf

The coordinate identity of section 1 is exact and closed.  The remaining gap is the
existence of a nonzero element of the Sonin carrier V_S that is nonzero on the
shifted window (log-lambda, log-lambda + log 2).  It must not be papered over, so this
section records precisely what is proven in-library, what is a plausible-but-unformalized
operator argument, and what is genuinely open.

Proven / in-library (no axiom):
- D = Ambient o J o GInv with GInv bijective on V_S and J an isometry; section 1 derives,
  exact in coordinates, that on the open strip (log-lambda - log 2, log-lambda) one has
  ((I-R) D w)(t) = -2^{-1/2} x(t+log 2) with x = J (GInv w), and t -> t+log 2 bijects onto
  (log-lambda, log-lambda+log 2). So (I-R)D nonzero is exactly equivalent to: some x in V_S
  has nonzero L2 mass on the shifted window (docs/815 makes outer channel independent and
  sufficient for the family).
- V_S is a closed Hilbert subspace of L2 over the half-line, the Paley-Wiener/Titchmarsh
  model: infinite-dimensional, so it has an open ball of elements on every non-empty window.

Plausible operator argument (NOT yet Lean-sealed, so still open):
- V_S is closed and the operators involved (P_lo = projection onto the lower band, HT =
  Hardy-Titchmarsh unitary scattering) are bounded; applying the finite-Euler transport
  equivalence V_S ~= V_semilocal (in-library) would pull a nonzero half-line witness back to
  V_S. The missing formal step is to exhibit the concrete element and prove its window
  non-vanishing: a genuine PSP/Sonin/Prolate-Slepian-type band limit element.

Verdict: the nonzero-outer-norm proof is COORDINATE-EXACT conditional on this single leaf;
the leaf is new PS-Sonin transcendental analysis, not assembly. The formal theorem with
witness remains OPEN. Until then the obligation module stays a build-clean Prop with zero
sorry/axiom, and the infinite-carrier Gate-3U readout for the {2} family stays OPEN
(docs/996, 997).

## 6. Next step toward closing the leaf

- Construct a concrete band element of V_S reaching (log-lambda, log-lambda+log 2) (a
  PSP/Sonin/prolate window function, or an eigenfunction of the finite-Euler transport
  pulled back through the equivalence), prove its L2 support and non-vanishing, seal the
  theorem with that witness.
RH not claimed.
