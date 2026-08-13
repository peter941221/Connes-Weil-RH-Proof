# 998 - OUTER channel: nonzero radial-complement of the metric coframe on the {2} family

Date: 2026-08-11. Status: conditional paper derivation plus a typed Lean
obligation. Neither the strip identity nor the nonzero outer channel is yet a
Lean theorem; the Sonin-window witness is also open.
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
subspaces (docs/815), a Lean proof of Outer != 0 would refute the canonical
infinite-carrier Gate for that family. This document derives the intended
coordinate implication; it does not prove the operator statement in Lean.

## 1. Candidate coframe action near the band edge (paper derivation)

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
   (T^dag T x)(t) = - c_2 @ x(t + log 2).            [paper algebra]

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
contains an element whose restriction to
`(log-lambda, log-lambda + log 2)` is nonzero in `L2`.

The coordinate calculation proposes the conditional implication from this
restriction statement to outer leakage. It does not prove that every nonzero
element of `V_S` reaches every window. That implication needs a separate
determining-set or unique-continuation theorem.

The finite-Euler transport is a continuous-linear equivalence onto the
semilocal Sonin space (`ccm24FiniteEulerTransport_maps_sonin`,
`SemilocalFourierSupport.lean`). It transports a verified witness but does not
manufacture one. A concrete PSP/prolate witness remains the required analytic
input.
Assumption table:
- Proven, repo: D = Ambient o J o GInv, GInv bijective on V_S,
  J isometry, radial projection geometry, the family structure, J^dag D = I.
- Paper-only: the shift/coframe depletion stripe and its restricted-L2
  consequence. These still need Lean lemmas respecting `Lp` a.e. equality,
  translation, projection readback, and the finite-Euler product at `{2}`.
- THE REAL ANALYTIC LEAF: an element of `V_S` with nonzero `L2` restriction
  on `(log-lambda, log-lambda+log 2)`. The library equivalence can transport an
  explicit witness; it does not supply one.

## 3. Choosing w completes the bound

Conditionally on both the strip theorem and a witness `u0` in `V_S` with
nonzero `L2` restriction on the window, take the input vector
w := finiteEulerGram u0  (the inverse of finiteEulerGramInv, so that
finiteEulerGramInv w = u0).  Then x := J (finiteEulerGramInv w) = J u0 = u0 in V_S is
nonzero after restriction to the window. By the strip-exact identity (1), ((I-R) D) w equals
-2^{-1/2} * (u0 shifted right by log 2) almost everywhere on
(log-lambda-log2, log-lambda) -- a nonzero L2 element, since t -> t+log2 is a bijection
there.  Hence (I-R)D is nonzero on the source vector w, so its operator norm > 0.

Numeric cross-check: docs/884 reports ||(I-R) o D|| ~ 0.62 on log-l in [-2,2].
This supports the direction but is not a proof of the positive lower bound.

## 4. Status and next Lean step

- The coordinate identity above is not formalized. The obligation module
  `Dev/OuterTwoNonzeroObligation.lean` (`twoOuterNonzeroObligation`, with `twoFamily`
  carrying the prime term `(2,1)` and `twoFamily_memTerm`) builds axiom-clean on WSL
  (`lake build ConnesWeilRH.Dev.OuterTwoNonzeroObligation`: 3315 jobs, exit 0; `#print axioms`
  on its proved declarations = `[propext, Classical.choice, Quot.sound]`). The
  `twoOuterNonzeroObligation` declaration is a `def ... : Prop`, not a proof.
- Still OPEN: first formalize the strip/restriction implication; then construct
  the Sonin-band witness of section 2, an explicit element
  of `V_S` with nonzero `L2` restriction on `(log-lambda, log-lambda+log 2)`, pulled back through the
  finite-Euler semilocal-Sonin equivalence. Both pieces are required before the
  positive lower bound becomes a theorem.

RH not claimed. No new axiom/sorry.

## 5. Honest status: the Sonin-window witness is a real analytic leaf

The coordinate identity of section 1 is a paper derivation, not a closed Lean
theorem. The second gap is the existence of an element of the Sonin carrier
`V_S` with nonzero `L2` restriction on the shifted window. This
section records precisely what is proven in-library, what is a plausible-but-unformalized
operator argument, and what is genuinely open.

Proven / in-library (no project axiom):
- D = Ambient o J o GInv with GInv bijective on V_S and J an isometry;
  `twoFamily` is the concrete family `{(2,1)}`; the radial/Sonin projections and
  finite-Euler operators are defined.
- `V_S` is a closed Hilbert subspace. Nontriviality alone does not imply nonzero
  restriction to a particular window; a determining-set theorem would be needed.

Open formal bridge:
- Prove the `{2}` finite-Euler shift identity a.e. on the strip and transport a
  nonzero restricted norm through translation and scalar multiplication.
- Construct a Sonin carrier element and prove its restricted norm is nonzero.

Verdict: the nonzero-outer-norm route has two open pieces, a Lean operator bridge
and a PSP/Sonin witness. The obligation module only fixes the target type. The
infinite-carrier Gate-3U readout for the `{2}` family remains open.

## 6. Next step toward closing the leaf

- Formalize the `{2}` strip identity and its restricted-L2 implication.
- Construct a concrete band element of V_S with nonzero restriction to
  `(log-lambda, log-lambda+log 2)` (a PSP/Sonin/prolate window function, or an
  eigenfunction pulled back through the equivalence), prove its `L2` membership
  and nonzero restricted norm, then seal the operator theorem with that witness.
RH not claimed.
