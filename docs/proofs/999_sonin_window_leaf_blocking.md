# 999 - BLOCKING STATEMENT: the Sonin-window leaf (Gate-3U {2} outer != 0)

Date: 2026-08-12. Status: the library-assembly route is blocked. The required
analytic statement remains open in this repository. RH is not claimed. No new
axiom or `sorry` is added.

This document pins the analytic witness behind docs/998. The audit also found
that docs/998's strip identity has not yet been formalized, so the witness is
not the only remaining Lean task. This is not a refutation or a done claim.

## 1. The claim to close (recap, exact)

For a physical Sonin scale `lambda` and the concrete non-empty finite family
`twoFamily = { (2,1) }` (prime 2), the build-clean obligation is:

    theorem twoOuterNonzeroObligation lambda :
        sourceOuterCoframeLeakage lambda twoFamily != 0

with
    sourceOuterCoframeLeakage = (id - radialSupportProjection lambda) o metricCoframe
    metricCoframe            = finiteEulerAmbientGram o sourceInclusion o finiteEulerGramInv

Inputs range over:
    sourceSoninCarrier lambda = (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule

The archimedean Sonin space on the log carrier `Lp CC 2 volume` equals
`RadialSupport lambda INTER FourierSupport lambda`, where
    RadialSupport             = { u = 0 on t < log lambda }
    FourierSupport            = { HardyTitchmarsh u in RadialSupport }
    HardyTitchmarsh           = FT^-1 o (phase * reflection) o FT   (involutive unitary).

The paper calculation in docs/998 says that the `{2}` ambient `T adjoint T` acts on the radial band by
`(T adjoint T x)(t) = -(2^-1/2)*x(t+log2)` on the strip (log-la - log2, log-la) for x in
RadialSupport, the obligation collapses exactly to:

    exists u in V_arch : u has nonzero L2 mass on the window
        W = (log lambda, log lambda + log 2).

See docs/998 for the coordinate derivation. It remains to be proved in Lean,
including its a.e. and restricted-L2 consequences.

## 2. Why window-reachability is genuine new analysis (not closed-form assembly)

A closed subspace of `L2(log lambda, +oo)` can vanish after restriction to an
open window. The desired statement is that the restriction map
`V_arch -> L2(W)` has a nonzero value. A determining-set theorem would imply
this from nontriviality of `V_arch`, but the repository has not proved either
the determining-set theorem or the required nontriviality.

The repository currently lacks:
  - a concrete nonzero `V_arch` element;
  - a determining-set / unique-continuation theorem for the relevant Hardy model;
  - a proof that a proposed witness has nonzero restriction to `W`.

Repo-wide search (all CCM24*Sonin*, CCM24HardyTitchmarsh, CCM24SemilocalFourierSupport,
CCM24LogRadialSupport) finds NO example / witness member of any Sonin space. The
parameterized modules only rotate the involution through transport; they never build an
element. So there is no library witness to reuse.

## 3. What a standalone module must do (irreducible work)

A complete closure must:
  1. formalize the `{2}` finite-Euler strip identity and prove that nonzero
     window restriction implies nonzero outer leakage;
  2. exhibit a concrete `u0 : sourceSoninCarrier lambda` with nonzero
     `L2(volume.restrict W)` restriction;
  3. prove u0 in V_arch from the defining predicates (support at log lambda and the
     Hardy-Titchmarsh conjugate support at log lambda);
  4. prove that `soninWindowRestriction lambda u0 != 0` and consume it in the
     operator bridge.

The required ingredients are not shipped by this repo or mathlib. A prolate
construction is a candidate, but it needs a formal carrier transport and a
restricted-norm proof before it can close this leaf.

## 4. Status

OPEN analytic target (not an assembled leaf). Blocked for closed-form / single-session
assembly only; NOT marked dead (not refuted). The typed family and target Prop are
axiom-clean in `Dev/OuterTwoNonzeroObligation.lean`; docs/998 is not a Lean theorem.
For the infinite-carrier Gate-3U `{2}`
readout: the object stays NOT certifiable under current defs until the window witness is
built (docs/996, 997 negative-numerics side; docs/998/999 exact-identity side).

RH not claimed.
