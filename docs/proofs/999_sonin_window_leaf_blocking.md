# 999 - BLOCKING STATEMENT: the Sonin-window leaf (Gate-3U {2} outer != 0)

Date: 2026-08-12. Status: CONCLUSIVE blocking statement on closed-form assembly; the
underlying claim is mathematically TRUE but NOT formalizable in this repo at mathlib
v4.30.0 without new real analysis. RH NOT claimed. No new axiom / sorry.

This document pins, by name, the exact irreducible analytic premise behind docs/998, why
no existing library declaration meets it, and what a standalone module must seal before
the obligation twoOuterNonzeroObligation can become a theorem. It is a blocking verdict on
the assemble-by-existing-theorems route; it is not a refutation, and not a done claim.

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

Because the {2} ambient `T adjoint T` acts on the radial band by
`(T adjoint T x)(t) = -(2^-1/2)*x(t+log2)` on the strip (log-la - log2, log-la) for x in
RadialSupport, the obligation collapses exactly to:

    exists u in V_arch : u has nonzero L2 mass on the window
        W = (log lambda, log lambda + log 2).

See docs/998 for the coordinate derivation; that identity is exact and closed.

## 2. Why window-reachability is genuine new analysis (not closed-form assembly)

A closed subspace of L2(log lambda, +oo) avoids an open window only if it sits inside
{u : u = 0 on W}, i.e. the restriction map V_arch -> L2(W) vanishes. For the Sonin /
Hardy-Titchmarsh half-line model (analytic conjugate also half-line), W is a determining
set: the restriction is injective, so V_arch reaches W iff V_arch is nonzero.

Every step is classically true, and EVERY one is absent from mathlib v4.30.0 today:
  - nonzero of V_arch: only the transport equivalence gives V_arch =~ V_semilocal, which
    transports nonzero-ness but never manufactures a specific element;
  - determining-set / analytic-conjugate Hardy space: no such lemma in mathlib.

Repo-wide search (all CCM24*Sonin*, CCM24HardyTitchmarsh, CCM24SemilocalFourierSupport,
CCM24LogRadialSupport) finds NO example / witness member of any Sonin space. The
parameterized modules only rotate the involution through transport; they never build an
element. So there is no library witness to reuse.

## 3. What a standalone module must do (irreducible work)

A future `Dev/SoninWindowWitness.lean` must:
  1. exhibit a concrete u0 : sourceSoninCarrier lambda, with 0 != u0 and u0 nonzero on W;
  2. prove u0 in V_arch from the defining predicates (support at log lambda and the
     Hardy-Titchmarsh conjugate support at log lambda);
  3. prove a nonzero norm / inner-product against the indicator of W.

The required ingredients - a nonzero generating element of V_arch, and the Titchmarsh /
Paley-Wiener determining theorem for V_arch - are not shipped by this repo or by mathlib.
They are many sessions of new real analysis. The claim is true and buildable, just long.

## 4. Status

OPEN analytic target (not an assembled leaf). Blocked for closed-form / single-session
assembly only; NOT marked dead (not refuted). The verified side remains axiom-clean in
`Dev/OuterTwoNonzeroObligation.lean` and docs/998. For the infinite-carrier Gate-3U {2}
readout: the object stays NOT certifiable under current defs until the window witness is
built (docs/996, 997 negative-numerics side; docs/998/999 exact-identity side).

RH not claimed.
