# 860 — Gate-3U tail trace-assembly roadblock verdict

Status: verdict (no sorry / no axiom). Date: 2026-08-07. Lane: Gate-3U trace bridge.

## What this is

A check that the single remaining Gate-3U open piece — turning the closed housing
operator-norm tail bound

    norm_inverseLowerFactorPhysicalRenewalTailResponse_le_const_exp   (TailBound.lean:751)

into a trace bound

    hdecay : |(ordinaryTraceAlong sourceBasis (inverseLowerFactorPhysicalRenewalTailResponse ...)).re| <= bound

consumed by canonicalRealGate3UnAt_of_tailNormBound (TailBound.lean:163) — has a
constructible Lean bridge. Endpoint: it does NOT, on the current carrier, because the
tail operator has no provable trace-class certificate with the tools in-library.

## Evidence (each item has a file/line)

| fact | evidence |
|---|---|
| carrier is a closed Sonin subspace of finite carrier = L2(log) | sourceSoninCarrier := ccm24ArchimedeanSoninClosedSubspace.toSubmodule (FrameGramCalculus), finiteSCarrier := cc20GlobalLogCrossingL2 (ProjectionTrace:73) |
| detector = positive convolution = conjugate Fourier multiplier | cc20GlobalConvolutionPositive h = (cc20GlobalLogConvolution h)^{adj} comp (…) ; log-convolution = F^{-1} * multiplier * F (GlobalLogConvolution:43) |
| Fourier-multiplier on infinite-dim L2 is neither compact nor HS nor trace-class | analysis standard ; no in-library instance anyway |
| renewal multi-index is infinite (a nat count per visible prime) | FiniteEulerRenewalIndex := PUnit | Nat × (…), MultiRenewal:28-31 |
| forward multi-index is finite | FiniteEulerForwardIndex := PUnit | Bool × (…) with Fintype instance (ForwardRenewal:43-48) |
| tail response = finite forward sum | infinite renewal tsum | inverseLowerFactorPhysicalRenewalTailResponse (RenewalSupportSplit:251) |
| repository bans trace-sum interchange on the tail | §6 guard: coefficient support ≠ trace support (807 boundary); no trace moves in renewal module |
| no op-norm → trace inequality in repo | "the only HS/markers checked" scan |
| no finite-dim/Noneempty instance for the carrier is present; it is constructed as a closed submodule intersection | search of whole Source+Dev for FiniteDimensional / Nonempty on Son carrier : no hit |

## Conclusion

Combined: the raw renewal *tail* operator is a 	sum over an infinite Nat multi-index
sandwiched around an L2 Fourier-multiplier (the detectorOperator = A†A) that is neither
compact nor Hilbert—Schmidt nor trace-class on the uncompressed carrier. No in-library
IsTraceClassAlong source, no nuclear/HS bound, and no finite-basis instance on the
carrier gives the trace bound. Hence Abs(Re Tr tail) <= bound can be stated, but not
proved to any positive content with the current declarations.

This is a route judgment change: the "tail operator-norm decay → trace" hopeful step is
blocked at the object layer, consistent with the earlier Slepian/prolate verdicts
(see 817-824, 842-843).

## Not claimed (honesty)
- We did NOT prove the carrier is uninhabited; we only report that no finite carrier
  basis / trace-class certificate for the raw *tail* is directly given.
- This claim is the *raw* renewal *tail*. The *prolate* layer is a DIFFERENT carrier
  lane (semi-infinite band), which has its own trace-class machinery (see below).

## Corrected route (2026-08-07, discovered during this turn)

The original judgement ("trace-assembly impossible") is too strong. Reading
`CCM24SourceProlateTrace.lean` shows the library ALREADY carries a prolate-class
trace-classification bundle for detector-sandwich operators:

- `sourceProlateRemainder` = `sourceFourierSupport composed (radialSupport - sourceSonin)` is
  Hilbert--Schmidt (summable `|norm|^2`) as soon as its own `IsTraceClassAlong` is granted
  (`sourceProlateHilbertSchmidtFactor_summable_of_isTraceClassAlong` : 74).
- `sourceProlateCommutator_isTraceClassAlong` (:157) and
  `sourceThreeBranchCommutator_isTraceClassAlong` (:299) already decide
  `IsTraceClassAlong ... (commutator (sourceProlateRemainder lambda) (detectorOperator owner))`.

So the single missing step is NOT "build nuclear-trace theory from scratch".  It is to
**wire the raw renewal tail's own trace-class certificate** to a certificate already in
that bundle (i.e. connect `? Globally (tail)` to `sourceProlateComplementary` / commutator
facts).  That is a genuine, project-owned, winnable lemma — not an open-analysis dead
end.

## Blocked (2026-08-07, final)

A full Sync of this turn's exploration: the tail side already has its operator-norm bound
(norm_inverse...TailResponse_le_const_exp, axiom-clean per TailBoundAudit). What is missing is
`hdecay : |Re Tr tail| <= bound`, which needs an `IsTraceClassAlmost basis tail` certificate
on the **Gate carrier** (`sourceSoninCarrier`). The library trace-class machinery
(`CCM24SourceProlateTrace.lean`) is closed and axiom-clean, but it lives on `finiteCarrier` /
`globalBasis`, NOT on the Gate carrier. The AGENTS `A1/A2` seam (SourceTestAlgebra forces a
LegacyTestEquiv full bijection / carrier type mismatch) is a STRUCTURAL blocker: no transfer
from global-basis trace-class to Gate-carrier tail exists, and the seam is documented
incompatible. Repointing the carrier is an architecture-level decision (§3b/§6: needs Peter).

So this specific "打穿 3U" road is BLOCKED at the object layer until either:
  (A) Peter authorizes a Gate carrier re-point to a Hilbert--Schmidt/finite-rank basis, or
  (B) a genuinely new analytic bound (Slepian/prolate nuclear trace bound) that the
      current projective model cannot express is supplied.
None of that is constructible under the current declarations, so the Gate remains open.
