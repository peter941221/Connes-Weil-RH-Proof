# MEMORY.MD

Current route snapshot + rotating change log. Compressed 2026-08-27: full
history lives in git history, `docs/proofs/`, and
`_precompress_backup_2026-08-27/`. Working rules live in `AGENTS.md`.

## Current snapshot (2026-08-27)

- Route: C1 same-owner mainline, ROOT form (`[-log 2/2, log 2/2]`); design
  record `docs/proofs/1043`. RH NOT claimed.
- Committed frontier `13bae3d`: CC20 window-operator chain landed through the
  L2-kernel quotient lift (`applyKernelLp`, proof 1043 s6g-s6v). The generic
  equation-(121) engine is complete: uniform displacement bound, weighted
  correlation fold, Fubini discharge, operator-norm adapter.
- Pending commit (working tree): s6w/s6x square-window readback leaves -
  `pairing_applyKernel_windowedDisplacementKernel_eq_weightedCorrFold` and
  `norm_pairing_applyKernel_endpointKernelOnSquare_le_of_l1Weight` give the
  concrete endpoint owner `K_I` an L1 x L2 x L2 scalar pairing bound.
- Next bricks, in order:
  1. Concrete finite-rank difference profile `K_I - T`
     (`T = lambda * rankOne phi phi`) with certified envelope feeding eq-(121).
  2. Eq-(100) slope identity + GATE 1 numeric certificate (Yoshida rational
     LDL^T, or CC20 rank-one gamma ~ 2.94355 in `13 < 4*gamma/log 2 < 17`).
  3. Universal W4b / coverage root; capstone already formal:
     `sourceRH_of_rootSupportedHealthyDetectorData_and_endpointCertificates`.
- GATE 2 (Titchmarsh/Cartwright square-form bridge): deferred, not attempted.

Settled verdicts never to re-litigate:

- Bare whole-line HS premise is FALSE for every nonzero test (`bareHS_iff_zero_test`);
  plain-window cutoff trace family is an empty producer (docs/proofs/1016).
- Pure-analysis budget ladder cannot reach the ROOT window: true zero of the
  budget expression R* ~ 1.98e-3, and B(log 2) ~ +3.9 > 0 - only the endpoint
  theorem (vanishing orthogonality) closes the gap.
- Gate 2 (arithmetic-to-spectral equality) closed via center-2 contour assembly;
  Yoshida detector existence closed as a conditional consumer on the right half.
- Numerical eigenvalues/probe floats are NEVER transported into Lean.

Provenance for GATE 1 numeric certificates: Yoshida 1992 paywalled (class
C(a) = supp phi subset [-a,a] confirmed from preview); Bombieri 2000, "Remarks
on Weil's quadratic functional I" verified it at t = log(2)/2 - full text free
at bdim.eu (local extracted text under `/home/peter/blogs/bombieri.txt`; PDF
never committed). Recheck Bombieri eq-(7.3) normalization before transcribing.

## Change Log

- 2026-08-27 AGENTS/MEMORY : compressed both files to live-route essentials;
  full prior versions backed up under `_precompress_backup_2026-08-27/`.
- 2026-08-27 README : pushed status dashboard (commit 906bbd4).
- 2026-08-27 C1CC20WindowedPairingReadback(+Audit) : s6x - concrete K_I owns
  the eq-(121) L1xL2xL2 pairing bound; audits 2698 jobs, axiom-clean.
- 2026-08-27 C1CC20WindowedDisplacementReadback(+Audit) : s6w - window
  identity `K_I f = 1_I * K(1_I * f)` at raw and a.e.-quotient level; 2695
  jobs, axiom-clean.
- 2026-08-27 C1CC20FiniteRankApproximation(+Audit) : constructed the
  normalized Fourier rank-one projections, proved their square-window kernels
  lift exactly to `rankOne`, packaged equation-(119) `T` and its shared L1
  profile, and discharged equation (120) with automatic Fubini; 2700 jobs,
  axiom-clean.  Primary CC20 DOCX readback confirms 1732 paired alpha/d values
  (with an unpaired terminal angle sentinel 1733), but a rigorous equation-(115)
  certificate still needs strict lambda data, the 11-term chi formula/remainder,
  and certified absolute-value integration.  The fixed-window feedback cost
  `C(R)` has no definition or quantitative producer in the tree, so that route
  is not yet formally closed or rejected.
- 2026-08-27 C1CC20NegativeIndex(+Audit) : proved without numerical input that
  positivity of the endpoint defect form on one linear-functional kernel
  forces every strictly negative complex subspace to have finrank at most one;
  specialized the functional to the CC20 Riesz bad direction; 3617-job paired
  batch axiom-clean.
- 2026-08-27 C1CC20EndpointSpectralOwnerGuard(+Audit) : proved the existing
  endpoint spectral owner permits arbitrary replacement of `analyticModeDeriv`
  while preserving all its other certificate fields, so it cannot honestly
  produce endpoint positivity without lower analytic laws; 3617-job paired
  batch axiom-clean.
- 2026-08-27 C1CC20EndpointAnalyticModeData(+Audit) : added the minimum genuine
  derivative owner and proved derivative uniqueness plus a negative replacement
  guard; this closes the arbitrary-derivative defect without storing endpoint
  positivity as source data; 2562-job paired build axiom-clean.
- 2026-08-27 six leaf pairs committed in five coherent commits (ff29431..
  4f00d51) after SHA-verified WSL replay audit; docs/proofs/1043 gained section
  6y : Bombieri-2000 scope-check GO at t = log 2 / 2, normalizations (7.1)-(7.5)
  captured elementary/digamma-free, Theorem 12 ruled out as a producer
  (constant -1.29 - O(1) at our window), Theorem 8/Lemma 10 flagged
  conditional-only.
- 2026-08-27 scan located (`~/bombieri_weil_qf.pdf`, out of repo, 53 pp) :
  (7.1) sign erratum fixed (MINUS between the cosines; text layer was lossy),
  K* definition and completed Lemma-10 Gram identity certified by visual read
  plus numerical triangle closure (worst 8.9e-16); doc 1043 §6y rewritten in
  place; engine README provenance refreshed to make Bombieri sec-7 the
  transcription source.
- 2026-08-27 C1BombieriSection7Readback(+Audit) : first Lean slice of the
  Bombieri sec-7 lane - bombieriK (sinc with removable value 1 at 0),
  bombieriKstar verbatim from book p.203, and the master re/im split lemma
  for K on any `a + b*I`; 1507-job build axiom-clean
  (`[propext, Classical.choice, Quot.sound]`, no sorryAx); real-arg and
  pure-imag special cases plus the (7.1)/(Lemma-10)/(7.2)-(7.5) identities
  are the next slices.
