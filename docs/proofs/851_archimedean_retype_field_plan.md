# 851 — Re-typing `RouteInputs.cc20.archimedeanSymbols` onto the CompactLog carrier: a field-by-field plan

Date: 2026-08-07 · Status: source-verified structural plan (no new build). This is the
concrete first step of 850's "re-type onto the CompactLog carrier" — not a proof, not an
RH claim, but the exact bill of fields that must be instantiated, with, for each one, the
existing repo object/theorem that fills it or the honest GAP that requires new analysis.

## 0. 先讲结论

850 showed the additive "endpoint sign" was a fake problem; the real positive content is
already present on the `CompactLogTest` carrier. 851 turns that into a **constructive
checklist**: of the 11 fields in `ArchimedeanTraceSymbols`, **6 are already anchored by an
existing repo theorem** (gate, trace-class, positive trace, `Test`), and **5 are Propositions**
that this carrier must still furnish** — but the hard one (the Mellin product law)
is ALREADY proved, axiom-clean (§6); what remains is wiring it onto the route
and the normalization conventions.

```
ArchimedeanTraceSymbols
 ├─ data-ish (4) : Test, supportSquareTrace, sourceNoDefectTrace, positiveTrace   (Test→ℝ/Type)
 ├─ gate (3)     : traceClass, cyclicLegal, hilbertSchmidtGate   (Test→Prop)
 └─ convention   : mellinHalfDensityMatched, uInfinityNormalized, qduNormalized,
                   archimedeanSignNormalized                               (Prop)
```

## 1. The gate that must hold on this carrier

`ArchimedeanTraceSymbols` wraps the whole CC20 archimedean contract. The two committed
consumers (the RH aperture) are:

```
TraceSquareStatement A = ∀g, traceClass g → cyclicLegal g → supportSquareTrace = sourceNoDefectTrace ∧ 0≤positiveTrace
TraceClassTemplate   A = ∀g, hilbertSchmidtGate g → traceClass g ∧ cyclicLegal g
OrdinaryTraceSquare  A = ∀g, traceClass g → cyclicLegal g → positiveTrace = supportSquareTrace
```

So the *positive* gate (the only one 850 wanted to keep) is `0 ≤ positiveTrace` with
`positiveTrace = supportSquareTrace`. On `CompactLogTest` that is, by construction,
`∫‖g‖²`-like — the additive-counterexample freedom is gone.

## 2. Field-by-field map

| `ArchimedeanTraceSymbols` field | type | how the CompactLog carrier supplies it | repo anchor | status |
|---|---|---|---|---|
| `Test` | `Type` | `CCM25Concrete.CompactLogConvolution.CompactLogTest` | `CompactLogConvolution.lean` (imports resolve) | READY |
| `hilbertSchmidtGate` | `Test→Prop` | the A3 windowed detector being self-adjoint + HS-trace-class along a Hilbert basis; **nonzero** witness exists | `A3.hsGate_selfAdjoint_witness`, `A3.hsGate_traceClass_witness`, `A3.nonzero_hsGate_witness` | READY (carrier proof, axiom-clean) |
| `traceClass` / `cyclicLegal` | `Test→Prop` | derive from `hilbertSchmidtGate` via `TraceClassTemplateStatement` | `Basic.lean` (rfl-level) | derivable once gate is set |
| `positiveTrace` | `Test→ℝ` | `∫ g‖²`-type: `convolutionSquare(0) = ∫‖g‖² ≥0` and `⟨u,F†Fu⟩=‖Fu‖²≥0` | `CompactLogConvolution:154/176`, `A3.detector_diagonal_re_nonneg` | READY |
| `supportSquareTrace` | `Test→ℝ` | must be the **true half-density square** (Mellin of `g*⋆g`) in log coords | **need: convolution MELFIN** `g*⋆g`, not additive `M(conv²)=2M g` | GAP (new analysis) |
| `sourceNoDefectTrace` | `Test→ℝ` | the no-defect side; equal to `supportSquareTrace` on the trace-class side | `TraceSquareStatement` (recall) | GAP (follows from above) |
| `mellinHalfDensityMatched` | `Prop` | the strong (multiplicative) Mellin half-density law; its proof ALREADY EXISTS, axiom-clean, in `Dev/MellinConvolutionIdentity` / `MellinProductCarrier` | additive `2=1` still refuted (YoshidaConstruction:2727); law lives in the parallel carrier | WIRING (see §6) |
| `uInfinityNormalized` / `qduNormalized` / `archimedeanSignNormalized` | `Prop` | normalization conventions expressed on the Compact hull | `SignsAndNormalizationsStatement`; most requires unpacking | TO FILL (convention) |

## 3. The real remaining work is WIRING, not the Mellin identity (see 6)

This re-type used to look like one new analytic object (a multiplicative
half-density Mellin square).  It is not: the Mellin product law is already proved,
axiom-clean, in `Dev/MellinConvolutionIdentity` / `Dev/MellinProductCarrier` (6).
The additive model's failure (`M(g*g)=2M g`, `2=1`) is real and stays outside the
picture; the faithful carrier for the Mellin product law already exists.  So the
winning fields of `ArchimedeanTraceSymbols` (`mellinHalfDensityMatched`,
`sourceNoDefectTrace`, and the positive trace) become a wiring/shelf task: give
`MellinProductCarrier.Test` the HS structure, hook the identity into
`mellinHalfDensityMatched`, and route the result into the Yoshida detector.

## 4. Next executable step

1. On a clean image (current images are stale/dirty; see §8), instantiate the **ready**
   and **derivable** fields first (`Test`, `hilbertSchmidtGate`, `traceClass`,
   `cyclicLegal`, `positiveTrace`) to get the outer `0≤ positiveTrace` gate.
2. Open the wiring step as a named theorem: `MellinProductCarrier`'s already-proved
   Mellin product law (§6) is hooked into `mellinHalfDensityMatched` and the Yoshida
   detector; if the wiring conflicts structurally, record that as honest failure (§12).

## 5. Honest scope

No RH claim, no build run, no closed blocks. 851 is the field-level of the re-type: it
tells exactly which fields are concrete-ready (6-ish) and which needed fields are wired and which is wiring residue (the Mellin law is already
proved, §6; only its connection to the route remains). The next round must verify this against
a clean build; the current dirty/stale mirrors cannot supply that evidence (§5/§8).



## 6. Correction on 2026-08-07: the multiplicative Mellin product law already exists (do not reinvent it)

850/851 cited the "multiplicative half-density Mellin square" as a genuinely new analysis
gap.  BUILD-CONFIRMED 2026-08-07: both `mellin_log_convolution_product` and
`mellinConvolutionProductLaw` compile in a WSL mirror and are axiom-clean
(`#print axioms` = [propext, Classical.choice, Quot.sound], no sorryAx).
  That marking is now OUTDATED.  The product law is ALREADY proved, axiom-clean, in
`ConnesWeilRH/Dev/MellinConvolutionIdentity.lean` (`mellin_log_convolution_product`) and
packaged as a carrier in `ConnesWeilRH/Dev/MellinProductCarrier.lean`
(`mellinConvolutionProductLaw`).  Those realize steps 1-2 of
`docs/proofs/setup/plan-mellin-convolution-identity.md` (a previously-unbuilt plan);
`docs/proofs/setup/design-parallel-source-model-consensus.md` frames this as the parallel
"Route A" re-type.  Neither module is imported by the Route/`ArchimedeanTraceSymbols` line.

REVISED gap (smaller and concrete, not original analysis): wire this existing
Mellin-product carrier into the route.
  (a) Give `MellinProductCarrier.Test` the trace/HS structure (`{ log : ℝ → ℂ }` only,
      integrability kept as terminating witnesses);
  (b) set `ArchimedeanTraceSymbols.mellinHalfDensityMatched` via this identity;
  (c) feed the Mellin-processed test into the Yoshida detector / criterion that the
      additive "we-chair" was serving.
If (a)-(c) wire, the 850/851 (b) gap collapses to plumbing; if they conflict, record it
as honest structural failure per AGENTS-x12.
