# RFC — R1/C1 route to L1552: where the non-arithmetic assembly ends and L653 begins

Status: planning (not a proof).  RH NOT claimed.

## 1. What R1 is
R1 is the route-C/C1 exit: construct a `FullWeilPositivity` witness so the
`SourceRouteTraceData`-backed `CC20PropositionC1SourceCriterion` trigger a
`SourceRH`.  It's the B-lane main axis (memory 916: A and B both pivot on the same
L653 wall).

## 2. What is PROVEN now (axiom-clean, via 979/980/981 on the CompactLog carrier)

| Step | What's closed | Proof |
|---|---|---|
| R1-1 | object shape: `ArchimedeanTraceSymbols` w/ `Test := Compact`, `positive = Re(arch)` | 979 |
| R1-2 | HS operator gate is uniform over `g`; `bumpPlateauTest` carries both gate & positivity | 980 |
| R1-3 | full CC arch symbols w/ `positive = (Re arch)²`, all 5 non-L^2 obligations | 981 |

The archimedean side of `SourceRouteTraceData` (hilbertSchmidtGate, positiveTrace,
traceClassTemplate, ordinary-trace) is essentially assembled. What's blocked:

## 3. The remaining seam: `ccm25ArithmeticPackage` = L653

`ConcreteCCM25ArithmeticPackage` (Package.lean:27) has `rows :
ConcreteCCM25ArithmeticRows`, whose **load-bearing field** is
`finitePrimeArithmeticCertificates :
FixedLambdaArithmeticSourceTestCertificatesForAllTests` (Rows.lean:51).  This is the
"arithmetic package" feeding `L653 = normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot`
(UnconditionalSkeleton:653).  Memory 916/918 pin it as the shared A/B pivot.

### What L653 actually is (current read)
It's the `FixedLambda` certificate family quantifying over ALL source tests `∀ f g`.
Per 916c, on the concrete `{2}` model with `archimedean ≡ 0`, the cerfificate
arrows are structurally refutable at the composites (a `∀ n` demands
`IsPrimePow n` which fails at `n=1` / composites).  Per 849/848, the per-F carrier
Data rows ARE constructible; what's open is the `∀ f g` certificate family over ALL
tests + the finite-prime atoms lattice that satisfy `multiplicativeMellin`.

## 4. Options for the real bill

| Option | What it does | Verdict |
|---|---|---|
| **A. Re-type `archimedeanSymbols` to Compact + assemble `RouteInputs`** | RouteInputs needs `SemilocalModelSymbols`+`CCM25Interface`+`CC20Interface` on `R1ArchimedeanSymbols`; then `testAndQuotient`/`fixedSSupportTransport` buildable. | Assembly proceeds, but does NOT make `L653` provable — the finite-prime certificate family still bottom. |
| **B. Attack L653 directly: build certificates on a real multiplicative carrier** | Since `convolutionStar = additive` on the concrete model makes Mellin double-not-square (915 §12), make `FixedLambdaArithmeticSourceData` on a genuinely multiplicative-convolution carrier (`log ℝ→ℂ` log-carrier). Mellin route (Memory 918) already has axiom-clean `squareLaw`/`two_term>0`. | The real R1-core: give the arithmetic package a genuinely multiplicative carrier + a nontrivial prime. |
| **C. Skip L653, use `Route.FullWeilPositivity` constructively from the Mellin free chain** | If the witness is fed from Mellin rows (square-law + prime-2), avoiding the L2 package's `∀ f g` family. | Deviation from how skeleton wires the C1 — may not trigger L1552 as configured. |

## 3. Recommendation
Option B is the only one that turns the arithmetic package from an axiom into a proof.
A de-risking path:
1. Prove `FixedLambdaArithmeticSourceData` for a SINGLE test (not `∀ f g`) on the
   Mellin carrier first (parallel of `ConcreteP1SupportProbe` / `MellinFullRecord`),
   with real prime-2 finite-prime term.
2. If a single-test certificate holds, lift to the fixed-lambda family.
3. Port the whole assembly (980/981 + arithmetic) into the `SourceObjectPackage` /
   `CC20RouteRealization` pipeline.

## Remaining honest gap
- L653 (L1-arithmetic) is a REAL arithmetic bottom, not a Lean-assembly leaf.
- Even if L1 certifies, `L1552` C1→RH needs the `FullWeilPositivity` witness, which
  also has `ledgersCleared`/`fixedSPositiveTraceReadOff` closure steps.

So R1's "remaining" = build the certificates on a genuinely multiplicative carrier
(Option B) + assemble the witness. Both finite and buildable, but the certificate
field is the load-bearing wall.