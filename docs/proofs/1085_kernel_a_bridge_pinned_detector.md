# 1085 - consumer #3 kernel (a) IS the record-1080 scalar gate

Date: 2026-09-01.  Follows 1084 (anchor collapse onto one test).  Advances
consumer 3 kernel (a): unifies its open inequality with the consumer-2/3
handoff gate of record 1080.

## 1. What landed (`ConnesWeilRH/Dev/C1HealthyDetectorKernelABridge.lean`)

1. `convolutionSquare_negTest`: pointwise negation of the test leaves the
   Hermitian square pointwise unchanged - `star (-z) * (-w) = star z * w`,
   the two minus signs cancel inside the quadratic integrand.
2. `archimedeanNumerator_negTest` / `archimedeanIntegrand_negTest` /
   `archimedeanTerm_negTest`: the archimedean term of the square is
   INVARIANT under pointwise negation of the test (pure congruence, no
   integrability input - the same mechanism as record 1084's scaling).
3. `exists_pinnedDetector_of_kernelAInterpolant` - THE BRIDGE.  For every
   off-line source zero there is an explicit pair `(h, g)` such that:

   * `h` is the 7-node symmetric interpolant of records 1083/1084: root
     window `(-log 2 / 2, log 2 / 2)` support, triple vanishing on
     `{0, 1/2, 1}`, and detection with the EXACT value `1` at `rho`
     (1084 only exposed `≠ 0`; the target-value lemmas give the value);
   * `g = negTest h` is a PINNED detector in the record-1080 sense:
     `HealthyMinimalLaplaceRealizes rho g`, detection value `-1`, support
     radius `log 2 / 2`, and `globalPrimeIndexSet g.convolutionSquare = ∅`
     (both 1080 transport lemmas apply verbatim);
   * `selectedDetectorArchimedeanGate rho g ↔ 0 < arch h.convSq` (the
     negation invariance of item 2) - the two "open inequalities" of the
     post-1084 frontier and of record 1080 are THE SAME Prop; and
   * `0 < arch h.convSq → HealthyYoshidaDetectorData rho g` - the anchor
     positivity yields the full healthy-detector package through the 1080
     handoff iff, on an explicitly pinned detector.

## 2. Structural verdict (honest)

The architecture is now a single unduplicated chain: records 1080/1082/
1083/1084/1085 all land on ONE object and ONE inequality.

    7-node interpolant h  (explicit, per off-line zero)
      lap h = 0 on {0, 1/2, 1},  lap h rho = 1,  supp h ⊆ (-log2/2, log2/2)
    g := negTest h        (pinned detector, 1080 spec: value -1, ∅ primes)
    OPEN:  0 < arch h.convSq  ↔  selectedDetectorArchimedeanGate rho g
      ⟹  HealthyYoshidaDetectorData rho g

Nothing was proven about the inequality itself - the numerical content is
still exactly the 1077-1079 measured object (fl2 = -1.294, sink 33.78%).
What changed: kernel (a) no longer lives beside the record-1080 gate as a
parallel formulation; they are provably the same obligation on the same
explicit witness, and its discharge pays out the full detector package.
Kernel (b) (prefix-side wall) remains untouched.  RH is NOT claimed.

## 3. Build evidence

WSL ext4 mirror through the resource runner
(`build-logs/kabridge_build1.log`):

    Build completed successfully (3653 jobs).
    zero `^error:` lines; zero `sorryAx`.

Focused axiom audit (`C1HealthyDetectorKernelABridgeAudit.lean`, same
log) - all five pinned statements depend on exactly the three standard
axioms `[propext, Classical.choice, Quot.sound]`:

    convolutionSquare_negTest            OK
    archimedeanNumerator_negTest         OK
    archimedeanIntegrand_negTest         OK
    archimedeanTerm_negTest              OK
    exists_pinnedDetector_of_kernelAInterpolant  OK

## 4. What is NOT here

No proof of `0 < arch h.convSq` for any test; no g_3-family object (the
1077-1079 program remains the numeric blueprint for the remaining
inequality); no prefix-side (kernel (b)) progress; capstone premises
unchanged.
