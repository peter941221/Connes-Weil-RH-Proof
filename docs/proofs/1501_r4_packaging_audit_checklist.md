# 1501 — R4 pre-audit: the RH exit packaging checklist

**Status: AUDIT CHECKLIST (zero new Lean).** This record pins, before any R4
attempt, the exact composition chain, the anti-circularity obligations, and
the final-claims audit procedure for the G8 exit. It answers work-order step
4. RH is not claimed; the wrapper is blocked on the two open items of record
1500 (ρ4 endpoint trace limit, ρ5 same-owner identification).

## 1. The committed chain (all FORMAL, verified this session)

```text
D1  C1HealthyYoshidaSpectralNegativity.lean:611
      one same-detector qw >= 0 fact refutes a right-hand off-line zero
D2  C1P2DefectControl.lean:644-647
      the zero supplies a healthy detector with support + visible-prime audit data
G1  SelectedWeilSquare.lean:36-52
      every CompactLogTest g has the canonical owner ofCompactLogTest g
G2  C1SameOwnerWeil.lean:220-221
      (ofCompactLogTest g).sourceTest = g definitionally
G3  C1G8AdjointShearGram.lean:499-577
      each G8 source cutoff is trace-class and positive on the named bases
G4  C1G8AdjointShearGram.lean:1016-1065
      G8SameOwnerReadbackData -> 0 <= qw owner.sourceTest
G5  C1G8P3Contradiction.lean:28-50
      false_of_g8SameOwnerReadbackData_and_healthyDetector
      (readback data + HealthyYoshidaDetectorData rho owner.sourceTest -> False)
R0  record 1464, C1G8R0OrbitG8Geometry.lean
      OrbitG8Geometry rho g exported without any sign/health field
```

The R4 wrapper to be composed once ρ4/ρ5 land:

```text
hypothetical right-hand off-line zero rho
  -> tower construction -> g + OrbitG8Geometry rho g        (R0, sign-free)
  -> G8 readback analytic theorem on that raw geometry      (R2/R3, record 1500 gate)
       constructs G8SameOwnerReadbackData (ofCompactLogTest g) lambda
         (g8CanonicalFamily owner) globalBasis sourceBasis
  -> G5 with HealthyYoshidaDetectorData rho g               (D1/D2)
  -> False -> not-exists-zero -> healthy_sourceRH_of_right_detector_specific_qw_nonneg
  -> SourceRH -> the project's Mathlib RH output.
```

## 2. Anti-circularity audit (run on the readback producer when it exists)

1. **Statement purity (A1).** The producer's type may mention only
   `OrbitG8Geometry` fields and committed sign-free analytic theorems. Grep
   the statement for: `HealthyYoshidaDetectorData`, `qw`, `SourceRH`,
   `spectralWeilValue`, any `0 ≤`/`< 0` on Weil values, any universal
   positivity gate. Any hit is a typed circularity and stops the route
   (record 012 stop rules, record 007 §3).
2. **Same-owner pinning (A2).** The constructed data must be at owner
   `ofCompactLogTest g` with family
   `FinitePrimePowerFamily.ofSelectedOwner owner` (canonical-family theorem,
   `C1G8P1CanonicalFamily.lean:32-67`) and `sourceTest` definitionally `g`
   (G2). A different test, square, or prime family is a route mismatch and
   stops (R1 stop rule).
3. **Proof input audit (A3).** The proof may use only: the raw geometry
   (selected-owner factorization, orbit interpolation values, centered orbit
   identity, finite zero control, fourth-order tail, support interval,
   visible-prime cutoff) and the analytic pipeline of records 1476-1500.
   Numeric probe output is not admissible input.
4. **Parameter hygiene (A4).** `lambda`, `globalBasis`, `sourceBasis` fixed
   once in the statement; no cutoff step may rebind them.
5. **Composition minimality (A5).** The wrapper is exactly G5 applied to the
   constructed data and the healthy-detector data, followed by the existing
   `healthy_sourceRH_of_right_detector_specific_qw_nonneg` consumer; no new
   mathematics inside the wrapper.

## 3. Final-claims audit (A6, before any public statement)

* `#print axioms` on the wrapper and the producer: only
  `[propext, Classical.choice, Quot.sound]`; any `sorryAx` blocks.
* The advertised claim is the committed Mathlib RH statement via the existing
  `source-rh-to-mathlib-rh-definition-bridge`; no rewording that strengthens
  or weakens it.
* RH is claimed only after the wrapper builds green end-to-end; until then
  the public-facing status stays "RH-reachable, ANALYTIC-OPEN" (record 012).

## 4. Blocking ledger (from record 1500)

```text
ρ4  endpoint channel trace limit b_n -> B          OPEN (route: 1478 + 1476)
ρ5  B + 2X + L = qw(g) identification              OPEN (same-owner Euler readback)
```

Both must be discharged *before* A1-A6 can even run on a real producer.
