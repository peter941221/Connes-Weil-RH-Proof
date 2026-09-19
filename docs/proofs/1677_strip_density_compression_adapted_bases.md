# 1677 — The StripDensity compression obligation holds for adapted bases

Date: 2026-09-19.

Status: one Lean brick + Audit.  The named obligation of the 1625/1630
strip-density layer is discharged in the form its applications use.  No
estimate on the strip density itself, on S3, on B4, or on RH is claimed.

## 1. The obligation

`StripDensityTraceLedger.StripDensityCompressionObligation` — the
trace-level compression inequality

```text
re Tr(P T P)  <=  re Tr(T)      (T positive, P a projection)
```

was filed as a named obligation because the standard proof factors
T = T^{1/2}T^{1/2} through an operator square root that the tree's layer
lacks, while the naive operator sandwich P T P ≤ T is FALSE as stated (the
audit companion carries an explicit two-dimensional counterexample; 1630
Erratum B).

## 2. The brick

`Dev/StripDensityTraceLedgerAdaptedCompression.lean` (+ Audit): when the
basis is ADAPTED to P — every basis vector fixed or killed by P — the
inequality is pure positivity bookkeeping and needs no square root:

```text
re ⟨⟨ basis i, (P ∘L T ∘L P) (basis i) ⟫⟩
   = re ⟨⟨ P (basis i), T (P (basis i)) ⟫⟩        (P self-adjoint)
   = re ⟨⟨ basis i, T (basis i) ⟫⟩                 (if P (basis i) = basis i)
   = 0                                             (if P (basis i) = 0),
```

pointwise dominated by `re ⟨⟨ basis i, T (basis i) ⟫⟩` (T positive), and
`tsum_le_tsum` finishes:

```text
re_diagonal_PTP_eq                    the diagonal fold through P† = P
ordinaryTraceAlong_re_PTP_le_of_adaptedBasis    the inequality
stripDensityCompressionObligation_of_adaptedBasis
                                      the named-obligation instance
```

Only self-adjointness of P is used in the proof; the projection condition
is carried by the applications.

Build: `build-logs/1677_adapted_compression.log`, focused two-module build,
footer "Build completed successfully (2663 jobs)", zero `^error:` lines,
zero `sorryAx`, all three theorems on
`[propext, Classical.choice, Quot.sound]`.

## 3. Why adapted bases are the case that matters

The annular-Gram consumers (1669–1676) quantify over a Hilbert basis OF THE
CARRIER, and every carrier basis vector satisfies R_0 e_i = e_i: the
carrier basis is R_0-adapted.  Any Hilbert basis split into a basis of
range P and one of ker P is likewise P-adapted.  The generic-basis version
of the obligation remains open (it is a basis-independence statement for
the diagonal-series trace); the strip-density chain of 1625 section 2 is
now repaired at trace level for exactly the window/projection pairs the
front-A and StripDensity consumers instantiate.

## 4. Boundary

The uniform annular Gram upper bound, the strip-density bound itself, and
RH remain open.  This brick adds no analytic estimate; it removes a named
formal obligation from the ledger.
