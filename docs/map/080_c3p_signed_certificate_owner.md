# 080 — C3' signed certificate owner

Status: active formal owner socket. The owner and consumers are complete; the
detector-specific analytic sign is open.

## Exact owner

`C1C3CarrierTransport` packages a `CarrierTwoSpanDeterminantCertificate` on
one carrier frequency, two `CompactLog` tests, one common support radius, one
support-derived finite prime owner, and the aggregate budget

```text
Archimedean determinant
  + mixed Archimedean/prime discrepancy
  + prime determinant
<= 0.
```

Its `gate` theorem feeds `orbitWindowSemiLocalGate`. The direct consumers in
[082] then produce the same-detector Weil nonnegativity and the formal
contradiction to `SourceRH`.

## Formal progress that must be preserved

- exact phase-cell, positive/negative, determinant, and optimal-coefficient
  readbacks on the same owner;
- opposite-gate determinant construction: one nonpositive diagonal and one
  nonnegative diagonal force the aggregate determinant nonpositive, with no
  cross-sign premise;
- the selected healthy detector has a strictly positive gate orientation;
- narrow prime-free roots and an odd parity component can supply a negative
  diagonal under their stated support/nonvanishing hypotheses;
- the odd component can be constructed for an off-line zero with the required
  node vanishing and nonzero detection;
- carrier Fourier/Laplace shifts and the complete GammaR/sigma owner are
  formal;
- the sigma profile is even, antitone for nonnegative height, and eventually
  negative in an existential sense;
- finite physical-node and aggregate-kernel consumers are formal through
  [079] and [081].

These results solve algebra, ownership, and several component constructions.
They do not prove the sign for the final selected span or detector.

## Current missing theorem

Construct, for every hypothetical off-line zero, one test on the selected
healthy owner that simultaneously has:

1. the already-required triple vanishing and off-line-zero detection;
2. the exact support-derived finite visible-prime set;
3. a semi-local gate value at most zero; and
4. compatibility with the strict negative spectral contribution used in the
   contradiction.

In the direct C3' lane this means proving the displayed aggregate budget (or a
stronger physical-kernel inequality) with an explicit margin. In the
phase-balanced lane, [091] supplies item 3 and [094] reduces item 4 to a
finite-prefix margin plus a weighted high-shell tail.

## What does not count as closure

- proving separate signs for the three determinant channels when only the
  aggregate determinant is needed;
- an existential negative sigma height without connecting it to the actual
  zero and prime budget;
- a negative auxiliary component without proving detection and tail behavior
  for the final span;
- a conditional structure whose final field is the desired budget;
- a different finite prime owner or a demodulated surrogate not proved equal
  to the selected detector.

## Evidence

Primary formal modules include `C1C3CarrierTransport.lean`,
`C1HealthyDetectorEvenOddPair.lean`,
`C1P2NegativeDiagonalCertificate.lean`,
`C1P2OddNegativeDiagonalCertificate.lean`, `C1C3SigmaKernel.lean`, and paired
audits. Proof records 1800, 1804, 1812--1826, 1873--1902 retain the detailed
chronology and build evidence.

Classification: owner/readbacks/component theorems are `FORMAL`; the aggregate
selected-detector sign and full spectral-tail compatibility are `OPEN`.

## 2175 strict pinned margin

The paired module `C1C3StrictPinnedMargin.lean` and audit now strengthen the
pinned C3′ owner socket.  For the same carrier-demodulated pair
`(narrowArchRoot, g)`, with `g` carrying `HealthyYoshidaDetectorData`, the
strict root gate and strict healthy pivot give the explicit determinant margin

```text
μ = (-ICgate narrowArchRoot.convolutionSquare)
      * ICgate g.convolutionSquare > 0,
determinant ≤ -μ.
```

The exact determinant/phase split then gives the same `-μ` margin for the
aggregate Archimedean + mixed + prime phase budget.  The retained cross term
is handled only by its exact square nonnegativity.  This is a real
quantitative strengthening of the existing nonpositive certificate on the
same owner; it does not reopen the frozen four-point family and does not close
the selected-detector producer.  Support, triple vanishing, zero detection,
and full spectral-tail compatibility remain named obligations.

Evidence: proof record [2175](../proofs/2175_c3_strict_pinned_margin.md),
module build `results/20260929_c3_strict_margin_build4.log`, and paired audit
`results/20260929_c3_strict_margin_audit_build5.log`.

## 2176 explicit optimal q-form margin

The same module now exposes the pinned determinant margin through the exact
optimal two-coordinate q-form.  `carrierTwoSpanOptimalQform` uses the
coefficient

```text
λ* = -ICgate(u.involution.convolution v) / ICgate(v.convolutionSquare),
```

and `strict_carrier_twoSpan_determinant_product_bound_of_pinned_geometry`
rewrites the determinant upper bound as

```text
det(u,v) ≤ -((-ICgate narrowArchRoot.convolutionSquare)
              * ICgate g.convolutionSquare).
```

`strict_carrier_twoSpan_optimal_qform_margin_of_pinned_geometry` consequently
returns the explicit witness
`μ = -ICgate narrowArchRoot.convolutionSquare > 0` and proves
`carrierTwoSpanOptimalQform γ u₀ v₀ ≤ -μ` for the carrier-demodulated
root/healthy pair.  This is a strict quantitative strengthening at the
existing owner socket; it does not reopen the frozen four-point family or
close the selected-detector producer.  Support, triple vanishing, detection,
and full spectral-tail compatibility remain open.

Evidence: proof record [2176](../proofs/2176_c3_optimal_qform_margin.md),
module build `results/20260929_c3_qform_margin_build9.log`, paired audit
`results/20260929_c3_qform_margin_audit_build10.log`, and root aggregate
`results/20260929_c3_qform_margin_root_build11.log`.

## 2131 cross-sign boundary

Record 2131 closes one proposed shortcut: the opposite diagonal signs in
`CarrierTwoSpanSignCertificate.diagonal_signs` do not imply
`directed_cross_nonneg`. Two rows from the registered 1798 two-span family
satisfy the diagonal sign predicate while their Archimedean/prime cross
products are `-1.343614e-6` and `-1.856144e-7`. The condition must therefore
be proved separately on the actual owner, or replaced by a genuinely
aggregate signed inequality. This is a scoped family no-go, not a no-go for
the formal zeta owner or Route A.

## 2172 CC20 (143) contract contraction

Record [2172](../proofs/2172_cc20_h143_discharge.md) discharges the exposed
CC20 auxiliary-transform equation (143) on the same compact-log owner by
choosing `k = -(g + g)`. The paired Lean module
`C1CC20ArchimedeanComparisonH143.lean` proves the identity from exact
`laplaceAt` linearity and constructs the existing comparison package with only
the nonnegative-trace, (142), and `E`-chain fields remaining. Its companion
consumer theorem feeds the package to `qw_nonneg` under the unchanged
triple-vanishing and root-support hypotheses. The trace identification and
gamma-side estimate are still analytic inputs, and the root-support endpoint
consumer is not the selected Route-A producer. This is a strictly smaller
contract, not a sign certificate or RH result.

## 2173 CC20 E-chain scalar contraction

Record [2173](../proofs/2173_cc20_echain_scalar_contract.md) uses the same
canonical `(143)` choice after triple vanishing to show
`normSq (laplaceAt k (1/2)) = 0`. The new theorem
`cc20Echain_iff_nonpos_of_vanishes` proves that the stored `hEchain` is then
exactly equivalent to the scalar remainder sign `eTerm ≤ 0`. The constructors
`cc20ArchimedeanComparison_of_h142_eNonpos` and
`qw_nonneg_of_h142_eNonpos` remove the vector norm and gamma bound from the
caller contract while retaining the same owner, `(142)`, and trace
nonnegativity. This is a strictly smaller named obligation, not a sign
certificate or RH result. The remaining analytic work is explicit: prove
`(142)` and `eTerm ≤ 0` for the selected owner; the existing trace model does
not contain that connecting identity.

## 2177 topology extension screen

Record [2177](../proofs/2177_routea_topological_extension_screen.md) closes a
topology-only extension as a scoped no-go. Weak compactness can produce a
minimizer but does not produce the selected-owner signed C3' margin; ROOT
closure does not control the mixed terms; the current high-height owner count
blocks one-node-per-zero interpolation; and record 2157 gives a quantitative
near-pin derivative-cost divergence.

The sole retained grandchild is `A.005.1`: an owner-preserving,
non-interpolating weighted-zero-measure C3' certificate. Its first gate is an
exact-owner enclosure with a weight fixed by the physical-kernel/correction
formula and a strict `B_zm < epsilon` margin. The candidate is unpriced and
does not alter the selected-detector producer status.

## 2178 tail sub-obligation

Record [2178](../proofs/2178_routea_infinity_algebraic_remainder.md) gives an
explicit two-sided algebraic remainder for the order-48 high-height tail on
the one-copy G8-H numerical owner.  The bound is `6.9025590685960082e-974`
after `|xi| >= 10^6`, and no floating-point underflow is used.  This is a
strictly smaller tail obligation only; it does not transfer the owner, certify
the finite-window signed aggregate, or close the selected-detector producer.

Records [2179](../proofs/2179_routea_n48_rational_horner_audit.md) and
[2180](../proofs/2180_routea_root_sturm_audit.md) strengthen this tail branch:
exact-rational Horner arithmetic and an exact Sturm chain independently preserve
the enormous tail margin and certify the 64-root sign partition.  The branch
still remains a candidate-owner tail result; the complete closed-ball owner
and finite-window signed aggregate are open.
