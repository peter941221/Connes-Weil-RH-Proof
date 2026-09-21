# 075 — C3' opens: phase law is a theorem, the floor has a symbol

Status: the analytic page of the two-span producer opens (2026-09-21).

Formal follow-up (1873): the carrierized two-span diagonal gates and the
directed AB cross gate now both have same-owner envelope-level phase
readbacks. The diagonal readback is available through the carrierized span
identity and the AB readback is an explicit Archimedean term plus the full
visible prime-power sum. This closes the phase-transport/readback interface,
not the signed inequality.

Formal follow-up (1876): the optimal two-span coefficient is now explicit.
When the BB diagonal is positive, the q-form at `lambda = AB / BB` equals
`(AA*BB - AB^2) / BB`, and its nonpositivity is equivalent to the determinant
budget `AA*BB <= AB^2`. This is an exact reduction, not a sign certificate.

Formal follow-up (1877): under the same support hypotheses, that optimal
determinant condition now directly produces the concrete
`orbitWindowSemiLocalGate`; the remaining input is precisely the determinant
sign certificate, not a choice-of-coefficient or support bridge.

Formal follow-up (1878): the determinant is now decomposed exactly into an
Archimedean determinant, the Archimedean/prime mixed discrepancy, and the
prime determinant. This identifies the three signed-estimate consumers; it
does not assign a sign to any of them.

Formal follow-up (1879): the directed cross phase law now lifts from each
prime cell to the complete finite visible-prime sum. Thus the prime
determinant consumer is explicitly phase-readable on the same finite owner;
its sign remains open.

Formal follow-up (1880): the AB finite-prime sum now also has an exact
positive-minus-negative decomposition on its own visible-prime owner. The
square-only signed-budget definition is not reused for the directed cross
channel; no sign is assumed.

Formal follow-up (1881): the cross phase cell is now a named owner, and the
same signed balance is stated directly in phase-cell variables. Future
estimates can therefore target the phase credit and deficit without reopening
the carrier algebra.

Formal follow-up (1882): the diagonal square phase cell now has the same named
owner and positive-credit/negative-deficit readback. The AA, AB, and BB prime
consumers therefore share one phase-cell data layer; no sign conclusion is
claimed.

Formal follow-up (1883): each complete AA, AB, and BB finite-prime sum now
reads as a sum of its named phase cells. The prime side of the determinant is
therefore fully on the phase-cell owner; its signed estimate remains open.

Record [1800](../proofs/1800_c3p_carrier_transport_and_sigma_floor.md)
lands one formal brick (`C1C3CarrierTransport`, standard axioms, clean
build) and one paper page:

Formal follow-up (1884): the square and directed-pair Archimedean numerators
now have named phase-owner readbacks as well. Both sides of the determinant
are therefore phase-readable; no Archimedean or total sign is claimed.

Formal follow-up (1885): those named numerators now lift through the actual
Archimedean denominator to named phase integrands for square and directed-pair
channels. This closes the function-level phase readback; the sigma/sign
estimate remains open.

Formal follow-up (1886): the named square and directed-pair phase integrands
now lift through the full Archimedean functional to named phase terms. The
Archimedean determinant consumer is therefore fully phase-owned; its sign
remains open.

Formal follow-up (1887): the full two-span determinant is now packaged as
three named phase-owner consumers: Archimedean determinant, mixed
Archimedean/prime discrepancy, and prime determinant. The equality is formal
and axiom-clean; it supplies no positivity or signed-budget conclusion.

Formal follow-up (1888): under the existing positive-BB hypothesis, the
optimal two-span q-form is equivalent to nonpositivity of the sum of those
three phase-owner consumers. This is the direct signed-budget consumer; the
inequality itself remains open.

Formal follow-up (1889): the prime determinant consumer now expands through
named square and directed-pair phase credits and deficits. This exposes the
positive/negative cross terms needed by a future signed estimate, without
assuming any of their signs.

Formal follow-up (1890): `carrier_twoSpan_phase_budget_of_margin_bounds` adds
the margin-form sufficient condition on the same owner. If the Archimedean
determinant is at most `-delta`, while the mixed and prime determinants are at
most `mu` and `pi`, the budget follows from `mu + pi <= delta`. This is an
estimate interface, not an estimate: the three analytic bounds remain open.

Formal follow-up (1891): the same owner now proves absolute-value envelopes
for the two non-Archimedean consumers. The prime determinant is at most the
product of the two diagonal prime magnitudes, and the mixed discrepancy is at
most the sum of its three absolute product terms. These are rigorous upper
bounds that can feed the negative Archimedean margin; they do not assert the
needed margin or any RH conclusion.

Formal follow-up (1892): a faster one-span socket is now formal. If one
carrier square has Archimedean term at most `-delta` and its complete finite
prime phase sum has absolute value at most `delta`, then the same-owner
`orbitWindowSemiLocalGate` follows directly. This is a valid B5-shaped
consumer and may close before the two-span determinant, but both margin
estimates remain to be proved for the selected detector.

- **Carrier transport (formal)**: same-carrier pair tests transport the
  carrier exactly; the square channel and the Weil pair sum collapse to
  `2·Re[e^{-iγy}·G(y)]`; every prime cell reads `Λ(n)·2/√n·Re[e^{-iγ log
  n}·G(log n)]`. The 1799 W2 quasiperiodicity is now structural algebra.
- **σ-shift arch floor (paper)**: `arch(carrier square) = σ(−γ)·‖u‖² +
  O(W·‖Ĝ‖₁/γ)` with `σ(−γ) < 0` for `γ > ξ*` theorem-grade (1741 digamma
  leaf). The budget's deficit side has a symbol.
- **C3' precisely stated**: the producer reduces to an ENVELOPE-level
  inequality `q(λ; γ) ≤ 0` at fixed γ. Per-zero locality of B5 kills the
  phase obstruction (γ is fixed by the zero, not quantified); uniformity
  in γ lives only in the separate W4 limit page.

Next active target: the envelope-level determinant inequality itself — now
including the cross channel in the same explicit owner — first as a
measurement (envelope q-form at fixed γ, λ free, interpolation-pinned
envelopes), then as signed estimates with the two-IBP pairing tool; the
σ-identity Lean brick is the parallel formalization entry.
