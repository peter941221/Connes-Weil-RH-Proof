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

Formal follow-up (1893): the one-span prime obligation is now reduced to a
finite cell-norm budget. The phase sum is bounded by the sum of cell absolute
values, each cell by `|Lambda(n) * 2/sqrt(n)|` times the envelope convolution
norm at `log n`. This preserves the exact visible-prime owner and is the
first quantitative interface below the abstract `hprime` margin assumption.

Formal follow-up (1894): a detector-specific opposite-sign branch is now
formal. If the two square prime phase sums satisfy `P_u <= 0 <= P_v`, then
the prime determinant is nonpositive. A compatible sign branch also makes the
mixed determinant nonpositive when both Archimedean diagonal terms are
nonpositive, both prime diagonal terms are nonnegative, and the directed
Archimedean/prime product is nonnegative. Together with a nonpositive
Archimedean determinant, this gives the complete two-span budget and the
optimal q-form consumer. This is a conditional sign socket only: the actual
selected detector still needs those sign certificates.

The same budget is also bounded by the exact visible-prime coefficient sum
times the zero-order Schwartz seminorm of the envelope convolution square.
This is still an owner-preserving upper bound; no continuous-prime or frozen
prime-set replacement is made.

Formal follow-up: `C1C3CarrierTransport` now proves the exact inverse
modulation identities
`carrierModulate (-gamma) (carrierModulate gamma f) = f` and the resulting
surjectivity of `carrierModulate gamma` on `CompactLogTest`; the support is
unchanged. Thus any actual compact-log detector can be represented as a
carrierized envelope at a chosen fixed frequency, and the existing phase-law
readbacks can be applied without changing the detector owner. This is a
coordinate/owner bridge only: the envelope depends on the chosen frequency,
and the signed determinant or prime-budget estimate remains open.

The bridge is now consumed by `orbitG8Geometry_carrier_reparam`: every actual
`OrbitG8Geometry rho g` admits, for any fixed carrier frequency, a same-owner
`OrbitG8Geometry rho (carrierModulate gamma u)` together with the equality back
to `g`. Thus the raw orbit cutoff and the carrier phase consumers can be
composed on the selected detector. This closes representation only; it does
not supply the Archimedean margin or the signed prime estimate.

The phase bridge is now explicit in
`finitePrimeSum_eq_carrierPhase_sum_of_orbitG8Geometry`: for every actual
orbit geometry and every fixed frequency, its exact finite prime sum is the
carrier phase-cell sum of a same-owner envelope. This is the first direct
interface from the actual selected detector to the existing phase-cell signed
estimate consumers; the estimate itself is still open.

For every actual visible prime power, the coefficient is further bounded by
`2 * log(n)` using the exact von Mangoldt inequality and positivity of the
square-root weight. The resulting log-weighted seminorm sum is now formal on
the exact visible owner; it remains an upper bound, not a sign certificate.

The same owner now admits a cutoff adapter: if every visible index is at most
`N`, the phase magnitude is bounded by the owner cardinality times
`2 * log(N)` times the envelope convolution-square zero-order seminorm. This
is the direct interface for consuming the orbit geometry's support-derived
finite cutoff; it still supplies no margin or sign by itself.

The cutoff adapter is now instantiated on the raw `OrbitG8Geometry` owner:
its support-derived `Nat.ceil(exp(...)) + 1` range supplies the exact `hcut`
without changing the carrier or visible-prime owner. This closes the
representation bridge to the selected detector; the quantitative margin
comparison remains open.

The same adapter now feeds the actual `orbitWindowSemiLocalGate`: under the
Archimedean bound `arch <= -delta`, it is enough to prove one scalar inequality
that the cutoff budget is at most `delta`. This is the current detector-specific
producer socket; no budget sign or RH conclusion is asserted.

The finite owner cardinality is now also bounded by the same explicit cutoff,
and the phase budget consequently has the fully explicit majorant
`N * 2 * log(N) * seminorm`, where `N = ceil(exp(2*(orbitIndex+2))) + 1`.
This removes the remaining abstract owner-cardinality factor; it is still a
majorant only, so the signed margin comparison remains the live obligation.

That fully explicit range majorant now feeds a second gate socket directly;
the remaining producer obligation is exactly the displayed scalar inequality
against `delta`, together with the Archimedean bound, with no hidden owner
cardinality or support-to-range step.

Route correction after the raw-owner audit: `OrbitG8Geometry` exports support,
zero, tail, and visible-cutoff data, but no envelope seminorm/energy certificate.
Consequently the absolute-value `N * log(N)` budget cannot be discharged from
the current geometry fields and is retained as a diagnostic upper-bound socket
only. The fastest live producer is the signed same-owner physical-kernel node
certificate of records [079](079_physical_node_certificate_route_socket.md) and
[080](080_c3p_signed_certificate_owner.md), which preserves cancellation and
must supply the actual Archimedean remainder together with signed node bounds.

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
