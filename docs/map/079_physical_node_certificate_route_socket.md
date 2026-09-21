# 079 - Finite physical-kernel node certificate route socket

Date: 2026-09-21.

Status: formal consumer interface landed; the signed certificate remains open.
This record is subordinate to the binding B5 route in [003](003_b1_b5_minimal_exit_route_selection.md).

## Result

The actual selected `OrbitG8Geometry` owner has a finite visible-prime range.
For a function `nodeBound : Nat -> Real`, Lean now accepts the following
certificate shape:

```text
archimedeanTerm(g * g) + sum_{n in visible range} nodeBound(n) <= 0
every actual physical-kernel prime term(n) <= nodeBound(n)
```

The first theorem produces `orbitWindowSemiLocalGate g`. The end-to-end
theorem `sourceRH_of_right_orbitGeometry_physicalKernel_nodeBounds`
quantifies this certificate over every right-hand off-line zero and produces
`RHDefinitionBridge.standard.SourceRH`.

## Evidence and boundary

Formal evidence:

- `ConnesWeilRH/Dev/C1P2OrbitPhysicalProfileReadback.lean`
- `orbitWindowSemiLocalGate_of_physicalKernel_nodeBounds`
- `sourceRH_of_right_orbitGeometry_physicalKernel_nodeBounds`
- paired audit module with standard axioms only

The focused audit build completed successfully with zero `error:` lines and
zero `sorryAx`. This record changes the producer target from an opaque finite
budget to a finite auditable certificate, but proves no node bound, no gate
sign, and no RH. Existing support, zero, and tail fields are representation
and health data; they do not imply signed prime estimates.

## Next mathematical target

For the actual constructor-selected correction, construct signed bounds for
the finite physical-kernel terms while retaining the Archimedean remainder.
Any proposed bound must be same-owner, finite-range, and compatible with the
correction's zero/tail data. Mellin interpolation alone is excluded by
[078](078_mellin_physical_separation.md), and pointwise profile negativity is
excluded by the earlier sign audit.

The new module `C1P2OrbitPhysicalKernelIntegrandBounds` supplies the next
formal bridge: an almost-everywhere real majorant for the weighted physical
kernel integrand yields an integral upper bound, and paired majorants at
`+log n` and `-log n` yield the signed finite node bound after multiplication
by the nonnegative von Mangoldt coefficient. This is formal infrastructure,
not the analytic certificate itself. The same module now proves that the
weighted kernel integrand is integrable for every selected geometry by reducing
it to an exponential-weighted compact convolution. Thus the remaining
producer obligation is only to construct explicit same-owner integrable
majorants for the selected orbit correction and to bound the Archimedean
remainder.

The same module now packages the remaining analytic input as the
data-bearing `OrbitPhysicalKernelIntegrandCertificate`: per visible node it
stores plus/minus integrable majorants, almost-everywhere signed inequalities,
and one finite Archimedean budget. Its constructor produces the existing
`OrbitPhysicalKernelNodeCertificate` without changing owners. This is the
current fastest producer socket; the stored inequalities and budget are still
open mathematics, not assumptions discharged by the route.

The exact kernel symmetry `K(-x) = star(K(x))` is now also consumed by
`orbitPhysicalKernel_nodeTerm_le_of_plus_integrand_bound`: a single majorant at
`+log n` controls the bilateral node with the factor two. The analytic target
can therefore be formulated with one physical integrand majorant per visible
node, while preserving the same-owner signed cancellation boundary.

That reduction is now data-bearing:
`OrbitPhysicalKernelOneSidedIntegrandCertificate` stores exactly one `E n`
per visible node, its integrability and a.e. signed majorant, plus the finite
budget with the symmetry factor two. Its constructor directly yields the node
certificate consumed by the existing SourceRH socket.

The end-to-end theorem
`sourceRH_of_right_orbitGeometry_oneSidedIntegrandCertificate` now consumes
this one-sided certificate directly for every hypothetical right zero and
feeds the existing `SourceRH` implication. The remaining open producer is
therefore exactly the construction of that certificate, not any further route
conversion.

The canonical choice
`orbitPositiveIntegrandMajorant geometry n := max (Re I(log n, t)) 0` is now
formal: it is integrable, pointwise dominates the real integrand, and yields a
node bound with the reflection factor two. Hence the unresolved finite estimate
can be stated without arbitrary auxiliary functions: it is exactly the
positive-part integral budget for the actual physical kernel plus the
Archimedean term. This remains an open signed estimate, not a positivity claim.

The final producer socket is now explicit in
`sourceRH_of_right_orbitGeometry_positivePartBudget`: a per-zero actual
geometry satisfying the canonical positive-part finite budget directly implies
`SourceRH`. All auxiliary certificate packaging has been eliminated from the
statement of the remaining mathematical target.

To preserve cancellation, the same owner now has an exact positive/negative
physical-integrand split: both parts are integrable, their difference is the
real integrand pointwise, and the bilateral node equals twice the difference
of their integrals. This replaces any forced absolute-value reading by an
exact signed integral identity; the remaining estimate may bound positive and
negative masses separately.

The split is now summed over the exact finite visible-prime owner by
`finitePrimeSum_eq_positive_sub_negative_integrals`. The finite prime face is
therefore an exact sum of weighted positive integrals minus weighted negative
integrals, with no replacement by a continuous density, frozen prime set, or
absolute-value envelope.

The exact gate consumer is now also rewritten by
`orbitWindowSemiLocalGate_iff_positive_sub_negative_integral_budget`: the
same-owner semi-local gate is equivalent to the Archimedean term plus the
finite weighted positive-integral mass minus negative-integral mass being at
most zero. This is the final integral-level sign target for the live route.

The direct consumer
`sourceRH_of_right_orbitGeometry_signedIntegralBudget` now accepts exactly
that signed integral budget and feeds `SourceRH` without an auxiliary upper
bound. The remaining producer obligation is therefore the exact finite
positive-minus-negative physical integral inequality for each hypothetical
right zero.

The finite owner now also has a single signed-integrand representation:
`orbitFiniteSignedPhysicalIntegrand` is integrable and its integral is exactly
the finite prime face. This permits estimates after summing the visible prime
channels pointwise, retaining cross-prime cancellation before the final
Archimedean comparison.

For direct kernel estimates, the equivalent raw owner
`orbitFinitePhysicalKernelIntegrand` is now formal and integrable:
`finitePrimeSum` is exactly its integral, with integrand
`Σ 2 * Λ(n)/sqrt(n) * Re I(log n,t)`. The positive/negative split remains
available as an exact proof of the same identity, while estimates may now act
on the summed oscillatory kernel itself.

The gate is now exactly equivalent to the Archimedean term plus this single
raw summed-kernel integral being nonpositive, via
`orbitWindowSemiLocalGate_iff_finitePhysicalKernelIntegralBudget`. The direct
consumer
`sourceRH_of_right_orbitGeometry_finitePhysicalKernelIntegralBudget` converts
that raw producer obligation to the signed-integral consumer and then to
`SourceRH`. This is a formal interface reduction, not a positivity result;
the raw integral estimate for the selected detector remains open.

The raw integrand now also has an exact support cutoff: outside the raw-factor
window supplied by `OrbitG8Geometry`, every t-integrand vanishes pointwise,
and so does the finite summed owner `orbitFinitePhysicalKernelIntegrand`.
Together with the existing doubled-support theorem for the physical kernel,
this is a formal domain reduction for the next analytic estimate; it is not a
sign or positivity result.

The summed raw integral is now exactly equal to its interval integral over the
raw-factor window, by a support-subset theorem. The next estimate can
therefore work on this finite interval without changing the detector owner or
the visible-prime range.

The finite-window form is now wired into the route itself:
`finitePrimeSum_eq_intervalIntegral_finitePhysicalKernelIntegrand` gives the
exact prime-face readback,
`orbitWindowSemiLocalGate_iff_finitePhysicalKernelIntervalBudget` is the
corresponding gate equivalence, and
`sourceRH_of_right_orbitGeometry_finitePhysicalKernelIntervalBudget` is the
direct conditional consumer. The remaining obligation is now a genuine
finite-interval signed estimate, not a whole-line representation artifact.

The first quantitative window estimate is now formal: each weighted kernel
integrand is bounded in norm by an explicit exponential factor times the
square of the raw factor's zero-order Schwartz seminorm. This is an owner-
preserving absolute majorant only; its comparison with the Archimedean margin
is still open and must not be treated as the signed producer.
