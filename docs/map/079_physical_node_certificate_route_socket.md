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

The channelwise bound is now summed on the exact visible-prime owner:
`abs_orbitFinitePhysicalKernelIntegrand_le_seminorm_budget` gives a pointwise
absolute finite-channel budget on the raw window. This retains no cancellation,
so it is a quantitative diagnostic and not yet the required signed estimate.

The pointwise budget now feeds an interval-integral upper bound through
`intervalIntegral_orbitFinitePhysicalKernelIntegrand_le_seminorm_budget`.
This is the exact scalar socket for testing the absolute budget against the
Archimedean margin; it still does not establish the required signed gain.

The finite visible-prime kernel now also has a same-owner complex aggregate
`orbitFiniteComplexPhysicalKernelIntegrand`, with the existing real integrand
proved to be its real part by
`orbitFinitePhysicalKernelIntegrand_eq_re_complex`. This preserves the full
cross-prime phase sum for the next estimate; it is a representation bridge,
not yet a signed-gain or positivity theorem.

The complex aggregate is also formally integrable, and
`finitePrimeSum_eq_re_integral_orbitFiniteComplexPhysicalKernelIntegrand`
reads the complete finite prime face as the real part of its single complex
integral. This is the cancellation-preserving integral owner for the next
analytic estimate; it remains an identity, not a sign result.

The complex aggregate now factors exactly as the common reflected raw factor
`star(raw(-t))` times the same-owner profile
`orbitFiniteComplexPhysicalKernelProfile`. The theorem
`orbitFiniteComplexPhysicalKernelIntegrand_eq_common_factor_profile` keeps all
visible-prime phases inside that profile, supplying the direct correlation
owner for the next signed estimate. No sign or positivity is inferred.

Its norm also factors exactly into the norm of the common raw factor and the
norm of the finite-prime phase profile via
`norm_orbitFiniteComplexPhysicalKernelIntegrand_eq_common_factor_profile`.
This is the first quantitative interface that preserves the aggregate profile
before any later estimate; it still supplies no sign by itself.

The aggregate now yields the cancellation-preserving scalar estimate
`finitePrimeSum_le_integral_common_factor_profile_norm`: the finite prime face
is bounded by one integral of the common raw norm times the norm of the full
phase profile. This is strictly a post-aggregation bound, distinct from the
earlier sum of channelwise absolute budgets; it remains an upper bound rather
than the required signed gain.

The post-aggregation bound now has an L2 reduction,
`finitePrimeSum_le_l2_common_factor_profile_mass`: under same-owner MemLp(2)
certificates for the raw factor and the finite-prime phase profile, the prime
face is bounded by the product of their two square-root masses. This separates
the remaining analytic work into two energy obligations without changing the
detector owner or claiming a sign.

Both integrability obligations are now formally discharged. The raw
obligation is handled by
`orbitRawFactor_reflected_memLp_two`: the orbit raw test is Schwartz, and
reflection through `t |-> -t` preserves Lebesgue measure. The reduced socket
`orbitFiniteComplexPhysicalKernelProfile_memLp_two` handles the finite-prime
profile by expressing every summand as a translated/reflected exponentially
weighted Schwartz test and closing under finite sums. Thus
`finitePrimeSum_le_l2_common_factor_profile_mass_of_profile` is now a fully
typed same-owner L2 socket. The remaining obligation is quantitative: bound
the profile square-root mass strongly enough against the Archimedean term.
The auxiliary theorem
`orbitFiniteComplexPhysicalKernelProfile_lpNorm_le_sum_of_memLp` reduces that
mass to the sum of the individual visible-prime term masses, so the next
estimate can be local in the prime-power index rather than treating the
profile as an opaque finite sum.
This is a formal functional-analytic reduction, not a positivity result.

The individual term is now normalized exactly by
`orbitFiniteComplexPhysicalKernelProfile_term_lpNorm_eq_common`: each visible
prime-power summand has L2 norm equal to the modulus of its explicit scalar
coefficient times the common norm of the same-owner exponential-weighted raw
test. The proof uses the measure-preserving affine reflection
`t |-> log(n) - t`; it introduces no new owner or support assumption. The
remaining quantitative task is therefore an explicit coefficient sum times
one common weighted-raw L2 mass, followed by comparison with the Archimedean
negative term. This remains an open signed estimate.

The aggregate form is now packaged as
`orbitFiniteComplexPhysicalKernelProfile_lpNorm_le_common_weighted_raw_mass`.
Given the already available per-term MemLp certificates, it bounds the whole
profile mass by one explicit coefficient sum times one common weighted-raw
mass. This is still a conditional norm reduction: it discards phase
cancellation and therefore cannot itself close the signed B5 budget.

Using the raw-factor support, the same estimate is now localized to the exact
finite window by
`finitePrimeSum_le_intervalIntegral_common_factor_profile_norm`. This is the
current scalar comparison socket against the Archimedean window term; it
retains the aggregate profile but still does not prove its required negative
signed balance.

The full conditional route is now composed by
`sourceRH_of_right_orbitGeometry_interval_common_factor_profile_norm_budget`.
For every hypothetical right zero, the remaining analytic producer obligation
is exactly one actual-geometry Archimedean-plus-profile-window inequality;
that inequality implies the same-owner gate and then `SourceRH`. No such
inequality has yet been proved.

The profile-window budget is now consumed by
`orbitWindowSemiLocalGate_of_interval_common_factor_profile_norm_budget`:
an Archimedean-plus-profile-norm inequality is sufficient for the actual
same-owner semi-local gate. This is a genuine producer socket, although the
profile inequality itself remains the open analytic obligation.
