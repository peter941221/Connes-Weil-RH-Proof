# 080 — C3' signed certificate owner

Status: formal owner socket, 2026-09-21.

`C1C3CarrierTransport` now packages the selected carrier two-span producer
input as `CarrierTwoSpanDeterminantCertificate`. The record binds the carrier
frequency, the two compact-log tests, their common support radius, the
positive BB pivot, and the exact signed budget

`Archimedean determinant + mixed discrepancy + prime determinant <= 0`.

The record's `gate` theorem feeds the existing orbit-window semi-local gate.
This is formal algebra and consumer wiring, not a proof of the inequality.
It prevents a future estimate from combining a phase term from one carrier,
support owner, or visible-prime range with another. The next mathematical
target is to construct this record for the detector selected by the healthy
`CompactLog` B5 route. The remaining obligation is exactly its `phase_budget`;
no pointwise sign of the three summands is assumed.

## Round 1 closure (2026-09-22)

Round 1 is complete at the formal owner-and-consumer boundary, not as the
analytic sign proof. The committed `C1C3CarrierTransport` leaf now has one
exact same-owner phase budget for the selected carrier pair:

```text
Archimedean determinant
+ mixed Archimedean/prime discrepancy
+ prime determinant
<= 0
```

The phase-cell readbacks, positive/negative decompositions, determinant split,
optimal-coefficient consumer, and `CarrierTwoSpanDeterminantCertificate.gate`
are formal interfaces. The paired Audit module is the axiom evidence for this
boundary. Round 2 must prove the actual inequality; the existing sigma-tail
results do not by themselves imply the detector-specific phase budget.

Evidence: `ConnesWeilRH/Dev/C1C3CarrierTransport.lean`, theorem
`CarrierTwoSpanDeterminantCertificate.gate` (formal, project candidate
owner); prior exact determinant split and phase readbacks are recorded in
`docs/map/075_c3p_carrier_transport_after_1800.md`.

Formal follow-up: `C1C3CarrierFourierShift.lean` proves the exact same-owner
frequency transport
`Fourier(carrierModulate gamma f, xi) = Fourier(f, xi + gamma/(2*pi))`,
including the zero-frequency specialization. This is the algebraic front of
the paper sigma-shift argument; it does not prove a sigma identity, a sign,
or the phase budget.

The same file also identifies this integral with the existing
`C1XiArithmeticPrimePowerReadback.fourierLaplace` owner, so the shift is now
usable by the vertical Gamma/Xi readback rather than being an isolated
auxiliary transform.

Further formal follow-up: `laplaceAt_carrierModulate_eq_shift` proves the
same transport in the bilateral Laplace owner,
`Laplace(carrierModulate gamma f, s) = Laplace(f, s - gamma*i)`. This is the
coordinate identity needed before defining and estimating the sigma weight;
the sigma identity and its negative sign remain open.

The transport is now lifted further through the existing centered and
symmetrized Xi weights. Thus a fixed C3 carrier frequency is represented in
the same vertical-functional owner used by the Gamma readback; this remains
an exact coordinate theorem, not an Archimedean sign theorem.

The actual `gammaRIntegrand` now has the corresponding shifted centered-weight
readback on this owner. The next missing step is therefore genuinely the
GammaR kernel/sigma estimate, not carrier bookkeeping.

`C1C3GammaRBound.lean` now proves an explicit norm upper bound for
`logDeriv GammaR` on `Re(s) >= 1/2`, by transporting the existing digamma
vertical-line estimate through the exact GammaR formula. This controls the
kernel magnitude for the future remainder estimate; it is not a real-part
sign theorem.

Formal follow-up: `C1C3SigmaKernel.lean` defines the paper sigma profile on
the same GammaR owner and proves its exact identity with minus twice the real
part of `logDeriv GammaR` at `1/2 - xi*I`. This is formal route evidence for
the coordinate identity only; sigma negativity and the full signed budget
remain open.

The same leaf now proves `c3Sigma xi - c3Sigma 0` as the real part of an
explicit convergent reciprocal-difference series. This is the formal series
owner for a future tail/sign certificate; it still supplies no numerical
threshold and no aggregate C3 inequality.

The series has also been reduced termwise to a nonnegative rational expression
and summed through `Complex.re_tsum`, yielding the formal global bound
`c3Sigma xi <= c3Sigma 0`. This establishes monotonicity away from the
zero-height anchor in the required owner, but does not prove that the profile
has crossed zero at any explicit height.

For `xi != 0`, the same positive first term gives the strict inequality
`c3Sigma xi < c3Sigma 0`. The remaining sign task is therefore an explicit
lower bound on the accumulated reciprocal series strong enough to overcome
the anchor value, followed by the detector-specific signed prime budget.

The leaf now also proves the finite partial-sum form: for every natural `N`,
`c3Sigma xi` is at most `c3Sigma 0` minus the first `N` explicit nonnegative
rational terms. This is the formal finite-threshold socket for a future
certified zero-crossing bound; it does not itself choose a numerical `N` or
prove the C3 prime budget.

Finally, the same series proof gives the exact symmetry
`c3Sigma (-xi) = c3Sigma xi`. The remaining profile-sign work may therefore
be restricted to nonnegative heights, while the detector-specific signed
budget remains unchanged and open.

The individual rational summands are now formally monotone in height: for
`0 <= xi <= eta`, the eta summand is at least the xi summand. This supplies
the comparison mechanism needed to propagate one certified negative sigma
value to all higher nonnegative heights; the first certified negative point
and the C3 signed budget are still open.

The comparison has now been summed on the same convergent reciprocal-series
owner, yielding the global theorem `c3Sigma_antitone_of_nonneg`: for
`0 <= xi <= eta`, `c3Sigma eta <= c3Sigma xi`. Thus a future certified
negative point propagates to every higher nonnegative height. This remains a
formal propagation result only; it supplies neither the first negative point
nor the detector-specific signed prime budget.

The finite-sum certificate has now been combined with divergence of the
harmonic series to prove `exists_c3Sigma_neg`: some real height has strictly
negative sigma. The construction is exact and axiom-clean, with no numerical
approximation. This closes only existential Archimedean sign; it does not give
an explicit threshold for a hypothetical zero height, nor the same-owner
detector-specific signed prime budget required by the B5 producer.

Using evenness and global antitonicity, this is now packaged as
`exists_c3Sigma_negative_tail`: there is a nonnegative threshold `T` such that
every `xi >= T` has negative sigma. The threshold is still existential rather
than a concrete certificate, so the hypothetical-zero height lower bound and
the detector-specific signed prime budget remain the active producer gates.

The anchor has now received an explicit rational ceiling:
`c3Sigma_zero_lt_twelve`. Its proof uses the committed quarter-line digamma
norm bound, the exact half-point digamma value, and Mathlib's rational bounds
for log 2, pi, and the Euler constant. This makes the remaining threshold
certificate purely a finite harmonic lower-bound problem; it does not yet
close the hypothetical-zero height quantifier or the visible-prime budget.

The finite arithmetic interface is now explicit in
`c3Sigma_neg_of_harmonic_certificate`: any finite `K` whose reciprocal sum
exceeds 24 gives a strict negative sigma at height `2*(K+1)`. The proof is
parameterized and never unfolds the range, so a later `ceil(exp 25)` or other
exact harmonic certificate can instantiate it without large-range recursion.

That supplier is now instantiated formally by
`c3Sigma_neg_at_exp_ceiling`: with `K = Nat.ceil (Real.exp 25)`, the harmonic
lower bound gives a concrete exact negative height
`2 * (Nat.ceil (exp 25) + 1)`. This closes the Archimedean sigma-sign
certificate on its own owner.

The monotonicity theorem now packages the usable conditional height gate:
`c3Sigma_neg_of_height_above_exp_ceiling` proves negativity for every real
height at least that exact threshold. This is intentionally conditional: the
project has not proved that an arbitrary hypothetical off-line zero reaches
this height, so the theorem is not presented as a universal zero-height lower
bound. The detector-specific visible-prime signed budget remains open.
