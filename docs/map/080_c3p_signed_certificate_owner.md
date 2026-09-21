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
