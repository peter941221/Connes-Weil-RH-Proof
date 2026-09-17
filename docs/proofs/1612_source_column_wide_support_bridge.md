# 1612 — Source-column Hardy/Fourier support bridge

Date: 2026-09-18

Status: formal, accepted.

The B4 consumers act on a source-Sonin column `A : sourceSoninCarrier λ →L Carrier`,
not necessarily on an ambient-domain operator.  The new theorem
`wideHardySupport_sourceColumn_iff_wideFourierSupport` proves, at that exact
type, that

`E_w H A = H A` iff `Q_w A = A`.

Here `E_w` is the widened radial projection, `H` is the Hardy--Titchmarsh
involution, and `Q_w` is the same-scale Fourier-support projection.  The proof
is purely formal from the involution and the projection conjugation identity;
it introduces no analytic estimate and no new axiom.

This sharpens the remaining B4 obligation: for each actual boundary column,
one must produce the Fourier-support equality (or an equivalent square-sum
bound for its Fourier defect).  The completed physical boundary-kernel files
currently provide only kernel/trace readback, so they do not discharge this
producer obligation.  S3 remains the corresponding source-compressed energy
estimate.

Acceptance: `build-logs/1612_source_column_bridge.log`; 4071 jobs,
zero `error:` lines, zero `sorryAx`, and two standard audited axiom prints.
