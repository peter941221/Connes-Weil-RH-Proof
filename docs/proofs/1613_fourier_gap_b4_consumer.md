# 1613 — Fourier-form B4 gap consumer

Date: 2026-09-18

Status: formal, accepted.

The existing composite B4 gap theorem takes the Hardy support premise
`E_w H A = H A` for a source column `A`.  Using record 1612's exact
source-column equivalence, the new theorem
`compositeGapLeg_sourceColumn_normSq_summable_of_wideFourierSupport` accepts
instead the same-scale Fourier certificate `Q_w A = A` and returns the same
source-basis square-summability conclusion.

This is a real interface reduction: S3 and B4 can now share one Fourier-tail
producer.  It does not assert that the actual visible-prime column satisfies
the certificate; that analytic producer remains the open obligation.

Acceptance: `build-logs/1613_fourier_gap_consumer.log`; 4071 jobs,
zero `error:` lines, zero `sorryAx`, and one standard audited axiom print.
