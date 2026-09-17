# 1600: Joint Hardy-sub-identity consumer for S3/B4

Date: 2026-09-18

## Result

The new audited module `C1G8R3JointHardySubIdConsumer` formally proves the
generic implication

`Hardy-sub-identity square-sum + source prolate factor`
`=> source-Sonin commutator square-sum`.

The external factor is deliberately an arbitrary bounded finite-S operator
`D`.  The root-specific composite factor can therefore be supplied by a
separate consumer without forcing Lean to elaborate the long root-convolution
expression in this theorem's signature.

## Mathematical status

This is a consumer/interface, not the missing analytic producer.  It combines
the already formal prolate Hilbert--Schmidt factor with the Hardy-sub-identity
term and feeds the source commutator ledger.  The actual S3/B4 closure still
requires a proof that the selected Hardy-sub-identity square-sum is summable
for the actual boundary operator.  No positivity, endpoint estimate, or RH
statement is added here.

## Acceptance

The focused build log
`/home/peter/rh/build-logs/1606_joint_hardy_subid_generic.log` reports
`Build completed successfully (4071 jobs)`, zero `error:` lines, zero
`sorryAx`, and one audited standard-axiom print.
