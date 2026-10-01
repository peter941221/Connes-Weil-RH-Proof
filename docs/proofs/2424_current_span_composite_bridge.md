# 2424 — current-source span composite bridge

Date: 2026-10-02.

The bridge now reads both the span sum and the parent directed total from the
same 2422 artifact.  It retains the prior 2408 parent reading only as a
legacy comparison, so evaluator revisions cannot silently masquerade as
current data.  The largest assembled upper is `137991.35871664502` on
`corr_D2`.

Pointwise mathematical-term dominance, Lean numeric import, the producer gate,
and any RH claim remain false.
