# 2397 — independent point-box containment control failure

Date: 2026-10-02.

On a 1001-point grid, an independent 90-digit mpmath evaluation found two
containment escapes among 4004 point/channel values. The first is in
`base_D2` at `x=5.669356830720005`: the imaginary reference value is below the
reported hull lower endpoint by about `2.65e-55`. The reference converts every
stored binary64 operand to an exact rational; it does not reuse the evaluator's
float64 `channel_arrays` (whose cancellation error is much larger).

This is a scoped enclosure failure, not a producer certificate. It invalidates
the current sampled independent-containment claim until the missing outward
margin or formula term is identified and revalidated. It does not by itself
prove a full-domain failure, and it does not enable Lean numeric import.
