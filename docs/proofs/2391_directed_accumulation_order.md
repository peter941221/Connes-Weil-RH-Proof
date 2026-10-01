# 2391 — directed accumulation order lemma

Date: 2026-10-02.

The finite-sum part of the 2385 accumulation step has been written as a
candidate Lean interface.  The single-span lemma and its nested span version
show the intended order-theoretic implication: termwise upper bounds,
followed by span upper bounds, imply the final finite-sum upper bound.

The audit is pending because the current WSL Lean invocation hangs even on the
existing 2390 audit.  This does not certify that the
MPFR/binary64 values stored by the replay are the corresponding mathematical
terms, and it does not import any numeric value into Lean.

The required Mathlib brick check was rerun on 2026-10-02 and completed with
its existing result artifact at `results/2049_mathlib_brick_check.json`.  That
check is a library inventory, not a proof of this candidate file; the direct
Lean audit therefore remains pending.
