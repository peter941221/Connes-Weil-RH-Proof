# 2388 — strip manifest refresh and Linux integration control

Date: 2026-10-02.

After the strip-replay evaluator change, the required 2271 manifest refresh
was run with `--refresh`.  Validation passed for all 126 bound files with
manifest hash `e00d1efdfebcca83c3f630e953cb4df9cd1c1a454aa3bce961b71f799e265f2a`.

The Linux integration control was then run with `--integration`: all 22 tests
passed in 3.218 seconds.  This refresh establishes provenance and fail-closed
replay behavior only; it is not an analytic strip proof or producer GO.
