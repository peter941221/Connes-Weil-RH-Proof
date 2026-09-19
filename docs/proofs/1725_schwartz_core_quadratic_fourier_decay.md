# 1725 — Schwartz-core quadratic Fourier decay

Date: 2026-09-20.

Status: FORMAL, supporting S3 brick; RH remains open.

`C1G8R3SchwartzQuadraticDecay.lean` supplies two audited consequences of the
existing Schwartz API. Every `SchwartzMap ℝ ℂ` has integrable first and second
derivatives through `SchwartzMap.derivCLM`, so the existing
integration-by-parts estimate gives quadratic Fourier decay. The decay is
then square-summable on the integer translation tail.

The Audit leaf builds with 2968 jobs, zero `error:`/`sorryAx`, and only
`[propext, Classical.choice, Quot.sound]`.

This closes the regularity-to-rate leg on the genuine Schwartz core only. It
does not identify the L2 Hardy--Titchmarsh output of the selected root with a
Schwartz function, and therefore does not close S3. The remaining live task
is the concrete Hardy regularity bridge, or a direct diagonal majorant, for
the actual source-Sonin compressed root.
