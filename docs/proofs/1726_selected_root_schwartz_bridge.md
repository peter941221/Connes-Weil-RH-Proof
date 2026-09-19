# 1726 — selected-root Schwartz bridge

Date: 2026-09-20.

Status: FORMAL, supporting the healthy-CompactLog B5 S3 consumer; RH remains
open.

`C1G8R3SelectedRootSchwartzBridge.lean` defines the genuine selected-root
Schwartz output and proves that `rootConvolution owner (u.toLp 2)` is exactly
its L2 representative. The 1725 quadratic-decay and square-summability
theorems are therefore available for this actual owner on the Schwartz core.

The paired Audit builds with 3167 jobs, zero `error:`/`sorryAx`, and only
`[propext, Classical.choice, Quot.sound]`. The result still does not cover
arbitrary source-carrier basis vectors and does not identify the L2
Hardy--Titchmarsh output with a Schwartz representative; those are the
remaining S3 analytic obligations.
