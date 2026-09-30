# 2271 — Route A strip replay controls and fail-closed verdict

Date: 2026-09-30

## Scope

This record closes the reproducibility and control-plane gaps found in the
2267 strip-envelope artifact. It does not add a new analytic estimate and it
does not turn the artifact into a Lean proof.

## Changes

- The 50 negative-sigma inputs required by 2267 (j = -50..-1) are now
  versioned beside the existing j = 0..100 inputs.
- results/2267_replay_operands.json stores the exact binary64 construction
  operands used by the replay. This removes dependence on the ignored local
  2234_build_cache.npz and chunk files.
- results/2271_strip_replay_manifest.json binds the replay inputs by SHA-256,
  byte count, parameter set, and schema version.
- The 2267 consumer validates the manifest before reduction. A missing,
  modified, malformed, or out-of-scope input produces STRIP-CONTROL-FAIL.
- The success status now requires both the numerical strip inequality and all
  raw/2243 anchors. A passing inequality with a failed anchor is not success.

## Verification

~~~text
manifest files checked       123
negative-sigma files added    50
control/replay tests          20 passed
anchor-failure injection     STRIP-CONTROL-FAIL
Lean scope                    unchanged; no producer GO
~~~

## Nonclaims

- The manifest proves provenance, not the analytic correctness of every
  numerical bound.
- The 2267 envelope remains an artifact-grade input to
  FrozenStripHypothesis; it is not yet a Lean-checked certificate.
- No gate sign change, producer GO, or RH claim.

## Provenance

- consumer: scripts/routea_weighted_zero_sigma_envelope_certified_2267.py;
- manifest generator: scripts/routea_strip_replay_manifest_2271.py;
- tests: scripts/routea_strip_replay_selftest_2271.py;
- inputs: results/2271_strip_replay_manifest.json and
  results/2267_replay_operands.json.
