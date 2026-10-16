# Record 2715: same-owner consumer integration VERIFIED (2355 seam closed)

**Verdict: CONSUMER-INTEGRATION-VERIFIED.**  The record-2355 binding
instruction — "run the full consumer build in a clean, project-compatible
Lean environment with the existing Mathlib changes preserved or separately
isolated; the authoritative pass condition is the original consumer file
completing at the two repaired sites, followed by the permitted-axiom
audit" — is now executed and green.  The record-2354 consumer lane
upgrades from `CONSUMER-INTEGRATION-UNVERIFIED` to verified; both
acceptance lanes (scalar + consumer) of the record-2354 class are now
green.  No producer premise is discharged by this record; the hypotheses
of the consumer theorem remain exactly as binding as before.

## What ran

```text
tree     /home/peter/projects/Connes-Weil-RH-Proof  (live ext4 era tree)
command  LEAN_NUM_THREADS=1 lake build
           ConnesWeilRH.Dev.C1HealthyYoshidaSpectralNegativity
           ConnesWeilRH.Dev.C1HealthyYoshidaSpectralNegativityAudit
force    mtime touch of the consumer source (content unchanged;
         md5 51c5bb17509e477b8cecdb7d8e3f4205 identical on both sides)
log      build-logs/2355_consumer_verify_build.log
```

The touch forced genuine re-elaboration of the repaired module, so the
two repaired sites (`rw [← Finset.sum_sdiff hS]` at line 371 and the
`spectralWeilValue`-before-split rewrite pattern, commit f9809767)
completed fresh in this run rather than replaying a cached olean.

## Result

```text
lake exit        0        (3633-job plan)
error: lines     0
uses sorry       0
sorryAx          0
axiom records    6/6 exactly [propext, Classical.choice, Quot.sound]
warnings from
  the two target
  modules        0
```

The audited chain includes the end consumer
`healthy_sourceRH_of_right_detector_specific_qw_nonneg` (the audit
module's `#print axioms` output wraps across lines; parsed per the
AGENTS wrapping rule: 6 records, each flattening to exactly the trio).
The 158 warning lines in the log are cached-closure replays from other
modules (`C1XiCenterTwoGamma` 36, `CC20YoshidaConstruction` 32, ...),
decomposed per the record-2664 log-replay law — none from the rebuilt
consumer or its audit.

## Blockers named by record 2355, and their resolutions

1. "mathlib repository has local changes" — the ext4 tree's mathlib
   checkout showed 8729 porcelain entries, ALL permission-bit-only:
   after `git config core.fileMode false` (AGENTS 2bd, no content
   change) porcelain = 0 and diffstat is empty.  Nothing to preserve or
   isolate.
2. "cached project dependency C1HealthyYoshidaClosedPrefix.olean is
   absent" — present in the live ext4 tree
   (`.lake/build/lib/lean/ConnesWeilRH/Dev/`).  The absence was specific
   to the record-2355 replay path (the /mnt/c-mounted tree).

The /mnt/c tree is NOT the verification environment of this record.
Per the standing workspace law, the Linux-native ext4 tree is the build
environment; the record-2355 blockers were artifacts of replaying in the
mounted tree.

## Environment incident (ops, resolved)

The WSL VM was down at session start: every start failed with
`Wsl/Service/CreateInstance/MountDisk/HCS/ERROR_SHARING_VIOLATION`.
Root cause: the distro's `ext4.vhdx` was orphan-attached to the Windows
host storage stack as a "Msft Virtual Disk" (1024 GB, state "Attached
not open", associated disk# 3) — invisible to `wsl --shutdown`
(kills the VM, not the host-side attachment) and to `wsl --unmount`
(no `wsl --mount` bookkeeping entry).  Fix: elevated
`diskpart` → `select vdisk file="...ext4.vhdx"` → `detail vdisk`
(confirmed the attachment) → `detach vdisk` (state back to "Added");
WSL started normally afterwards.  An intermediate `Restart-Service
vmcompute` was performed and was not harmful but was NOT the fix — the
sharing violation returned until the diskpart detach.

## Nonclaims

- The consumer theorem is conditional; its hypotheses (closedBall
  square-zero control, fourth-order tail, and the record-2708 contract
  inputs) are untouched.  This record closes the INTEGRATION gate only.
- No gate witness, no prefix completeness, no source-zero identity, no
  per-rho C2 re-certification, no Producer GO, no SourceRH, no RH claim.

## Consequence for the gate map

The remaining mathematical gates to RH are unchanged and now fully
enumerated by the record-2666 trio plus the record-2708 P5 duty:

```text
G1  same-owner signed gate witness at n = 2/3   (the RH core; OPEN)
G2  source-zero prefix completeness + finite-set -> shell-prefix
    identification                              (OPEN)
G3  source-zero identity/quantifier; near-line frontier priced
    non-binding by record 2714                  (OPEN, quantified)
G4  per-rho correction C2 re-certification      (OPEN; budget has room
    up to delta* = 1.0141e-16, record 2714)
G5  Lean end-to-end consumer integration        (CLOSED, this record)
```

## Evidence

- `build-logs/2355_consumer_verify_build.log` (committed)
- commit f9809767 (the repair under verification)
- `docs/proofs/2355_same_owner_consumer_integration_audit.md` (the
  binding instruction executed here)
- `docs/proofs/2354_same_owner_tail_acceptance.md` (the consumer class)
