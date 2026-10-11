# Record 2664 wave 5 — the degree-63 ladder subgroup closes (6/6)

**Verdict: WAVE-5 GREEN — the degree-63 ladder subgroup is complete.** All
six non-psi entries whose degree-55/58/60 boxes fail and whose degree-63
boxes pass are now certified members: (23,3), (24,3), (25,3), (26,3),
(27,3), (28,3). This closes the last non-psi ladder class of the 2664
off-diagonal campaign; the remaining non-psi backlog is the 825-member
degree-55 main group. Manifest: 44 entries, all disk_verified.

## Batch facts

Driver span 13:12:57Z - 14:01:33Z (48m36s wall, six sequential
umbrella+assembly cycles, resumable SKIP protocol unused — no failures).
Per entry: sync (965 lean files, two-sided md5), umbrella build (heavy
class), assembly build (normal class), census, evidence write.

```
+--------+--------+---------+--------------------+---------------------+
| entry  | branch | banner  | axiom footprint    | assembly sha256     |
+--------+--------+---------+--------------------+---------------------+
| (27,3) | frozen | 51923/  | 115 fresh +        | 2db0d2cf..          |
|        |        | 10000   | 1741 replay = 1856 |                     |
| (26,3) | frozen | 51923/  | 1856               | a4c885bf..          |
|        |        | 10000   |                    |                     |
| (25,3) | frozen | 51923/  | 1856               | a57632ea..          |
|        |        | 10000   |                    |                     |
| (23,3) | frozen | 51923/  | 1856               | (per artifact)      |
|        |        | 10000   |                    |                     |
| (24,3) | frozen | 51923/  | 1856               | (per artifact)      |
|        |        | 10000   |                    |                     |
| (28,3) | frozen | 51923/  | 1856               | (per artifact)      |
|        |        | 10000   |                    |                     |
+--------+--------+---------+--------------------+---------------------+
```

- All six recon verdicts: `passes=True`, `edge_branch=frozen`,
  `edge_banner=51923/10000` — no general-branch build was needed in this
  wave (the thinnest member (28,3), survey margin 6.8242 over box, passed
  at 63 without escalation; recon exact barriers decided, screen only
  ordered).
- Uniform footprint: 1856 axiom records, `nonstandard=0` — the exact
  expected non-psi footprint (115 fresh + 1741 replayed), degree-
  independent per the wave-3 law.
- Gates per entry: `zero_errors=True`, `zero_sorryAx=True`; umbrella
  olean census OK on all six.
- Prep (five-step pipeline, `--degree=63`): WAVE5-PREP-OK, 6/6 dry
  byte-stability 950/950, hygiene 7 checks/entry frozen branch.

## Class accounting (manifest, authoritative)

Manifest 44 entries by degree: 55 x22, 58 x7, 60 x8, 63 x6, 66 x1. With
this wave the non-psi LADDER subgroups are all closed: 58 x7 (wave 3),
60 x8 (wave 4), 63 x6 (this wave), plus the 66 outlier (29,3) (wave 1) —
22 ladder members total. The remaining backlog is the degree-55 main
group: 825 members (847 surveyed at 55 minus the 22 already landed).

## Nonclaims

Membership certificates only. No producer GO, no gate sign change, no
map-103 reopening, no RH claim. The 2354 acceptance chain and the
producer composition are separate obligations (see records 2665/2666 for
the margin re-measure and the gate-lambda separation).

## Evidence

`results/2664_entry_{23,24,25,26,27,28}_3.json` (+ bars, budget recon,
assembly evidence per tag), `results/2664_offdiag_manifest.json` (44
entries), driver log `_probe/wave5_build_driver.log` (operational,
uncommitted per convention), prep script `_probe/batch_wave5_prep_2664.py`
(operational). Map 104 paragraph appended.
