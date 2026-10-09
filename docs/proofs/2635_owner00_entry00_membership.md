Record 2635: owner-00 entry-(0,0) membership certificate (K00 panel family + assembly probe)
Date: 2026-10-10

Result

Positive at single-entry scope. The 541-module K00 owner-00 panel family
(PanelScalars / PanelTable / ActualPanel triplets for panels 000-179 plus
ScalarOwner2620K00) compiled green on the Linux-native workspace: xargs
batch, 170 s wall, 1082 artifacts (olean + ilean per module), full error
list empty, `uses sorry` count zero. The assembly probe
`ConnesWeilRH/Dev/ZProbe2628K00.lean` (213 theorems) then passed the triple
file-level acceptance: persisted olean present, full build-log error list
empty, `uses sorry` count zero (single-target lake run, wall 288 s,
4279-job graph). Deliverables: `actualOwnerMomentMatrix2351_entry00_mem2628`
— the 2597 entry-(0,0) analytic interval contains the owner moment integral
in all four coordinates — plus the real-side error bridge
`actualFullRealError2628K00` (|integral - center sum| <= edge charge + 180
panel bounds, every numeric re-derived from K00 sources), the four support
theorems `marginLo2628K00` / `marginHi2628K00` / `entry00_imLo_nonpos2628K00`
/ `entry00_imHi_nonneg2628K00`, the chunked replay chain (six
centersBlock/epsChunk pairs, partitionCentersSum, epsTotal), and the
extraction interface `entry00Interval2628` + kernel-rfl bridge.
eps = 10082735666832043 / 5*10^143; edge charge 2/10^68 (the committed
owner-0 certificate, bound unchanged from the 2620-era module).

Scope

Second of the 30 diagonal entries. The remaining 28 diagonal entries, the
partition assembly, the static consumer, the complex scalar engine, Producer
GO, SourceRH, and RH all remain open. No route ruling changed.

Generalization shape (2634 generator -> parameterized generator)

`scripts/generate_moment_assembly_2628_diag.py --owner-index D` replaces the
K04-only generator. Owner-specific laws it encodes:

- owner 0 predates the K-suffix rename: its edge theorem keeps the
  three-zero name `actualMomentEntry000_bothEdgeCharge_le2620`; a two-digit
  `{owner:02d}` template silently misses it (the regex fails loudly at
  generation time, which is the desired behavior).
- owner 0 needs no Fin.succ bridge: the numeral-0 head peel of the 2597
  matrix closes by kernel rfl directly (record 2618 Diagonal2618
  precedent); owners >= 1 keep the record-2634 succ-chain shape.
- capstone and extraction names drop the K suffix (`entry00Interval2628`,
  `actualOwnerMomentMatrix2351_entry00_mem2628`) to match the K04 naming
  convention, so per-entry names never collide across modules.
- all numerics (per-panel centers, error exponents, edge charge, the entry
  element itself) are re-derived from the owner's own sources; the
  chunked-vs-nested eps cross-check is retained; the verbatim element copy
  preserves the 2597 source's deep continuation indentation (AGENTS 2cc).

Preflight before the build (mechanical checks, both passed): token-stream
identity of the emitted def body against the 2597 row_00 element, and
per-field token identity of the four rfl bridges.

Incident 1 — wsl.exe one-liner target loss (silent no-op batch)

The first batch invocation passed its 541 targets via `$(cat targets.txt)`
inside a `wsl.exe bash -lc "..."` one-liner. The expansion did not reach the
lake invocation across the Git Bash -> wsl.exe quoting boundary, and lake
ran with ZERO explicit targets: exit success, "Build completed successfully
(4147 jobs)", zero K00 jobs in the graph, zero K00 oleans, 15 min spent
rebuilding stale Source modules. Nothing errored; detection came only from
an output census (Built-line classification plus olean count). Law: module
target lists cross into WSL only through a file plus `xargs -a`, or through
a WSL-side runner script, with no `$` substitution in the outer one-liner.

Incident 2 — ext4 mirror import holes

The probe's import closure reached pre-mirror-era modules that were never
transplanted into the Linux workspace: `C1RouteAMomentActualEdge2620`,
`C1RouteAMomentScalarEdge2620Panel094`, `C1RouteAMomentScalarOwner2620`
(all committed on the Windows side, absent from the mirror). Two probe
builds failed fast on `bad import` before a full transitive-closure audit
(590 ConnesWeilRH.Dev imports) synced the missing set in one pass. Law:
before building a generated probe, enumerate its full transitive import
closure and check existence on the build side; do not fix missing imports
one build failure at a time.

Next obligations

1. Remaining 28 diagonal entries (d = 2, 3, 5..29): generate each K{dd}
   family through the committed diagonal-owner wrapper, then the
   parameterized assembly probe; owners >= 1 use the succ-chain bridge
   shape.
2. Partition assembly closure: consume the entry certificates in the
   owner-matrix partition statement.
3. Static consumer, then the complex scalar engine (record 2624 GO route:
   degree-55 complex polynomial, exp(i psi c) rotation mandatory).
