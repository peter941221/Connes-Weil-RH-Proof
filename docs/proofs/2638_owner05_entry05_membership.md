Record 2638: project-local Matrix.cons_val family (indices 5-29) + owner-05 entry-(5,5) membership certificate
Date: 2026-10-10

Result

Positive at both scopes. (1) The project-local family module
`ConnesWeilRH/Dev/MatrixConsValFamily2637.lean` — 25 theorems
`Matrix.cons_val_5` .. `Matrix.cons_val_29`, each
`vecCons x u N = vecHead (vecTail^(N-1) u) := rfl`, replicating the
Mathlib VecNotation shape that stops at four — compiled green in a
single-module smoke build (error list empty, olean persisted). (2) The
full K05 owner-05 stack (541 family modules with the generated
`import ConnesWeilRH.Dev.MatrixConsValFamily2637` lines and digit-named
cons_val lemmas, regenerated edge pair, probe `ZProbe2628K05.lean`,
213 theorems) compiled green in ONE xargs batch: 544 targets, 388 s
wall, 4279 jobs (the +1 job is the family module in the dependency
graph), 1088 artifacts, full error list empty, `uses sorry` zero.
Deliverables: `actualOwnerMomentMatrix2351_entry05_mem2628` — the 2597
entry-(5,5) analytic interval contains the owner moment integral in all
four coordinates — plus `actualFullRealError2628K05` (eps
142470248507591/2*10^149, edge charge 7/10^69), the four support
theorems, the chunked replay chain, and the extraction interface
`entry05Interval2628` + kernel-rfl bridge.

Scope

Sixth of the 30 diagonal entries, and the FIRST owners >= 5 validation:
every diagonal index 0..29 is now unblocked (Mathlib words for 1-4, the
project-local digit family for 5-29). The 24 remaining entries (d =
6..29) are pure pipeline reruns. Partition assembly, static consumer,
complex scalar engine, Producer GO, SourceRH, and RH all remain open.
No route ruling changed.

Generator changes (all gated on owner >= 5; d <= 4 byte-identity proven)

- `rename_owner_symbols` now emits `Matrix.cons_val_{5..29}` (digits)
  instead of raising, and inserts the family-module import after the
  last import line of each generated module.
- `generate_moment_edge_owner_2628.py` uses the same digit names and
  adds the family import to the ActualEdge template.
- Byte-identity probe before any build: regenerating owner 2 with the
  changed generators reproduced all 540 panel modules, ScalarOwner2620K02,
  and both edge files EXACTLY (zero diffs) — the owners <= 4 path is
  provably unperturbed.

Incident 1 — module docstring before import (smoke-caught, 152 ms)

The family module originally placed its `/-! ... -/` docstring before
`import Mathlib.Data.Fin.VecNotation`; Lean 4 rejects any import that
does not open the file ("invalid 'import' command, it must be used in
the beginning of the file"). The single-module smoke build caught it in
152 ms. Law: in Lean 4, imports come first, THEN the module docstring;
new modules get a smoke build BEFORE joining a batch.

Incident 2 — dual-purpose rename function crashed on filenames

`rename_owner_symbols` is called both on module text and on FILENAMES;
the new import-insertion branch did `max()` over import-line indices,
which is empty for a filename. Fixed with an import-presence guard.
Law: when extending a dual-purpose text/filename function, branch on
content shape, not on the caller.

Instrument notes

- Pyright caught a structurally-unreachable branch when the edge driver
  was restructured from `return f"""..."""` to assign-then-patch-then-
  return; fixed before running anything.
- The cons_val smoke one-liner lost `$?` across the wsl.exe boundary
  (the AGENTS 2cd law applies to ALL `$` forms, including `$?` and
  `$(( ))`); the build verdict was read from the log and the olean
  census instead, which is the log-not-exit-code discipline.

Next obligations

1. Remaining 24 diagonal entries (d = 6..29): pure pipeline reruns
   (~6.5 min per owner batch on the current hardware).
2. Partition assembly closure: consume the 30 entry certificates in the
   owner-matrix partition statement.
3. Static consumer, then the complex scalar engine (record 2624 GO
   route: degree-55 complex polynomial, exp(i psi c) rotation mandatory).
