Record 2634: owner-04 entry-(4,4) membership certificate (K04 moment-assembly probe)
Date: 2026-10-09

Result

The result is positive at single-entry scope. `ConnesWeilRH/Dev/ZProbe2628K04.lean`
compiles green on the Linux-native workspace and delivers
`actualOwnerMomentMatrix2351_entry04_mem2628`: the analytic interval
`(analyticMomentInterval2597 4 4)` of record 2597 contains the owner-side
moment integral `momentEntry2351 capturedModulations2584 4 (capturedNodes2584 4)`
in all four coordinates. Supporting deliverables in the same module: the
real-side error bridge `actualFullRealError2628K04` (|integral - center sum|
<= edge charge + 180 panel bounds, all re-derived from K04 sources), the four
numeric support theorems `marginLo2628K04`, `marginHi2628K04`,
`entry04_imLo_nonpos2628K04`, `entry04_imHi_nonneg2628K04`, the chunked
replay chain (six `centersBlock2628K04_*`, six `epsChunk2628K04_*`,
`partitionCentersSum2628K04`, `epsTotal2628K04`), and the verbatim-literal
extraction interface `entry44Interval2628` + `entry44Interval2628_eq`.
Acceptance is triple and file-level: the persisted olean is present, the
full build-log error list is empty, and the `uses sorry` count is zero
(log k04v11, wall clock 4m44.5s, single module, lake 5.0, no -j flag).
The module carries 213 theorems; 60 style-class linter warnings (long
generated lines) remain and are not proof-bearing.

Scope

This certifies exactly one of the 30 diagonal entries. The remaining 29
diagonal entries, the full partition assembly, the static consumer, the
complex scalar engine (record 2624 GO route), Producer GO, SourceRH, and
RH all remain open. Nothing in this record changes a route ruling.

The extraction incident (micro campaign)

`simp`/`norm_num` peeling of `analyticMomentInterval2597 k k` for k = 4
stalls mid-chain: after unfolding, the residual goal keeps
`Matrix.vecCons (row_00 4) (fun i => ...)` with per-row column
applications un-reduced, and no combination of `Matrix.cons_val_zero`,
`Matrix.cons_val'`, `Matrix.head_cons`, succ-chain bridges, or kernel
`rfl` against a cast-shaped target closes it (twelve falsified micro
variants, module MicroIndex2597, builds micro6/micro7 logs). Index 0
peels fine (record 2618's Diagonal2618 works), so the stall is
index-specific.

The route that works is a VERBATIM copy of the target element: read
row_04's fifth element text out of the 2597 source, transplant it token
for token into a local `noncomputable def entry44Interval2628`, and close
`(analyticMomentInterval2597 (Fin.succ^4 0) (Fin.succ^4 0)) =
entry44Interval2628 := rfl` by the kernel - both sides elaborate to the
same literal term, so the defeq check is syntactic (build micro7 green).
The projection-level variant also works (`ComplexRect2427.reLo (2597 ...)
= ComplexRect2427.reLo <verbatim def> := rfl`), and that is the form the
four support theorems use: `have hre : (2597 succ^4 0 succ^4 0).reLo =
<verbatim field> := rfl`, then rewrite and finish with pure-literal
`norm_num`. The first-match regex trap is recorded in the generator: a
first `reLo` match after `analyticMomentInterval2597_row_04` returns
element 1's fraction, not element 5's - the early micro variants targeted
the wrong fraction on top of the peel stall.

The fake-green incident (why three acceptance checks)

Build v6 was read as "hmarginLo green, hmarginHi unsolved" from a
`tail`-truncated error list. Builds v7 through v9 carried TWO hidden
defects above the tail window: (1) the generated `entry44Interval2628`
body re-indented its continuation lines to the same column as the
opening brace, which makes Lean's structure parser close the literal
after the first field (`unexpected identifier; expected '}'` -
reproduced in isolation as micro9), and (2) with that constant broken,
`norm_num [entry44Interval2628]` still "closed" marginHi2628K04 in v7 -
through a sorry-substituted equation lemma, visible only as a
`declaration uses sorry` warning whose column pointed at the simp
argument. A declaration that closes through such a lemma is fake-green
at zero unsolved-goal errors. The acceptance protocol for this record
is therefore three checks together: olean existence, full error-list
grep (no tail windows), and `grep -c 'uses sorry'` = 0. The continuation
indentation law and the full-list law are recorded in AGENTS 2cc.

The centersBlock constants incident

The six `centersBlock2628K04_*` theorems failed from v6 through v10 for
a different reason, also hidden by tail truncation until v10's full-list
read: the template's block proof runs `norm_num [partitionCenter2628K04,
chunkCenters2628K04_N, ...]`, but the K04 `partitionCenter2628K04`
branches reference the imported panel-table constants
`momentPanelIntegralCenter2622K04Pxxx` (the owner-00 template's branches
held numerals directly). Those constants stay as atoms unless named in
the simp set, so the 30-term comparison never becomes numeric. The fix
states each block against its replay LITERAL (exactly the shape of the
already-green `epsChunk2628K04_*`) and unfolds exactly its own 30
panel-table constants; the assembly theorem first rewrites
`totalCenters_replay2628K04`, then the six blocks, leaving a seven-
literal `norm_num`.

Generator as single source of truth

`scripts/generate_moment_assembly_2628_k04.py` re-derives every numeric
fact from the K04 sources (per-panel centers from the 180 panel tables,
per-panel exponents from the actual-panel certificates, the edge charge
from the K04 edge certificate, row-04 endpoints and the entry-(4,4)
element verbatim from the 2597 module), cross-checks the chunked eps
against the nested eps sum, and emits the module. The owner-00 template
residue laws of record 2634 (AGENTS 2cb) are enforced by construction.

Next obligations

1. Parameterize the generator over the remaining 29 diagonal entries
   (the 2597 module carries all 30 rows; the verbatim extraction and
   rfl-bridge pattern is entry-agnostic).
2. Partition assembly closure: consume the 30 entry certificates in the
   owner-matrix partition statement.
3. Static consumer and then the complex scalar engine (record 2624 GO
   route: degree-55 complex polynomial, exp(i psi c) rotation mandatory).
