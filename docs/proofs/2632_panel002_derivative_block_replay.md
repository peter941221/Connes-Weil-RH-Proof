Record 2632: panel-002 derivative block replay verified in Lean
Date: 2026-10-09

Result

The result is positive: the committed panel-002 derivative block
replay module (commit 56c5bc34, 4460 lines, 1484 theorems) compiles
green on the Linux-native workspace. Exact numbers: `lake build
ConnesWeilRH.Dev.C1RouteAMomentDerivativeBlocks2632P002` returned
exit 0 with "Build completed successfully (778 jobs)" in 32.52 s
(user 18.37 s), zero error, warning, or sorry lines. The emitted
olean (10.9 MB) persists on the ext4 workspace and a rebuild is a
pure cache hit (user 1.7 s). This closes the open instrument question
left by record 2630: the "no compiler output within 120 seconds"
observation was an environment artifact (lake on the /mnt/c mount,
root-caused in record 2631), not a property of the norm_num replay
route. On the Linux-native cache the route is healthy at roughly
22 ms per block theorem.

What the module certifies

Every theorem has the shape `blockValue8 a0 .. a7 = <decimal
literal> := by norm_num [blockValue8]`, where blockValue8 packs eight
base-10^9 chunks (at most 72 decimal digits) into one natural number
by Horner expansion. The 1484 theorems pin, coefficient by
coefficient, the block decomposition of the four canonical operands
of the derivative identity
(i + 1) * primitive[i + 1] = polynomial[i]
for panel 002 of the owner-04 (K04) moment partition: left/right
numerator and left/right denominator, coefficients 0 through 32, at
most 24 blocks (217 decimal digits) per operand. Panel 002 is the
largest block count in the partition; every side of every coefficient
is byte-pinned to its decimal value, and paired left/right theorems
have identical statement text, so block-level equality of the two
fraction sides is visible from the paired statements.

Batch budget measured

All 180 K04 panel tables carry the same shape (polynomial length 34,
primitive length 34, verified with the generator's own parser), so
each panel yields 33 coefficients and about 1484 block theorems. At
the measured rate a full 180-panel derivative-replay batch is about
1.6 hours of serial compilation - a normal single-lane batch for this
repository.

Scope

Arithmetic-input progress only, one level further than record 2630:
the block-level replay of panel 002 is now a closed Lean certificate.
Still open: the carry/assembly step that combines blockValue8 blocks
into whole-operand values inside Lean (the record-2629 carry-row
interface), the full fraction-identity replay per coefficient, the
owner-04 (K04) 180-panel partition assembly (record 2628 pricing),
entry-04 membership, the static consumer, the complex scalar engine,
Producer GO, SourceRH, and any RH claim.

Evidence

- Module: ConnesWeilRH/Dev/C1RouteAMomentDerivativeBlocks2632P002.lean
  (commit 56c5bc34).
- Generator: scripts/generate_derivative_chunk_certificate_2630.py
  (already parameterized by --panel and --coefficients; theorem names
  carry the panel index).
- Data: results/2630_panel002_derivative_chunks.json (panel 002, all
  33 coefficients, Python-side Fraction reconstruction checks pass).
- Verification: Linux-native workspace
  /home/peter/projects/Connes-Weil-RH-Proof, toolchain
  leanprover/lean4:v4.30.0 (pinned, both sides identical), module
  copied from the Windows checkout and md5-compared before the build
  (9b265be491474923e5917565ff2339e1 on both sides).
