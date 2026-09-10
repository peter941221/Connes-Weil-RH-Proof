# G8 P0 physical readback — formal closure

Date: 2026-09-10

The existing G8 source cutoff leg was decomposed on the same healthy
`CompactLog` owner as

`A = sourceInclusion ∘ (sourceInclusion† ∘ A) + D`,

where `D` is the named complement leg outside the healthy source image.  The
physical endpoint trace product was then proved exactly as the original G8
trace product plus the internal forward correction, minus the three forced
complement channels:

`C† K C - (C† J† G D + D† G J C + D† G D)`.

This is a formal P0 carrier-alignment result, not a positivity result and not
a new owner or interface.  It records the obstruction that P1 must control;
the complement channels cannot be discarded by definition.

Evidence: `ConnesWeilRH.Dev.C1G8AdjointShearGram` and its paired Audit module
build successfully in
`build-logs/1266_g8_p0_alignment_retry23.log` and
`build-logs/1266_g8_p0_audit.log`; the audit prints only
`[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

Status: formal P0 complete.  Next is P1: prove a same-owner estimate or exact
vanishing theorem for the named complement channels, then continue to the
physical endpoint metric readback (P2).  No G8 positivity claim follows yet.
