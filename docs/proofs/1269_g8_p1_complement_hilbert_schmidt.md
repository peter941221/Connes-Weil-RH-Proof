# G8 P1 — complement-leg Hilbert–Schmidt control

Date: 2026-09-10

For the same healthy `CompactLog` owner and literal finite cutoff, the
complement leg

`D_n = A_n - J J† A_n`

is now proved Hilbert–Schmidt on the named source basis.  The proof keeps the
large cutoff leg opaque and applies the existing bounded-postcomposition and
sum-of-Hilbert–Schmidt lemmas to `A_n` and `-(J J† A_n)`.

This closes the first P1 legality obligation: each of the three complement
channels in record 1267 can now be treated as a legitimate finite-cutoff
trace-channel candidate.  It does not yet prove their trace vanishes, gives no
finite-visible-prime identity, and supplies no `qw` sign.

Evidence: `ConnesWeilRH.Dev.C1G8AdjointShearGram` and its paired Audit module
build successfully in `build-logs/1268_g8_p1_complement_leg.log` (3922 jobs,
zero `error:`/`sorryAx`); the new theorem is audited with the standard three
axioms only.

Next: construct the concrete cross-channel trace ledger using this
Hilbert–Schmidt leg, then compare that finite-cutoff ledger with the selected
finite visible-prime owner.  No generic projection interface or owner change
is permitted.
