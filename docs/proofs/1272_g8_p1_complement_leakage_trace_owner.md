# G8 P1 — complement diagonal trace owner

Date: 2026-09-10

Consumer: the healthy-`CompactLog`, selected-detector, same-owner B5/P2
readback `G8SameOwnerReadbackData`.

For the literal G8 cutoff on the fixed source owner, let

```text
D_n = A_n - J J† A_n,      G = g8AdjointShearGram.
```

This brick constructs the concrete Hilbert--Schmidt pair with legs `D_n` and
`G D_n`.  Its trace product is formally

```text
D_n† G D_n,
```

and is trace class along the existing named source basis.  Thus the diagonal
complement in the P0 carrier identity has an actual trace owner.  Together
with the mixed complement pair from record 1271 and its swap, every forced
P0 complement channel may now be entered into the same source-basis scalar
trace ledger.

This is only a legality result.  It proves neither a finite visible-prime
readback nor a sign or limit for a complement channel, and it does not imply
`0 <= qw`.

Evidence: `ConnesWeilRH.Dev.C1G8AdjointShearGram` and its paired Audit module
completed successfully in `build-logs/1272_g8_p1_complement_leakage_pair.log`
(3922 jobs, zero `error:` and `sorryAx`; the audit prints only
`[propext, Classical.choice, Quot.sound]`).

Next: take the P0 operator equality to a same-owner ordinary-trace equality,
then identify the literal metric/Euler trace with the finite visible-prime
boundary expression without removing the cutoff.
