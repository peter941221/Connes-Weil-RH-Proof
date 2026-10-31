# 3247: Route A shared-bump cancellation block

Status
------

Lean-verified exact block identity and enclosure interface. No strict sign,
finite aggregate, full-line tail, producer_go, SourceRH, or RH claim follows
yet.

Structural fact
---------------

The owner stores the same width for every family from 8 through 29. Therefore
their physical bump is exactly the same function at the 17168 midpoint. The
block can be rewritten without approximation as:

    sum[i = 8..29] bump_i * coefficient_i * phase_i
      = common_bump * sum[i = 8..29] coefficient_i * phase_i

The new module proves the shared width equality, common bump rectangle
membership, coefficient-phase aggregate rectangle membership, shared block
rectangle membership, and the exact equality between the block target and the
original family sum.

Files
-----

    ConnesWeilRH/Dev/C1RouteAConcreteOwnerSharedBumpBlock3247.lean
    ConnesWeilRH/Dev/C1RouteAConcreteOwnerSharedBumpBlock3247Audit.lean

Verification
------------

Built with lake in the Linux-native WSL2 ext4 workspace using the repository
toolchain leanprover/lean4:v4.30.0 and Lean 4.30.0. All audited theorems use
exactly propext, Classical.choice, and Quot.sound.

Why it matters
--------------

The previous 3243/3245 construction multiplied every family independently,
which widened cancellation before summation. Record 3247 moves the common
bump outside the 22-family phase aggregate, preserving the owner identity and
the signed phase cancellation needed by the producer route.
