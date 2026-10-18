# 2819 Route B exterior distance lower bound

For `t >= T > 0` and an active node height `y`, this record proves
`t * (1 - |y|/T) <= |t-y|`.  It is the denominator bound used by the
two-sided exterior envelope in the 2729 audit.

This is only the geometric denominator inequality; it does not certify the
stored node list, D-table, row-B coefficients, tail constants, cardinal pins,
SourceRH, or RH.
