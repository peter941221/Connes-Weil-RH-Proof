# 2891 Route B D4 Cauchy artifact checker

This checker reads the 2889 complex interval enclosure and the 2890 rational
Cauchy remainder assembly. It verifies that:

- the finest reported interval upper bound is below the declared conservative
  `M`;
- the stored remainder exactly replays `M*(r/R)^22/(1-r/R)`;
- the remainder is below the stored Taylor truncation margin;
- both source artifacts explicitly remain nonformal.

This is an artifact consistency gate. It does not replace the missing Lean
proof that the interval generator and Cauchy theorem are sound.
