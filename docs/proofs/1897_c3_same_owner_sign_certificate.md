# 1897 - C3' same-owner sign certificate

Date: 2026-09-23.

Status: formally verified conditional B5 producer interface. No detector sign
estimate, positivity theorem, or RH statement is proved.

`CarrierTwoSpanSignCertificate` packages, for one carrier frequency and one
envelope pair:

- support bounds for both modulated tests;
- positivity of the second test's complete-gate pivot;
- either orientation of the opposite Archimedean and prime diagonal signs;
- nonnegativity of the directed Archimedean/prime pair product.

Its `toDeterminantCertificate` conversion obtains the complete determinant
budget from the 1896 sign consumer. Its `gate` theorem sends that data directly
to `orbitWindowSemiLocalGate`. The package prevents sign and support evidence
from being silently taken from different carriers or envelope pairs.

This is only a lower-data/API brick. The actual selected detector still lacks
all required sign suppliers. In particular, the paper-level σ-shift expansion
has an envelope-dependent remainder, so `σ(-γ) < 0` alone does not establish
the sign of every carrier-square Archimedean term.

Verification: focused WSL build log `1897_sign_owner_try2.log`; successful
footer for 3788 jobs, zero `error:` lines, zero `sorryAx`, and the new Audit
declarations depend only on `[propext, Classical.choice, Quot.sound]`.
