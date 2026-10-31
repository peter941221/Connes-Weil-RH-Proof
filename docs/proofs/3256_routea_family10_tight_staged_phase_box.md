Record 3256: family-10 tight staged phase box

Status: verified tight numerical phase enclosure; no aggregate sign claim.

This record replaces the deliberately broad boxes from 3252 with rational
boxes propagated by the exact four-corner interval multiplication used by
`ComplexRect2427.mul`. The base box is checked against the 26th-order Taylor
rectangle; each later box is checked only against the preceding rectangle
product. Stages 1 through 9 use outward-rounded rational endpoints at
approximately `1e-15` resolution, because the earlier `1e-12` endpoint width
did not contain the exact stage-1 product lower bound.

The final theorem encloses the exact full phase after the 512th-power identity.
The focused WSL2 Lean 4.30.0 build and audit pass, and all three audited
theorems use exactly `[propext, Classical.choice, Quot.sound]`. The result is
now suitable for multiplying by the exact coefficient and combining with other
family boxes. It does not yet prove the shared coefficient-phase block sign or
`producer_go`.