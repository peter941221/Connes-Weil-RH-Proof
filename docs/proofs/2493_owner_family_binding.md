# Record 2493: exact owner-input binding control

`routea_owner_family_binding_2493.py` parses the generated Lean definitions
from `C1RouteAOwnerPanelSample2460.lean` and compares them with the exact
inputs consumed by the 2491 external price. For all 30 families, radius,
modulation, and both real/imaginary midpoint coefficient coordinates match as
`Fraction` values, with no tolerance. The control reports
`EXACT_OWNER_INPUTS_MATCHED`.

This closes only the provenance question for the 2491 inputs. It does not
prove the MPFR bump enclosure, import the 640-cell price as an analytic Lean
bound, discharge the selected-detector producer margin, or claim RH.

Evidence: `scripts/routea_owner_family_binding_2493.py` and
`results/2493_owner_family_binding.json`.
