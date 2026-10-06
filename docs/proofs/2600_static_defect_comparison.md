# 2600 static defect comparison

The generator reconstructs the candidate inverse as exact point rectangles and
uses the 2597 analytic rectangles with the 2598 interval operations. It emits
30 row-split Lean proofs for the 900 inequalities
`rectL1Upper2598(defect interval) <= analyticDefectEntryBounds2595`.

This is a finite rational comparison only. It does not prove that the 2597
analytic rectangles contain the actual integrals.

Independent validator scripts/validate_static_defect_bounds_2600.py recomputes all 900 Fraction bounds and confirms the 30 row sums match the committed 2351 exact check. The digest is stored in esults/2600_static_defect_comparison_validation.json.
