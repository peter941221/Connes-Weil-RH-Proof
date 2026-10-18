# 2804 Route B seed cell ledger

Record 2730 already evaluated all 8192 cells but retained only the aggregate
interval sums. Record 2804 exports each cell's exact rational geometry and the
order-4/order-7 upper charge. This makes the finite interior calculation
reviewable and gives the future Lean importer a stable per-cell input shape.

The ledger remains a model artifact until the interval evaluator is connected
to the Lean derivative-jet semantics. It does not by itself prove the finite
integral, the exterior tail, the cardinal pins, SourceRH, or RH.
