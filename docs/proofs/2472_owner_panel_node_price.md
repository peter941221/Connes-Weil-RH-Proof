# 2472 - diagnostic price of the actual-owner node panels

Date: 2026-10-02.

The 2471 node function was evaluated on the exact owner radius with ten equal
cells, using both strip signs `sigma = -1/2` and `sigma = 1/2`.  The probe
uses the repaired coefficient balls, frozen family parameters, the 2471
half-step geometry, and the same interval rectangle arithmetic at every node.

The largest weighted node reading is about `4.1553e3` at the central node;
the composite node readings are about `8.2791e3` and `8.2762e3` for the two
signs.  This is a routing price only: the evaluator uses high-precision
transcendental values and is explicitly not a directed-rounding certificate.

The result therefore does not close the strip margin.  It establishes the
next concrete task: replace this diagnostic with directed bounds (or a Lean
literal enclosure) and combine it with the owner-specific order-1/order-2
budgets and curvature term.  No old 2275 node certificate, producer gate,
GO conclusion, or RH claim is used.
