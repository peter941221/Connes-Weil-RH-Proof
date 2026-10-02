# 2471 - actual-owner local node upper

Date: 2026-10-02.

The 2469 attachment previously left `nodeUpper` and every node inequality as
external premises.  This record defines the node upper from the current exact
owner itself: at node `-radius + index * step`, use the 2466 indexed panel
whose endpoints are one half-step below and above the node, then multiply its
2467 norm box by the exact exponential weight.

`ownerPanelNodeUpper2471_bound` proves each node inequality directly from the
2467 weighted norm bridge.  The corollary
`ownerPanelStripNorm_le_panelNodeUpper_2471` consumes only the radius,
grid, zero/first/second-order budget comparisons, and constructs all node
bounds internally.  Thus no 2275-capture node number is silently reused.

The composite-node value still needs an independent numerical pricing and
margin certificate; this record does not claim that the resulting bound closes
the selected-detector budget, nor any producer, GO, or RH conclusion.
