# 2372 - Binding corr-D2 panel price

日期：2026-10-02。

The four-channel 2371 price shows that the simple 2348 second-derivative
remainder is currently binding on `corr_D2`: at 240001 nodes its price is
`131353.39607658036`, versus the directed pointwise node-integral reading
`125446.71132157759`, a ratio `1.0470852100686898`. Thus the current grid and
global derivative-budget curvature bound do not close this discrete-to-strip
obligation.

Keeping the same curvature formula, the estimated node counts for remainder
ratios `0.5`, `0.1`, and `0.01` of that directed reading are respectively
`347311`, `776610`, and `2455854`. These are planning figures, not a license
to claim a refinement certificate; the next admissible move is either a
same-owner refined evaluator with all controls or a sharper higher-order
panel enclosure.

Status: `CURRENT_GRID_PANEL_BOUND_NOT_CLOSING`; producer GO: `false`.
