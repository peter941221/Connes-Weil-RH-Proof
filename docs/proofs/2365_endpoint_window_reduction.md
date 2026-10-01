# 2365 - Endpoint reduction for coordinate segments

日期：2026-10-02。

The symmetric owner transfer from 2364 is now wrapped by
`correctedPhysical_weighted_coordinate_transfer_of_endpoint_window2359`.
The auxiliary theorem `owner_coordinate_segment_mem_window2359` proves that
two endpoint memberships in the closed owner window imply membership of the
whole interval between them. Thus a future node certificate only needs to
establish window containment for the stored and affine coordinates; no
separate per-node segment-containment ledger is required.

This is a geometric Lean reduction, not a numerical import. The stored-grid
endpoint facts, displacement maximum, directed accumulation, and trapezoid
remainder remain separate obligations.

Status: `ENDPOINT_REDUCED_OWNER_BRIDGE_ONLY`; producer GO: `false`.
