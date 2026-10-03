# Record 2519: production table payload

`C1RouteAExpProductionTable2519.lean` stores the 640 production-remainder
cell readings as exact rational reconstructions of the binary64 `nextUp`
values emitted by the 2517 external artifact.  The payload is split into
16 chunks of 40 entries and is therefore deterministic Lean data.

The exported theorem applies the 2518 table bridge, but retains the complete
per-cell premise
`ownerProductionRemainderTerm2516 sigma index ≤ table[index]`.  No theorem in
this file proves that premise from the stored numbers; the payload is not an
analytic certificate, producer margin closure, or RH result.

The module built successfully with 3896 jobs and the standard axiom trio.
Source artifact SHA256: `FE8EEC1F877F81B380781F7EF130D6540CE7534C017A8237355480415995E761`.
