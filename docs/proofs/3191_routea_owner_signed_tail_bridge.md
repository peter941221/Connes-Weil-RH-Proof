# 3191 Route A Owner-Signed Full-Line Tail Bridge

Status: Lean contract added; no numeric producer supplied.

The bridge accepts a finite-window upper bound and a full-line tail upper
bound only when both are tied by the exact equality

```text
archimedeanTerm + sum(owner node upper)
  = finite_window_upper + full_line_tail_upper
```

The `geometry` parameter is the selected owner and fixes its support, source
zero, detector, and both frequency signs through
`routeAOwnerPhysicalKernelNodeValue`. The bridge then reuses the existing
`RouteAOwnerNodeIntervalCertificate` and `RouteAOwnerPhysicalKernelEnvelope`
interfaces.

This is a contract, not a certificate instance. In particular, the external
2353/3190 tail rows are still not imported into Lean, and no claim about
`SourceRH` or RH follows from this record alone.
