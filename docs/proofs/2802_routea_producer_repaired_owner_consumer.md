# 2802 Route A producer consumer with repaired-owner charge

The full Route A producer conclusion now consumes the concrete repaired-owner
charge interface from records 2686 and 2801. The remaining owner-specific
obligation is explicit:

```text
actual selected-detector chargeRest
    <= record2686RepairedOwnerTotal2800
```

The theorem does not identify the selected detector with the captured repaired
owner and does not claim `qw >= 0`, `SourceRH`, or RH.
