# CHANGE-REQUESTS — DiscoveryKernel signature (FREEZE-1)

The `DiscoveryKernel` signature in `R2_Detector/Defs.lean` is frozen at
FREEZE-1. Any agent needing a signature change must HALT its work and append
a request here (date, requesting tier, exact change, why instantiation is
impossible without it). The orchestrator pauses all agents, arbitrates, and
rebroadcasts the verdict.

Expected number of requests: zero or one. More than one means the signature
was wrong — stop and reconsider rather than iterating live.

*(no requests)*
