# Roadmap

The paper-oriented compositional program is specified in
[`PAPER_PLAN.md`](PAPER_PLAN.md).  It targets POPL'10 verified-RDBMS parity plus
FSCQ-style durability while preserving the current proof and performance
floors.

The near-term objective is to strengthen the existing verified vertical slice,
not to grow SQL breadth indiscriminately.

1. Prove the remaining SQL parser/translation refinement so supported SQL text
   composes with the existing parsed-command and byte-level theorems.
2. Replace remaining validation fallbacks with certified page-directed paths,
   while keeping malformed external files fail-closed.
3. Extend localized page identity and delta commits to every supported bulk and
   index mutation.
4. Refine more of the concrete syscall behavior into the existing VFS contract
   and expand power-loss experiments across filesystems.
5. Widen SQLite compatibility only when the corresponding executable semantics,
   storage refinement, and live-path theorem can land together.

The 2026-08-13 bulk-mutation gate is complete: 2,000-row bulk load, UPDATE,
and indexed DELETE all measure at approximately 5× C SQLite or better. Mixed
storage-class indexes already use the exact `CertifiedAllValueIndex` path, and
the remaining validating query comparison is confined to explicitly foreign
SQLite files rather than Lean-generated images.

Larger research directions include a fully verified parser, a closer model of
SQLite's shared-memory WAL-index protocol, torn-sector journal composition,
and machine-checked interoperability over a less bounded portion of the SQLite
file format.
