# Roadmap

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

Larger research directions include a fully verified parser, a closer model of
SQLite's shared-memory WAL-index protocol, torn-sector journal composition,
and machine-checked interoperability over a less bounded portion of the SQLite
file format.

