# Security policy

SQLeanite is a research prototype, not a production database. Do not use it to
protect valuable or adversarial data.

Please report a suspected memory-safety issue, file corruption path, proof/live
path disconnect, or unsound trusted-boundary assumption through a private
GitHub Security Advisory once the public repository is created. Until then,
contact the repository owner privately. Include a minimal database/SQL input,
the Lean toolchain version, platform, and whether the issue reproduces after
reopening the file.

Public reports about unsupported SQL are useful compatibility bugs, but are
not security vulnerabilities when SQLeanite rejects them explicitly.

