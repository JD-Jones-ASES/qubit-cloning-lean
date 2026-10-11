# Disclosure

JD Jones directed this project. Claude (Anthropic) in Claude Code was used throughout, and the original repository was written by
Claude: the papers named in formalization.yaml were read as printed pages (the arXiv versions; the journal prints were
not read), and the certificates, the statements, the standard-library replay, the Lean proofs, the prior-art searches and
the documents were produced in that process. The papers are cited, not copied. `scripts/core_notation_audit.lean` is the
Palomar registry's own renderability audit script (PalomarRegistry/PalomarSubmission), copied with a three-line provenance
comment; no other code is derived from another project, and the neighbouring Lean work named in README.md is cited, not
used. Verification status is stated in VERIFICATION.md. No independent human review or source-author endorsement is claimed.

## Consultation of 2026-10-11

At JD Jones’s request, ChatGPT (OpenAI, GPT-6 Astra Pro with parallel subagents) audited the original commit
`378b68d58f7992ea1a22bc1ffd16a0b1755504da`, checked primary sources, corrected two documentation issues, and wrote
the additions in `FullTradeoff.lean`, `Signed.lean`, `Stability.lean`, the extension replay and integration, the CI
workflow, and the review documents. The original twenty definitions and twenty-seven theorem statements were
preserved. This is an AI-assisted review; it is not an independent human expert review.

The additions were checked using the pinned official Lean frontend at trust level 0, invoked by a Lake script,
because the environment blocks executable-path discovery used by the normal Lean launcher. Exact official
Mathlib caches were used. This was not a modified compiler or a substitute proof checker. The normal CLI/CI
gate and Palomar’s own Comparator/NanoDa checks remain distinct; [REVIEW_VALIDATION.md](REVIEW_VALIDATION.md)
records exactly what was and was not run. No upstream branch, commit, workflow run, or pull request was created
by this consultation because the GitHub integration denied repository writes.
