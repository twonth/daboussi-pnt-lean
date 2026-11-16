# Manuscript alignment review â€” 2026-11-16

The author's latest supplied TeX is preserved byte-for-byte in `paper.tex`.
SHA-256: `2876ed969a2ff4c5c82012780d4f69e4740880071f6462ae5c6ba1ba0da6bacd`.

## Alignment

Compared with published commit `38e8bd90d52594c1b74ac69485a09682ed60b489`,
the manuscript changes wording, explanatory detail, equation labels/order, and
bibliography formatting. The hypotheses, mathematical statements and proof
strategy are unchanged. In particular:

- The cutoff remains y >= 2.
- The newly labelled equation (needabs) is already proved by
  `Daboussi.smoothM_log_identity`; (psi-log) by `Daboussi.psi_log_identity`.
- Expanding M(t)-M(u) as a sum does not change the bounded-increment argument.
- The below-cutoff and positive-part arguments retain their existing estimates.
- The smooth comparison, recurrence, centered moment, three ranges and final
  geometric-block contradiction retain the same dependency chain.

No Lean source changes are necessary. All Lean source hashes match the prior
verification manifest. The published Lean sources also match after normalizing
checkout line endings. Challenge.lean and the comparator configuration are unchanged.

The accepted technical reorganizations in README.md and formalization.yaml
remain applicable. In particular, the paper uses partial summation and an
elementary polylogarithmic bound for positive mass; Lean uses Tonelli and the
smooth Euler product. This distinction is retained explicitly, not silently
presented as a line-by-line formalization of the partial-summation calculation.

## Checks for this update

- PASS: exact copy of the author's latest manuscript.
- PASS: no duplicate TeX labels or unresolved internal references.
- PASS: formalization.yaml validates against the official v0.4 schema cached
  with the original package.
- PASS: every Lean source matches its previously verified SHA-256 hash.
- PASS: fresh rebuild of all 38 supporting modules using the pinned Lean and
  mathlib cache. Fresh logs are included in Verification.
- PASS: Proofs, Audit, Challenge, Solution, MainAudit and the umbrella module
  compiled. The 169 supporting axiom reports plus the main theorem audit use
  only propext, Classical.choice and Quot.sound.
- The existing successful comparator record is retained: Lean sources,
  Challenge.lean, and comparator.json are unchanged. No new comparator run
  was needed or performed.
- Initial short-timeout audit attempts timed out. The longer-running main
  theorem axiom checks subsequently completed successfully.
- The earlier comparator run used Windows no-sandbox mode, as documented.
- No PDF compilation or new independent mathematical review is claimed.
