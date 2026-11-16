# Manuscript bibliography update — 2026-11-16

This review supersedes the manuscript identification in
[the earlier review](manuscript-update-2026-11-16.md); that document's build
results remain a historical record for the unchanged Lean sources.

The latest supplied TeX is preserved byte-for-byte in `paper.tex`.
SHA-256: `f3b59d60ee52ca1ea54422499ad636357420f3b77ce113967ced02aae95f5b04`.

The supplied `Daboussi-4.pdf` is preserved byte-for-byte as `paper.pdf`.
SHA-256: `d7845110fd1f881955e879855250e179b54bf0eeaa98b13d57a3dbb0e6fbb99f`.

Compared with commit `e35e5515bff006aea217095c8a584866d92fbac3`,
the TeX changes only:
- The title from “revisited” to “reconsidered”.
- The Tenenbaum–Mendès France citation to specify chapter, sections and pages.
- The introductory wording of the reference for Mertens' estimates.
- The Baas–Skau entry to link to the extended Selberg interview.

The abstract, theorem statements, proof steps and equation labels are unchanged.
No Lean sources, challenge, comparator configuration, pinned dependencies or
previous verification logs were changed. The existing proof alignment and
documented technical reorganizations remain applicable.

Checks for this revision: inspected the full TeX diff; verified the PDF includes
the clickable interview link; preserved the supplied files exactly.
No new Lean build, comparator run, PDF compilation or independent mathematical
review is claimed for this editorial update.
