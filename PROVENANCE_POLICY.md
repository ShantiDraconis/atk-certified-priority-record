# Evidence and authorship protocol
Inventory timestamp: 2026-10-10 (not the date of discovery).

A scientific priority assertion requires an exact mathematical statement, named contributor, earliest independently inspectable dated artifact, full commit SHA, public archive version/DOI, and reproducible source. A later result's mathematical dependency must be established theorem by theorem, not inferred from topic similarity. GitHub commits, hashes, and CI records provide provenance, not independent proof of originality, prize eligibility, or mathematical correctness.

## Status vocabulary
- VERIFIED_KERNEL_SCOPED: exact Lean proposition and imports checked with a reproducible run.
- HISTORICAL_MANIFEST_GREEN: source manifest reports success; original log not yet independently reproduced here.
- STRUCTURAL_RESULT: a proved conditional or intermediate result, not terminal closure.
- OPEN_MATH: terminal result not established.
- PUBLICATION_PENDING: public URL/DOI not independently checked.
- NUMERICAL_INTERVAL_VERIFIED: a numerical statement checked with rigorous interval arithmetic outside the kernel (runs and data pinned); in Lean it enters only as named hypotheses.

## Release gate
1. Inspect the exact source tree and license; do not bulk expose private repos, secrets, personal data or third-party content.
2. Pin full commit SHA and toolchain.
3. Run a clean Lean build and axiom audit, archive the run URL and logs.
4. Publish source snapshot and sha256sum in an immutable release, then DOI.
5. Independently check public visibility and the published artifact content.

Original repositories remain the source of truth. This central repository is a citation index, not a substitute for the formal sources.
