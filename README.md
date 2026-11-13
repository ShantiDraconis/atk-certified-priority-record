# ATK — Certified Priority Record

Inventory date: 2026-10-10. This date is **not** the original date of any mathematical discovery.

## Scope and attribution
Research program: Axiomatic Theorem Kernel (ATK). GitHub account: ShantiDraconis. Research attribution and original dates must be corroborated against signed commits, releases, author metadata, archived manuscripts and independent records. A GitHub username or certificate manifest alone does not establish legal authorship or mathematical novelty.

This repository indexes **historical** verification evidence. It does not claim a new kernel run or proof of any unresolved Millennium problem. A successful Lean build only certifies the exact statements, definitions, axioms and imports in that build.

## Primary verification record
ELYON Claim1–Claim7, scope CLAIM1_TO_CLAIM7_ONLY:
- Source repository: https://github.com/ShantiDraconis/Elyon-Public-Proof
- Source manifest: public/EXTERNAL_CERTIFICATE_COMPLETE.json
- Audited release commit: fed4f79b1b646be824904aa32bd05a5f481791b3
- Historical run: 36050478168
- Audit commit: d95cbb72b0ea671a1e70b6aa773a8f8647944de4
- Audit run: 36049892790
- Proof baseline commit: 6634422c8004966b97c9c96b0f878852dbbd9175
- Proof baseline run: 36048534795
- Lean 4.19.0; mathlib v4.19.0
- Manifest reports source scan GREEN, audit GREEN, kernel build GREEN.
- No global P versus NP proof is claimed.

## Seven-lane historical crosswalk
Source: https://github.com/ShantiDraconis/Elyon-Public-Proof/blob/main/FINAL_FAIL_EXTERNAL_CROSSWALK.md
Archive DOI documented in source: https://doi.org/10.6084/m9.figshare.33990856
Per-lane DOI verification remains pending. These are historical records, not current HEAD attestations.

| Lane | Source repository | Frozen source commit | Certificate package commit | Historical runs | Terminal |
|---|---|---|---|---|---|
| Beal | ShantiDraconis/m-core-beal | 73f1fd7b2a692ea857acaea70e18745f08878c2a | 0a0819ea3800d1a9cf40c2888eb971ad35dda188 | 35641414716, 35641414763, 35641897480 | OPEN_MATH |
| Navier–Stokes | ShantiDraconis/navier-stokes-critical-barrier-audit | 04aa4c0450bba417e83c643de1eb54eb189b7c53 | 99117aaa64280acf8c889b28eade26a8a51f5714 | 35587202636 | OPEN_MATH |
| Riemann | ShantiDraconis/m-core-riemann | d6a291b4563f9021f74ab63cc983d44f079472da | 8a179aee88ba3c7e794169e4e4e4100f5b5e8b32 | 35641657140 | OPEN_MATH |
| Hodge | ShantiDraconis/m-core-hodge | f4918c01d970658e303033c1caf7c2ee0899b342 | a4d9172f8795030dba07beff06109b20fa5fea30 | 35632216335, 35624030040 | OPEN_MATH |
| Yang–Mills | ShantiDraconis/m-core-yang-mills | dc5b45c4b1ec9e435b76f22e156878634dfdb59c | 075c2aee62cc829fe2a5ed10579e8e8475e4d4db | 35632222934, 35624033137 | OPEN_MATH |
| P versus NP | ShantiDraconis/m-core-p-vs-np | e927d32684ae9294bb97f2fa5e66f24e57e085de | 8ca2065ebc829a4c8cefe91062f03677f5396031 | 35632081050, 35632081097, 35629473883, 35629474058, 35629473878 | OPEN_MATH_TWO_EXACT_PRODUCERS |
| BSD | ShantiDraconis/m-core-bsd | 6258a9f9a13cd90193dc7d12927ce3c044fe0da6 | 5a1bb915bd600da469dcf14db61be08092fade48 | 35641972827, 35641972739, 35642114588 | OPEN_MATH |

## Claims registered on 2026-11-13

Machine-readable record: [`inventory/claims-2026-11-13.json`](inventory/claims-2026-11-13.json). Source snapshots with
sha256 are under `snapshots/M-Core/b3c08e45…/` and `snapshots/clay-riemann-proof/8114911…/`. Contributor: Tiago
Paschoalatto Fagliari (GitHub: ShantiDraconis). The registration date is not the discovery date; each claim lists its
earliest dated artifacts.

| Id | Claim | Evidence | Status |
|---|---|---|---|
| ATK-R105 | Exact weighted Báez-Duarte rate: `κ(σ) = 2(σ − Θ)` on `(Θ, 1)`; `PisoPonderado` (Q2(iii)) is a theorem; RH ⟺ rate `2σ₀ − 1` at one fixed `σ₀ ∈ (½, 1)` | proposal R105 (M-Core #176, 2026-10-27; approved 2026-11-05); first commit `b6d3c2a1` (2026-11-05); CI run 42698490788 on `ca9f98c` (CERTIFIED 8882/8882); 61 theorems, standard axioms | VERIFIED_KERNEL_SCOPED |
| ATK-R110-1 | Báez-Duarte rate on a monoid of `L`-functions: ceiling `TaxaDNF σ κ ⟹ L ≠ 0` on `Re s > σ − κ/2`, and the join (one rate of the product certifies every factor) | proposal R110 (M-Core #188, 2026-11-09; approved 2026-11-11); commit `db91159` (2026-11-11); CI run 43026127040 (CERTIFIED 8918/8918); 36 theorems, standard axioms | VERIFIED_KERNEL_SCOPED |
| CRP-CONT-2026 | RH verified numerically up to height `3 000 209 302 471.5`: above Platt–Trudgian 2021 (`T_PT = 3 000 175 332 800`) by 33 969 671.5 units and 145 389 043 zeros, all on `Re s = ½` | Arb/FLINT 3 interval arithmetic, Turing counting, runs 41559243734 (2026-11-03) … 43344579894 (2026-11-13); fixed values `8114911` in clay-riemann-proof; Lean composition `rhAteZ_continuacao43` under 45 named hypotheses (CI 43401888535) | NUMERICAL_INTERVAL_VERIFIED |

All three are first public in ShantiDraconis/atk-math-core-public (`8fee57b`, PolyForm Noncommercial 1.0.0) and
ShantiDraconis/clay-riemann-proof (CC0). DOI: PUBLICATION_PENDING. None of them proves RH, GRH or any Millennium
problem; all stay OPEN_MATH.

## Provenance protocol
1. Preserve original repository and immutable full commit SHA.
2. Fetch the exact source tree and verify theorem statements, assumptions, axiom dependencies, imports and Lean/mathlib versions.
3. Reproduce the referenced workflow; archive the exact log and artifact digest.
4. Record original authored, committed and first-public dates separately; do not infer them from this inventory.
5. Link exact public DOI/version to the artifact checksum.
6. For a later mathematical work, document an exact theorem-level dependency, not merely thematic similarity.

## Publication status
This repository was private when this inventory was written. Publishing this index requires separately changing GitHub repository visibility to PUBLIC. Existing source repositories may have different visibility.