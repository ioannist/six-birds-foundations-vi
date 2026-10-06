# Six Birds Foundations VI

This repository is the public support surface for one paper in the Six Birds
series: modular LaTeX sources, Lean 4 mechanization, an exact-arithmetic
computational laboratory, formalization inventories and gate records, and
vendored Foundations dependencies.

## Paper

- **Six Birds Foundations VI: A Catalog of Dynamical Structural Laws**,
  Preprint v2.0, 6 October 2026: `paper/main.pdf` with its supplement
  `paper/supplement.pdf`.
  DOI (v2.0): [10.5281/zenodo.23187548](https://doi.org/10.5281/zenodo.23187548);
  DOI (all versions): [10.5281/zenodo.22254288](https://doi.org/10.5281/zenodo.22254288);
  v1.0 (2 September 2026): [10.5281/zenodo.22254289](https://doi.org/10.5281/zenodo.22254289)

A static structural law classifies fixed data. Many questions about dynamics
concern runs instead: whether every orbit eventually descends, whether a run
terminates while its presentation changes, whether a cover must move with its
target. The paper states thirteen candidate laws of this kind, G1–G13, in the
Six Birds emergence calculus, and sorts them by what is proved. Seven are laws,
each with a concrete system in which the difficult hypothesis is proved (for
G13 only a small arithmetic example): G3, G4, G5, G8, G10, G12 and G13. Two
are general theorems with imported classical instances: G2 and G7. Four are
templates, whose implication is proved while the difficult hypothesis remains
an open obligation: G1, G6, G9 and G11.

The concrete results are checked in Lean: the exact affine ledger of the
accelerated Collatz map and its split pairs at every depth, the orbit of 22
under binary reverse-and-add, nilpotence of the Ducci map on binary vectors of
length 2^k, and order independence for move systems whose distinct legal moves
commute. Classical results are imported with attribution, nothing is labelled
new, and the Collatz, Erdős–Straus, Lychrel and Recamán problems remain open.

## What This Repository Provides

- Modular LaTeX sources under `paper/`, with the release identity (DOI,
  version, assembly date) generated into `paper/includes/release_metadata.tex`.
- Lean 4 mechanization of each law's abstract core under `lean/`: thirteen
  law files, Mathlib-free with zero imports, no `sorry`, no `admit`, and no
  project-declared axioms.
- An exact-arithmetic computational laboratory under `lab/`, with committed
  predictions and eighteen recorded lab verdicts under `lab/results/`.
- Per-law gate panels, deep-dive notes, kernel-axiom receipts, the interaction
  matrix, and formalization manifests under `formalization/`.
- The frozen target-state law catalog at `THEOREMS.md`.
- Verification and provenance records under `docs/`: duplication map,
  external anchors, source deviations, and kernel-axiom receipts.
- Vendored Six Birds Foundations dependencies under `lean/vendor/foundations/`.

The last column of the paper's catalog table, Section 8, and the supplement's
source concordance and formal status record which parts of each printed
statement the Lean covers and which are argued on paper or imported.

## Build and Verify

Build the manuscript and its supplement (also emits flattened sources at
`paper/build/main_flat.tex` and `paper/build/supplement_flat.tex`); each
document is built again so that its references into the other resolve:

```bash
cd paper && latexmk -pdf main.tex && latexmk -pdf supplement.tex \
  && latexmk -g -pdf main.tex && latexmk -g -pdf supplement.tex
```

Build the Lean project:

```bash
cd lean && lake build
```

Run the laboratory test suite:

```bash
pip install -e "lab[dev]" && pytest lab/tests
```

Run the imported-foundations audit:

```bash
python3 scripts/audit_foundations_dependencies.py
```

All four run in continuous integration (`.github/workflows/ci.yml`).

## Repository Layout

- `paper/` — modular manuscript sources, the built main and supplement PDFs,
  bibliography, and Zenodo submission records.
- `lean/` — the pinned Lean 4 project; `lean/vendor/foundations/` holds
  vendored upstream Foundations dependencies.
- `lab/` — the laboratory package, committed predictions, and recorded
  verdicts.
- `formalization/` — manifests, per-law gate panels, deep-dive notes, and the
  interaction matrix.
- `docs/` — verification and provenance records.
- `scripts/` — packaging and audit utilities.
- `THEOREMS.md` — the frozen target-state law catalog.

## Notes

- The LaTeX toolchain requires `latexmk` and a TeX distribution containing the
  packages used by the manuscript.
- The Lean toolchain is pinned in `lean/lean-toolchain`
  (`leanprover/lean4:v4.28.0`).
- The laboratory requires Python 3.11 or later.
- Some records cite internal working documents (the design record and the
  pre-ship audit) that are not part of this repository; the paper,
  `THEOREMS.md`, and `docs/` are authoritative.
- Third-party vendored code remains under its upstream license terms.
- The manuscript is distributed under CC-BY 4.0, as stated on its first page.
