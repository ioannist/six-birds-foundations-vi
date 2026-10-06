# Six Birds Foundations VI

This repository is the public support surface for one paper in the Six Birds
series: modular LaTeX sources, Lean 4 mechanization, an exact-arithmetic
computational laboratory, formalization inventories and gate records, and
vendored Foundations dependencies.

## Paper

- **Six Birds Foundations VI: A Catalog of Dynamical Structural Laws**,
  Preprint v2.0, 27 September 2026: `paper/main.pdf` with its supplement
  `paper/supplement.pdf`.
  DOI (all versions): [10.5281/zenodo.22254288](https://doi.org/10.5281/zenodo.22254288);
  v1.0 (2 September 2026): [10.5281/zenodo.22254289](https://doi.org/10.5281/zenodo.22254289)

The Six Birds corpus through Foundations IV certifies *states*: each of its
laws fixes a single map, quotient, package, or declared finite family and
proves a static classification about it. Nothing in that corpus certifies
*runs*. This paper is the catalog of exactly those laws: thirteen dynamical
structural laws (G1–G13) in four clusters, each stated in the six-part normal
form inherited from Foundations IV and each carrying an unbounded quantifier
that no static row possesses.

The laws were mined from eccentric mathematical problems — Collatz, Goodstein,
Egyptian fractions, reverse-and-add, Recamán, the angel problem, sandpiles,
rule 184, Ducci, aperiodic tilings, Hadwiger–Nelson, Apollonian packings —
treated as theorem detectors. Each law is layer-agnostic: it quantifies over
declared abstract data — carriers, quotients, ledgers, patch systems — in the
Six Birds emergence calculus, so any substrate supplying the data inherits the
classification. The paper solves no open problem and claims none: Collatz,
Erdős–Straus, Lychrel, Recamán, the Langton's-ant highway, Gilbreath, and the
exact chromatic number of the plane all remain open, and each law's nonclaims
say so explicitly.

Every theorem, schema, no-go and countermodel carries a provenance line
directly after its statement, distinguishing recovered standard mathematics,
recovered Six Birds results, elementary facts, and this paper's own sharpened
contributions. Nothing in the paper is labelled new.

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

Appendix A of the paper records, clause by clause, which parts of each printed
statement the Lean covers and which are proved or imported in prose only.

## Build and Verify

Build the manuscript (also emits a flattened source at
`paper/build/main_flat.tex`):

```bash
cd paper && latexmk -pdf main.tex
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
