# Duplication map — Foundations VI results against the vendored corpus and sibling papers

Method (2026-09-02). (1) Full-text grep of all 53 vendored corpus papers
(`find six-birds-papers -maxdepth 1 -type f -name '*.tex'` → 53 files; command:
`grep -l -i -- "<term>" six-birds-papers/*.tex` per term)
for each law's distinctive vocabulary: bad-tail, solvency, ghost, escrow, amortized, telescop*,
moving cover, exhaustion certificate, carry horizon, reverse-and-add, Recamán, angel, sandpile,
odometer, abelian, rule 184, Langton, Ducci, Gilbreath, aperiodic, Wang tile, chromatic number of the
plane, Hadwiger, Apollonian, thin orbit, Zaremba, Collatz, Goodstein, least action, future-sufficient.
(2) Reading of the theorem statements of every Foundations IV row named as a cousin (F2, F3, F4, F6,
F13a, F19, F27, F34, F40) and of the Holonomy paper's theorems, the AOR asymptotic-soundness theorem,
the Currency paper's C1–C4 definitions, Foundations I's theory-package definition, Foundations II's
P6-drive remark and Foundations III's nonclaim register. (3) Sibling check: Foundations V is not
vendored (see `PRESHIP_AUDIT.md` §0); no sibling paper importing a G-law exists.

External duplication search (2026-09-02, web search; queries recorded verbatim in
`PRESHIP_AUDIT.md` §3): no source stating a ghost-convergence/native-separation discharge schema
or a covering/hole-forming schema for history-generated obstructions was found; one non-peer-reviewed
preprint (a "2-adic finite-certificate descent closure" for 3x+1, PhilArchive) works with related
2-adic descent-certificate ideas. A web search is not strong enough to support the label NEW, so
G1(b) and G6 are labelled SHARPENED + ELEMENTARY, not NEW; the only NEW claim in the paper is the
mining protocol, as a procedure.

Grep outcome: no corpus paper states, names, or proves any G-law or any G-law's countermodel. The
only hits are unrelated word matches: Foundations IV uses "abelian" (sheaves, groups), "ghost"
(Faddeev–Popov ghost fields) and "solvency" (an insurance instantiation); *To Create a Stone* uses
"least-action" for a physics audit; "telescop*" occurs in ordinary prose in eight papers. The
Holonomy paper (and two fixed-support papers) use "future-sufficient" in the single-interface sense
that G5 extends.

## Canonical homes, one row per result

| Result | Nearest corpus content (canonical home) | Relation | Treatment in text |
|---|---|---|---|
| G1(a) bad-tail reduction | Foundations IV **F13a** Hiddenness Normal Form (single-instant hiddenness interface; partial wrapper over opaque source predicates) | differently scoped: F13a fixes one interface; G1(a) is an elementary reduction over a step-indexed membrane family. No corpus statement of G1(a). | cite F13a as cousin; label ELEMENTARY + SHARPENED |
| G1(b) ghost-discharge schema | none in corpus (grep: bad-tail/ghost/solvency absent in this sense); external search inconclusive | — | SHARPENED (typed record) + ELEMENTARY (proof); NEW not claimed |
| G1 Collatz facts (affine ledger, 2-adic ghost −1, 2^L−1 shadowing, cycle condition) | re-derived on the page; Lagarias 1985 survey as background | — | ELEMENTARY |
| G2(a) escrow termination | Foundations IV **F2** Descent–Repair (descent iff split-pair obstruction empty; one quotient, one map); external: Floyd 1967 well-founded ranking; AOR cascade termination uses multiset orderings | differently scoped (F2); identical in mechanism to the classical well-founded-ranking argument | RECOVERED STANDARD (Floyd) + SHARPENED (composed stage-coherence audit as typed record) |
| G2(b) price | external: Kirby–Paris 1982 | identical (imported); the escrow reading is an immediate consequence | RECOVERED STANDARD |
| G3 telescoping | Foundations IV **F27** Conservation as Orbit Descent (orbit-constant quantities); external: Tarjan 1985 potential method | differently scoped (F27); identical algebra to Tarjan's potential method | RECOVERED STANDARD + SHARPENED (currency-legality gate; C5 role) |
| G4 positive / biconditional / no-go | Foundations IV **F4** Local–Global Obstruction (finite patch system, four-status partition) | differently scoped: F4 classifies one finite family; G4 quantifies over an unbounded target family with a stage-indexed certificate. The three G4 clauses are elementary. | cite F4; ELEMENTARY + SHARPENED |
| G4 Fibonacci–Sylvester; Erdős–Straus facts | external: Fibonacci 1202 / Sylvester 1880; Vaughan 1970; Elsholtz–Tao 2013 (verified); Mordell 1969 identities (secondary-sourced only) | identical (imported); prime reduction elementary | RECOVERED STANDARD (Sylvester; Vaughan; Elsholtz–Tao); ELEMENTARY (prime reduction); Mordell identities attributed, not labelled |
| G5 no-go | Holonomy paper `thm:future-sufficient` and `thm:witness-strict-refinement` (single interface: a predictive witness ⇔ strict refinement of predictive→current); Foundations IV **F13a**, **F3** | differently scoped: G5 is the step-indexed family version; the per-depth step is the corpus's split-pair test | RECOVERED SBT (mechanism) + SHARPENED (step-indexed typed record) |
| G5 confinement | none in corpus | elementary induction | ELEMENTARY |
| G5 base-2 orbit of 22 | folklore: Brown (MathPages), OEIS A060382 (informal; no primary publication) | verified on the page | ELEMENTARY; informal sources as background |
| G6 covering / hole-forming | Foundations IV **F6** No-Needles Stability (declared static package); Needle Killer paper (needle definition) | differently scoped (F6 declares the needle up front); the two schemas do not occur in the corpus; external search inconclusive | SHARPENED (typed schemas) + ELEMENTARY (proofs); NEW not claimed |
| G7 escape / confinement / exclusivity | Foundations IV **F6** (no turn index, no adversary); external: angel-problem literature | differently scoped; the certificate typing is this paper's; classical threshold imported | ELEMENTARY + SHARPENED (explicit devil-legality conjunct: scope repair); threshold RECOVERED STANDARD |
| G8.A abelian odometer | Foundations IV **F3** (two routes, one comparison), **F27** (presumes conserved quantity); external: Dhar 1990 | differently scoped (F3, F27); G8.A is the carrier-agnostic form of Dhar's abelian property | RECOVERED STANDARD (Dhar) + SHARPENED (carrier-agnostic, v≠w scope) |
| G8.B least action | external: Fey–Levine–Peres 2010 | **weaker** than FLP: legal-vs-legal only | RECOVERED STANDARD (weaker) + SHARPENED (scope repair) |
| G8 countermodels (b), (d) | none in corpus (Rewriting paper discusses confluence vs flatness but not counters) | minimized falsifiers | SHARPENED + ELEMENTARY |
| G9 positive / negative | Foundations IV **F19** Object Persistence (declared transport); external: rule-184 literature | differently scoped (F19 starts from a declared transport); negative schema elementary | ELEMENTARY + SHARPENED (typed census record); rule 184 RECOVERED STANDARD |
| G10 persistence | Foundations IV **F34** Information Loss (single lossy step legitimacy) | differently scoped; induction elementary | ELEMENTARY + SHARPENED |
| G10 Ducci collapse | external: Chamberland–Thomas 2004; Breuer–Lötter–van der Merwe 2007 (mod-2 linearization) | identical | RECOVERED STANDARD |
| G10 checksum witness | none | own toy | ELEMENTARY |
| G11 | Foundations IV **F4**, **F40** Anomaly/Symmetry Obstruction; external: Robinson 1971 (hierarchy), Berger 1966 | differently scoped; proof shape is Robinson's | RECOVERED STANDARD (mechanism) + SHARPENED (per-period defect certificate as typed record) |
| G12.1 restriction | none (elementary) | — | ELEMENTARY |
| G12.2 orbit radiation | none (elementary equivariance) | — | ELEMENTARY |
| G12.3 bridge | external: de Bruijn–Erdős 1951 | identical (assumed as hypothesis in Lean) | RECOVERED STANDARD |
| G12 Hadwiger–Nelson facts | external: de Grey 2018; Heule 2018; Parts 2020 | identical | RECOVERED STANDARD |
| G13.1 relative density | none (elementary arithmetic) | — | ELEMENTARY + SHARPENED (typed audit record) |
| G13 imports | external: Bourgain–Fuchs 2011; Bourgain–Kontorovich 2014; Haag–Kertzer–Rickards–Stange 2024 | identical (imported) | RECOVERED STANDARD |
| Currency bridge (A),(B) | AOR `def:aor:asymptotic-statuses`, `thm:aor:asymptotic-soundness` | differently scoped and weaker: pure-sequence fragment only, no colimit conclusions, own reading of *contractive* | RECOVERED SBT + ELEMENTARY |
| Currency bridge (C) | AOR statuses; elementary series facts (Rudin) | (i),(iv) = mechanized G3 bounds; (ii),(iii) elementary scalar generalizations | ELEMENTARY |
| C5–C7 roles | Currency paper C1–C4 | extension of the taxonomy | SHARPENED (typed record) |
| Apparatus definitions (theory package, quotients, SAU, needle, statuses, nonclaims) | Foundations I Def. D-TK-THY-01; Holonomy paper; Why Mathematics Even Works (SAU); Needle Killer; AOR; Foundations II `rem:p6-drive`; Foundations III NC-12/14/16/17 | restated from the corpus | cited; nothing restated as this paper's |
| Methodology | none | procedure | NEW (as a procedure, not a theorem) |
