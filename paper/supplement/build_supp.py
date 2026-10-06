#!/usr/bin/env python3
"""Generate the supplement tables of Foundations VI from the Lean sources, the
theorem catalog THEOREMS.md, the dated axiom receipt and the instances report.
Run from the repository root:

    python3 paper/supplement/build_supp.py

Nothing is typed by hand except the map from main-paper items to their law and
Lean declarations (ITEMS below).  Every file and line number is read from the
sources; a declaration that cannot be found stops the script.
"""
import re, pathlib, sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
LEAN = ROOT / "lean"
OUT = pathlib.Path(__file__).resolve().parent

# ---- Lean declarations -------------------------------------------------------
DECL = re.compile(r"(?:noncomputable |protected )*(theorem|lemma|def|structure|inductive|abbrev|instance)\s+([^\s:({\[]+)")
DECLS = {}
for f in sorted((LEAN / "SixBirdsFoundationsVI").rglob("*.lean")):
    rel = f.relative_to(ROOT).as_posix()
    stack = []
    for i, line in enumerate(f.read_text().splitlines(), 1):
        m = re.match(r"namespace (\S+)", line)
        if m:
            stack.append(m.group(1))
            continue
        m = re.match(r"end (\S+)\s*$", line)
        if m and stack and m.group(1) == stack[-1]:
            stack.pop()
            continue
        m = DECL.match(line)
        if m:
            fq = ".".join(stack + [m.group(2)])
            DECLS[fq] = (m.group(1), rel, i)

# ---- Catalog: law headings and their Theorem subsections ----------------------
CAT = {}
cat_lines = (ROOT / "THEOREMS.md").read_text().splitlines()
law = None
for i, line in enumerate(cat_lines, 1):
    m = re.match(r"### (G\d+) - (.*)", line)
    if m:
        law = m.group(1)
        CAT[law] = {"name": m.group(2).strip(), "line": i}
        continue
    if law and line.startswith("#### 2. Theorem") and "thm" not in CAT[law]:
        CAT[law]["thm"] = i
TAG = {}
for line in cat_lines:
    m = re.match(r"- \*\*(G\d+) - [^*]+\*\* \(([^;]+);", line)
    if m:
        TAG[m.group(1)] = m.group(2).replace("`", "")

# ---- Axioms: dated receipt for the laws, instances report for the instances ---
AX = {}
SRC = {}
receipt = (ROOT / "docs" / "lean_axiom_receipts_2026-09-02.txt").read_text()
for m in re.finditer(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])", receipt):
    AX["SixBirdsFoundationsVI.Laws." + m.group(1)] = (
        "none" if m.group(3) is None else ", ".join(a.strip() for a in m.group(3).split(",")))
transcript = (OUT / "instance_axioms_2026-09-26.txt").read_text()
for m in re.finditer(r"'(SixBirdsFoundationsVI\.Instances\.[^']+)' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])", transcript):
    AX[m.group(1)] = "none" if m.group(3) is None else ", ".join(a.strip() for a in m.group(3).split(","))
    SRC[m.group(1)] = "2026-09-26 transcript"
report = (ROOT / "lean" / "INSTANCES_REPORT.md").read_text()
for line in report.splitlines():
    m = re.match(r"\| (Collatz|BinaryReverseAdd|Ducci|G2NativeCoherence) \| (.*) \| (.*) \|$", line)
    if not m:
        continue
    mod, names, axioms = m.groups()
    axioms = axioms.replace("`", "").replace(" each", "").strip("[] ")
    named = re.findall(r"`([^`]+)`", names)
    # The report groups some declarations under a phrase instead of naming them.
    if "numeric transitions" in names:
        named += [f"transition_{t}" for t in ("01", "12", "23", "30")]
    if "four word transitions" in names:
        named += [f"word_transition_{t}" for t in ("01", "12", "23", "30")]
    for nm in named:
        AX[f"SixBirdsFoundationsVI.Instances.{mod}.{nm}"] = axioms
        SRC[f"SixBirdsFoundationsVI.Instances.{mod}.{nm}"] = "instances report"


def tex(s):
    for a, b in [("&", "\\&"), ("%", "\\%"), ("#", "\\#"), ("_", "\\_")]:
        s = s.replace(a, b)
    return s


L = "SixBirdsFoundationsVI.Laws."
I = "SixBirdsFoundationsVI.Instances."
G1, G2, G3 = L+"G1HiddenAmortizedSolvency.", L+"G2TransfiniteEscrow.", L+"G3AmortizedCurrency."
G4, G5, G6 = L+"G4MovingCoverExhaustion.", L+"G5CarryHorizonConfinement.", L+"G6EndogenousNeedleGeneration."
G7, G8, G9 = L+"G7AdversarialMobilityConfinement.", L+"G8OdometerAbelianization.", L+"G9DefectEvacuationTransport."
G10, G11 = L+"G10LossfulPersistence.", L+"G11GlobalAntiSymmetry."
G12, G13 = L+"G12FiniteWitnessRadiation.", L+"G13ThinOrbitSaturation."
C, R, D, N = I+"Collatz.", I+"BinaryReverseAdd.", I+"Ducci.", I+"G2NativeCoherence."
MC, TO, RU = I+"MovingCover.", I+"ThinOrbit.", I+"Rule184."
BC, MS, D4, TS, RC, RS = I+"BinaryCounter.", I+"MoserSpindle.", I+"IntegerDucci4.", I+"TriangleSandpile.", I+"Rule184Conservation.", I+"Rule184Small."

# Main-paper numbered items -> (law, role, Lean declarations).  An empty list
# means the item is argued on paper only.
ITEMS = [
    ("def:collatz", "G1", "instance", [C+"exponent", C+"accelerated", C+"orbit", C+"A", C+"B"]),
    ("thm:affine-ledger", "G1", "instance", [C+"accelerated_step", C+"affine_ledger", C+"accelerated_affine_ledger"]),
    ("thm:split-pair", "G1", "instance", [C+"c_one_or_two", C+"first_formula", C+"split_pair", C+"split_pair_next_exponent", C+"split_pair_prior_exponent"]),
    ("cor:no-residue", "G1", "instance", [C+"split_pair_next_exponent", C+"split_pair_prior_exponent"]),
    ("rem:collatz-paper", "G1", "instance", []),
    ("thm:four-phase", "G5", "instance", [R+"transition_01", R+"transition_12", R+"transition_23", R+"transition_30", R+"word_transition_01", R+"word_transition_12", R+"word_transition_23", R+"word_transition_30", R+"p0_not_palindrome", R+"p1_not_palindrome", R+"p2_not_palindrome", R+"p3_not_palindrome", R+"family_closed", R+"family_target_free"]),
    ("cor:orbit-22", "G5", "instance", [R+"pre_entry_word_transitions", R+"pre_entry_orbit", R+"confined_after_entry", R+"orbit_22_never_palindrome"]),
    ("thm:ducci", "G10", "instance", [D+"iter_pow_two", D+"ducci_nilpotent", D+"ducci_vector_nilpotent"]),
    ("rem:ducci-integer", "G10", "theorem for n = 4; general n on paper", [D4+"step", D4+"maximum_nonincreasing", D4+"four_steps_even", D4+"repeated_four_divisibility", D4+"reaches_zero"]),
    ("def:move-system", "G8", "setting", [G8+"ApplyRun", G8+"LegalRun", G8+"RunCounter", G8+"Stable"]),
    ("def:abelian", "G8", "hypothesis", [G8+"AbelianCompatible"]),
    ("thm:G8", "G8", "Part A, with termination", [G8+"partA_order_independent_and_odometer", G8+"order_independent_stabilization", G8+"odometer_invariance"]),
    ("ex:G8-b", "G8", "case (b)", [G8+"caseB_not_abelian", G8+"caseB_confluent_runs_share_final", G8+"caseB_route_dependent_counter"]),
    ("ex:G8-d", "G8", "case (d)", [G8+"caseD_final_states_distinct", G8+"caseD_nonconfluent_witness"]),
    ("rem:least-action", "G8", "Part B", [G8+"LeastActionMonotonicity", G8+"least_action"]),
    ("prop:G1", "G1", "Part (a)", [G1+"PointwiseLiveness", G1+"EmptyBadTailIntersection", G1+"part_a_reduction"]),
    ("thm:G1b", "G1", "template, Part (b)", [G1+"GhostConvergence", G1+"NativeSeparation", G1+"part_b_discharge"]),
    ("thm:G2", "G2", "theorem", [G2+"no_infinite_nonterminal_run", G2+"not_nonterminal_of_stage_coherence", N+"NativeStageCoherence", N+"no_infinite_nonterminal_run_native"]),
    ("thm:G3", "G3", "theorem", [G3+"telescoping_identity", G3+"telescoping_bound", G3+"amortized_sum_le_scale", G3+"uniform_actual_cost_bound"]),
    ("thm:currency-bridge", "G1--G3", "corollary", []),
    ("thm:G4", "G4", "general statement", [G4+"positive_schema", G4+"conditional_biconditional", G4+"fixed_package_no_go"]),
    ("ex:G3-counter", "G3", "instance", [BC+"increment", BC+"cost_is_bit_changes", BC+"potential_nonnegative", BC+"amortized_exact", BC+"n_increments_from_zero"]),
    ("ex:G8-sandpile", "G8", "instance on three sites; general graphs on paper", [TS+"topple", TS+"h1", TS+"chips_drop_one", TS+"h2", TS+"stabilizes", TS+"canonical_stabilization"]),
    ("ex:G12-moser", "G12", "instance, combinatorial part; embedding on paper", [MS+"edges", MS+"no_fin3_coloring", MS+"spindle_witness", MS+"no_coloring_of_edge_image"]),
    ("ex:G4-intervals", "G4", "instance: exhaustion and leak discharged", [MC+"Region", MC+"residual", MC+"residual_decreases", MC+"exhausted", MC+"finite_leak", MC+"no_finite_package"]),
    ("thm:G5-nogo", "G5", "no-go template", [G5+"UnboundedHorizon", G5+"no_fixed_depth_future_sufficient", G5+"no_future_sufficient_depth"]),
    ("thm:G5", "G5", "confinement", [G5+"closed_pattern_persists", G5+"closed_pattern_confinement"]),
    ("thm:G6", "G6", "template: elementary final steps; rate bridge open", [G6+"DominantPressure", G6+"covering_schema", G6+"DominantObstruction", G6+"hole_forming_schema"]),
    ("thm:G7", "G7", "certificate checks; part 3 needs a state in the invariant", [G7+"escape_never_stuck", G7+"confinement_forces_trap", G7+"escape_confinement_mutually_exclusive"]),
    ("thm:G9-census", "G9", "census bound", [G9+"Census", G9+"census_tail_bound", G9+"census_excludes_unbounded_creation"]),
    ("thm:G9", "G9", "template; Lean has the packaging step only", [G9+"TransportData", G9+"certified_transport_regime_of_assigned_nonzero"]),
    ("prop:rule184", "G9", "partial results for rule 184", [RU+"step", RU+"Jam", RU+"free_flow_shift", RU+"free_flow_invariant", RU+"free_flow_tail", RU+"step_jam", RU+"step_freeA", RU+"step_freeB", RU+"jam_has_one_blocked", RU+"orbit4_blocked_zero", RU+"plateau_low_density", RU+"plateau_has_jam", RU+"plateau_jam_count_stalls", RU+"low_density_four_one_step", RC+"cars_conserved", RS+"clears_up_to_eight"]),
    ("thm:G10", "G10", "general statement", [G10+"boundary_persistence"]),
    ("ex:G10-checksum", "G10", "instance: protection and regeneration discharged", [G10+"checksumD", G10+"checksum_lossful", G10+"checksum_protect", G10+"checksum_regen", G10+"checksum_boundary_persistence"]),
    ("thm:G11", "G11", "template", [G11+"Hierarchy", G11+"ForcedBreaksPeriod", G11+"hierarchy_forces_aperiodic", G11+"g11_global_anti_symmetry"]),
    ("thm:G12", "G12", "theorem", [G12+"no_global_k_coloring", G12+"orbit_radiation"]),
    ("prop:G12-compact", "G12", "bridge", [G12+"CompactnessBridge", G12+"finite_witness_iff_no_global_coloring"]),
    ("thm:G13-density", "G13", "conditional on its count hypotheses", [G13+"relative_density_theorem"]),
    ("ex:G13-powers", "G13", "weak instance: powers of two", [TO+"powers", TO+"power_members_iff", TO+"power_count_sublinear", TO+"powers_infinite", TO+"powers_relative_zero", TO+"counted_exceptions", TO+"concrete_zero_density_failure"]),
    ("thm:G13", "G13", "template; via the density theorem, conditional on its count hypotheses and the imported bound", [G13+"relative_density_theorem"]),
]


def short(fq):
    return fq.replace("SixBirdsFoundationsVI.", "")


missing = [d for _, _, _, ds in ITEMS for d in ds if d not in DECLS]
if missing:
    sys.exit("missing declarations: " + ", ".join(missing))

rows = []
for label, law, role, decls in ITEMS:
    laws = [law] if law in CAT else []
    cat = f"{law}, {role}"
    if laws:
        cat += f" \\newline catalog line {CAT[law].get('thm', CAT[law]['line'])}"
    if decls:
        cells = []
        for d in decls:
            kind, p, line = DECLS[d]
            cells.append(f"\\path{{{short(d)}}} ({kind}) \\newline \\path{{{p}}}:{line}")
        lean = " \\newline ".join(cells)
    else:
        lean = "argued on paper; not formalized"
    rows.append(f"\\Cref{{{label}}} & {cat} & {lean} \\\\")
(OUT / "concordance_rows.tex").write_text("\n".join(rows) + "\n")

# ---- Catalog index: law, catalog tag, catalog lines, status in the paper ------
PAPER = {
    "G1": "template (with a reformulation)", "G2": "general theorem", "G3": "law",
    "G4": "law", "G5": "law (no-go part a template)", "G6": "template", "G7": "general theorem",
    "G8": "law", "G9": "template", "G10": "law", "G11": "template",
    "G12": "law", "G13": "law, weak instance (saturation part a template)",
}
idx = []
for law in sorted(CAT, key=lambda g: int(g[1:])):
    c = CAT[law]
    idx.append(f"{law} & {tex(c['name'])} & {tex(TAG.get(law, ''))} & {PAPER[law]} & {c['line']} \\\\")
(OUT / "catalog_rows.tex").write_text("\n".join(idx) + "\n")

# ---- Axioms of every theorem in the concordance ------------------------------
ax = []
seen = set()
for _, _, _, decls in ITEMS:
    for d in decls:
        if d in seen or DECLS[d][0] not in ("theorem", "lemma"):
            continue
        seen.add(d)
        if d not in AX:
            sys.exit("no axiom record for " + d)
        src = "2026-09-02 receipt" if ".Laws." in d else SRC[d]
        ax.append(f"\\path{{{short(d)}}} & {tex(AX[d])} & {src} \\\\")
(OUT / "axiom_rows.tex").write_text("\n".join(ax) + "\n")

print(f"{len(rows)} concordance rows, {len(idx)} catalog rows, {len(ax)} axiom rows")
