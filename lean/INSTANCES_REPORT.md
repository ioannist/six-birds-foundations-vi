# Foundations VI concrete instances

Build: `cd lean && lake build SixBirdsFoundationsVI` **passes** (83 jobs). All declarations are in new `Instances/` modules and imported by the library root. No existing declaration was changed. No `sorry`, `axiom`, `admit`, or `native_decide` was introduced.

## I1: accelerated Collatz (§G1, `sec_04_cluster_a.tex`, lines 40–85)

`Collatz.stripTwos` returns the power-of-two exponent and remaining factor of an integer; `exponent`, `accelerated`, `orbit`, and `orbitExponent` define the paper's accelerated map and its trajectory. `A` sums the exponents and `B` obeys `B₀=0`, `Bₖ₊₁=3Bₖ+2^Aₖ`. Theorems:

| Declaration | Plain mathematical statement |
|---|---|
| `stripTwos_eq` | The recorded factorization multiplies back to the input. |
| `stripTwos_pow_odd` | Stripping `2^m q` with odd `q` returns exactly exponent `m` and factor `q`. |
| `accelerated_step` | `2^a(n) T(n)=3n+1`. |
| `affine_ledger` | Any trajectory satisfying the accelerated step equations satisfies `2^Aₖ nₖ=3^k n₀+Bₖ` for every `k`. |
| `accelerated_affine_ledger` | The actual defined accelerated orbit satisfies that equation for every `n,k`. |
| `c_one_or_two`, `first_formula` | The recursive split-pair constructor has `c∈{1,2}` and `3n₁+1=2^(m+1)c`. |
| `split_pair` | For every `m≥1`, `n₂=n₁+2^m` agrees with `n₁` modulo `2^m`; `2^(m+1)` divides `3n₁+1`, while `3n₂+1=2^m q` for odd `q`. |
| `split_pair_next_exponent`, `split_pair_prior_exponent` | The defined valuation is `m` for `n₂` and at least `m+1` for `n₁`. |

The paper's exact accelerated ledger and split factorization hold. The request's description of a *fixed* affine ledger on each class modulo `2^k` does not apply to this accelerated map: the valuation can exceed `k`, as `split_pair` shows already for the first step. The map is defined on all natural numbers; the paper's odd-positive restriction is included as a subcase. The 2-adic ghost and logarithmic certificate were outside I1 and remain unformalized.

## I2: binary reverse-and-add (§G5, `sec_05_cluster_b.tex`, lines 198–225)

**Complete for the orbit of 22.** `Value` evaluates most-significant-first binary words, and `ReverseAdd w = Value w + Value w.reverse`. Closed value formulas for all four phases and their reversals yield `transition_01`, `transition_12`, `transition_23`, and `transition_30` for every `r≥2`. `Canonical` means a binary word with leading 1; `canonical_unique` proves uniqueness from its value. `WordStep` selects the canonical word with reverse-and-add value, so `word_transition_01` through `word_transition_30` state the four transitions as **word equalities**, not only value equalities.

`NumericStep` applies reverse-and-add through the canonical word of a number. `numeric_step_on` proves its intended behavior for every represented canonical word. `IsPalindrome` means its canonical word equals its reversal. All four phases are canonical and non-palindromic. `pre_entry_values` and `pre_entry_not_palindromes` are decided on concrete words; `pre_entry_word_transitions` and `pre_entry_orbit` verify `22 → 35 → 84 → 105 → 180 = Value (P0 2)`. `family_closed` and `family_target_free` instantiate G5 `closed_pattern_confinement` in `confined_after_entry`; `orbit_22_never_palindrome` covers every time, including the four pre-entry states. The numeric and word steps use classical choice for representation; uniqueness makes that choice irrelevant on the certified orbit. The construction does not prove that every natural number has a canonical binary word, which is unnecessary for this orbit theorem.

## I3: Ducci (§G10, `sec_06_cluster_c.tex`, lines 440–453)

`Ducci.Shift`, `D`, `Iter`, and `Periodic` describe binary periodic sequences; `Vec`, `liftVec`, `Dvec`, and `IterVec` describe finite cyclic vectors. `iter_add` composes iterations. `iter_pow_two` proves `D^(2^k)f(i)=f(i) XOR f(i+2^k)`. `ducci_nilpotent` makes this zero for period `2^k`. `lift_periodic`, `lift_Dvec`, and `lift_iterVec` connect finite vectors to periodic sequences. `ducci_vector_nilpotent` proves `D^(2^k)=0` on `(F₂)^(2^k)` for every `k`. This holds exactly as the paper states over F₂. The further assertion that every integer Ducci tuple eventually reaches zero needs a divisibility-growth and boundedness argument; it is not proved here.

## I4: G2 native coherence (§G2, `sec_04_cluster_a.tex`, around line 241)

`G2NativeCoherence.NativeStageCoherence` compares escrow at `T k (x k)` with escrow at `x k`. `no_infinite_nonterminal_run_native` uses `Run x T` to rewrite the next state and invokes the unchanged G2 well-foundedness theorem. This fixes the unused-run-hypothesis issue in a new declaration.

I5 rule 184 was not attempted in the earlier I1–I4 task; see J1 below.

## `#print axioms` receipt

Every new theorem has an in-module `#print axioms` command. The build output is:

| Module | Theorems | Axioms reported |
|---|---|---|
| Collatz | `stripTwos_eq`, `stripTwos_pow_odd`, `accelerated_step`, `affine_ledger`, `accelerated_affine_ledger`, `c_one_or_two`, `first_formula`, `split_pair`, `split_pair_next_exponent`, `split_pair_prior_exponent` | `[propext, Quot.sound]` each |
| BinaryReverseAdd | `value_zeros`, `pre_entry_values`, `pre_entry_not_palindromes` | none |
| BinaryReverseAdd | `p1_not_palindrome`, `p2_not_palindrome`, `p3_not_palindrome` | `[propext]` each |
| BinaryReverseAdd | `value_append`, `value_ones`, value formulas, numeric transitions, phase canonicality, `value_lt_pow_length`, `p0_not_palindrome`, and private arithmetic/pre-entry helpers | `[propext, Quot.sound]` each |
| BinaryReverseAdd | `value_injective_same_length`, `canonical_unique`, `numeric_step_on`, `word_step_on`, four word transitions, `not_palindrome_on`, `family_closed`, `family_target_free`, `pre_entry_word_transitions`, `pre_entry_orbit`, `confined_after_entry`, `orbit_22_never_palindrome` | `[propext, Classical.choice, Quot.sound]` each |
| Ducci | `iter_add`, `lift_periodic` | `[propext]` each |
| Ducci | `iter_pow_two`, `ducci_nilpotent`, `lift_Dvec`, `lift_iterVec`, `ducci_vector_nilpotent` | `[propext, Quot.sound]` each |
| G2NativeCoherence | `no_infinite_nonterminal_run_native` | none |

No new theorem depends on `sorryAx` or a project-specific axiom.

## J1: G9 rule 184 (`Instances/Rule184.lean`)

**Status: TEMPLATE; fidelity defect removed.** `Config n = Fin n → Bool` and `step` define rule 184 on a cyclic ring. The four-cell orbit `1100 → 1010 ↔ 0101` is a plain worked example: it has two cars at every time; its one initial blocked-car `11` witness disappears after one step; and for every later step `c_(t+2)(i+1)=c_(t+1)(i)`. A separate two-cell one-car orbit also has immediate one-cell recurrence. All synthetic `Unit` transport data and `CertifiedTransportRegime` claims were deleted. No declaration in this module claims to instantiate G9's absorption conclusion.

**General-ring attempt.** `Jam c i` means `c i = true` and `c(i+1)=true`; `blocked_zero_iff_jam_free` relates this real defect to the computed count. For all `n≥2`, `free_flow_shift` proves a jam-free state advances one cell per step, `free_flow_invariant` preserves that condition, and `free_flow_tail` proves recurrence from any jam-free entry time. The attempted descent by jam count fails: the proved six-cell state `001011` has density 1/2 and a jam, but its jam count remains one after one update (`plateau_jam_count_stalls`). The missing theorem is that **every** low-density run reaches a jam-free state by time `n`; it needs a quantitative interaction argument between jam and hole boundaries, not merely strict count descent. General-ring car conservation is also not proved here. Moreover, G9's existing `CertifiedTransportRegime` demands an assigned defect witness: a jam-free initial state has no actual jam to assign. A certificate for all low-density states with defects typed as jams would therefore need a jam-bearing restriction or a different conclusion. Neither is silently supplied.

## J2: G4 moving cover (`Instances/MovingCover.lean`)

Stage `a` covers `[0,a)` in `ℕ`; the residual at target `t` is `t+1-a` truncated at zero. It strictly decreases while positive and vanishes at stage `t+1`, yielding the unchanged `Exhausted Region`. For any finite list of stages, its maximum endpoint is a missed target; `finite_leak` proves the unchanged `FixedLeak`, and `no_finite_package` applies G4's no-go theorem.

**Status: INSTANTIATED.** Both G4 coverage and finite-package leak have concrete instances for staged intervals. This is an elementary cover, not an Egyptian-fraction application.

## J3: G13 counted sparse exceptions (`Instances/ThinOrbit.lean`)

`CountedFamily.count N` is the length of a duplicate-free list proved to contain **exactly** the family's members at most `N`. `counted_exceptions` proves that an infinite, sublinearly counted family of admissible missed values is a zero-density exception set and refutes full coverage. For powers of two, `power_members_iff` and `power_members_nodup` certify that exact enumeration; `power_count_bound` proves `count(N) ≤ log₂ N+1`, `power_count_sublinear` proves the G13 sublinear predicate, and `powers_relative_zero` applies the existing relative-density theorem with total count `N`. Taking positive naturals as admissible and the represented set to be nonpowers of two gives an infinite, zero-density missed family and failure of full coverage.

**Status: INSTANTIATED-WEAKLY.** The counting/reciprocity-compatibility phenomenon has a concrete arithmetic instance. It says nothing about Apollonian orbits, spectral gaps, or their exceptional set.

## J1–J3 verification

`lake build SixBirdsFoundationsVI` passes (83 jobs). Every new theorem, including private helpers, has an in-module `#print axioms` receipt. Outputs contain only `propext`, `Classical.choice`, and `Quot.sound` (some declarations contain none); no `sorryAx` or project-specific axiom occurs. No existing declaration or paper file was changed. The G9 synthetic certificate bridges were removed.

## Full program, task K (2026-09-26)

**K1 — G3 binary counter: INSTANTIATED.** `BinaryCounter.increment` uses least-significant-bit-first words and extends the word on overflow. `cost_is_bit_changes` identifies the declared cost with the number of flipped bits (including a new high bit); `potential` counts one bits. `amortized_exact` proves cost plus potential change equals 2 for *every* increment. `prefix_h1` supplies G3's H1 with `B=2`, and `n_increments_from_zero` applies the existing `uniform_actual_cost_bound` to obtain at most `2n` changed bits in `n` increments from zero.

**K2 — G8 interacting sandpile: INSTANTIATED ON A CONCRETE CONNECTED GRAPH.** `TriangleSandpile` has three mutually adjacent non-sink sites, each also joined to the sink. Each site has degree 3; a legal toppling sends one chip to each other site and loses one to the sink. `h1` proves that distinct legal topplings preserve cross-legality and commute, including the truncated subtraction at the toppled sites. `chips_drop_one` proves that total chips decrease by exactly one at every legal move, so `h2` excludes infinite legal runs. `stabilizes` constructs a stable run, and `canonical_stabilization` applies G8 Part A to obtain a unique stable configuration and odometer. This is the requested interacting fallback, not the arbitrary finite connected graph. The earlier non-interacting star instance remains as a separate elementary example.

**K3 — G12 Moser spindle: INSTANTIATED COMBINATORIALLY.** `MoserSpindle.edges` lists the paper's eleven edges on seven vertices. `finite_check` formalizes the two-triangle colouring contradiction using finite colour values and `omega`; `spindle_witness` proves there is no proper three-colouring. `no_coloring_of_edge_image` applies G12's `no_global_k_coloring`: any graph admitting an edge-preserving image of this spindle has no proper three-colouring. No Euclidean embedding is asserted.

**K4 — G9 rule 184: PARTIAL, STRENGTHENED.** `Rule184Conservation.cars_conserved` proves car conservation for every ring with at least two cells. It partitions occupied cells into blocked and moving cars, then matches outgoing and incoming cars by a cyclic shift. `Rule184Small.clears_up_to_eight` proves by kernel-checked `decide` on Boolean configurations that every ring with `2 ≤ n ≤ 8` and at most `n/2` cars is jam-free by step `n`. The checks establish earlier entry times: 0 for `n=2,3`, 1 for `n=4,5`, 2 for `n=6,7`, and 3 for `n=8`; the existing free-flow invariant carries them to step `n`. No `native_decide` is used. The all-ring jam-clearing theorem remains unproved. Strict one-step jam-count descent fails on the six-cell plateau in J1; tracking local jam predecessors also did not give a uniform survival bound. A general quantitative jam/hole interaction argument is still needed. General car conservation does not resolve G9's typed-defect issue: initially jam-free states have no actual jam witness to assign.

**K5 — integer Ducci length four: PROVED.** `maximum_nonincreasing` proves the largest entry never grows. `four_steps_even` proves four updates make every entry even. `repeated_four_divisibility` then proves that after `4k` updates every entry is divisible by `2^k`. Combining this with the initial maximum gives `reaches_zero`: every natural four-tuple is the zero tuple after at most four times its initial maximum number of updates. This is a new integer result, beyond the earlier F₂ nilpotence instance.

**Verification.** `lake build SixBirdsFoundationsVI` passes (90 jobs). Every new theorem, including private helpers, has a `#print axioms` receipt in its module. The printed sets contain only Lean's `propext`, `Quot.sound`, and, for the constructive-choice steps in sandpile existence and finite-function case analysis, `Classical.choice`; no `sorryAx` or project-specific axiom appears. Existing declarations and paper files were not changed. No commit was made.
