import SixBirdsFoundationsVI.Laws.G2TransfiniteEscrow

namespace SixBirdsFoundationsVI.Instances.G2NativeCoherence

open SixBirdsFoundationsVI.Laws.G2TransfiniteEscrow

/-- The escrow comparison is made on the actual native transition. -/
def NativeStageCoherence {X W : Type} {P : Nat → Type}
    (x : Nat → X) (T : Nat → X → X) (A : X → Prop)
    (pi : (k : Nat) → X → P k) (e : (k : Nat) → P k → W)
    (wlt : W → W → Prop) : Prop :=
  ∀ k, ¬ A (x k) →
    wlt (e (k + 1) (pi (k + 1) (T k (x k)))) (e k (pi k (x k)))

/-- Native coherence plus the run equation rules out an infinite nonterminal run. -/
theorem no_infinite_nonterminal_run_native {X W : Type} {P : Nat → Type}
    {x : Nat → X} {T : Nat → X → X} {A : X → Prop}
    {pi : (k : Nat) → X → P k} {e : (k : Nat) → P k → W}
    {wlt : W → W → Prop}
    (hrun : Run x T) (hcoh : NativeStageCoherence x T A pi e wlt)
    (hwf : WellFounded wlt) (hnonterminal : Nonterminal x A) : False := by
  apply no_infinite_nonterminal_run hrun
  · intro k hk
    rw [hrun k]
    exact hcoh k hk
  · exact hwf
  · exact hnonterminal

#print axioms no_infinite_nonterminal_run_native

end SixBirdsFoundationsVI.Instances.G2NativeCoherence
