import SixBirdsFoundationsVI.Laws.G4MovingCoverExhaustion

namespace SixBirdsFoundationsVI.Instances.MovingCover

open SixBirdsFoundationsVI.Laws.G4MovingCoverExhaustion

/-- Stage `a` covers the initial interval `[0,a)`. -/
def Region (a t : Nat) : Prop := t < a

/-- The unvisited length from `a` through target `t`. -/
def residual (a t : Nat) : Nat := t + 1 - a

theorem residual_decreases (a t : Nat) (h : 0 < residual a t) :
    residual (a + 1) t < residual a t := by
  unfold residual at *
  omega

theorem covered_of_zero_residual (a t : Nat) (h : residual a t = 0) : Region a t := by
  unfold residual at h
  unfold Region
  omega

theorem residual_eventually_zero (t : Nat) : residual (t + 1) t = 0 := by
  simp [residual]

theorem exhausted : Exhausted Region := by
  intro t
  exact ⟨t + 1, covered_of_zero_residual (t + 1) t (residual_eventually_zero t)⟩

/-- All finite collections of initial intervals miss a target. -/
private theorem member_le_foldmax {a : Nat} {l : List Nat} (h : a ∈ l) :
    a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b bs ih =>
      simp only [List.mem_cons] at h
      simp only [List.foldr_cons]
      rcases h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem finite_leak : FixedLeak (fun _ : Nat => True) Region := by
  intro l _
  refine ⟨l.foldr max 0, ?_⟩
  intro a ha
  have hbound := member_le_foldmax ha
  unfold Region
  omega

theorem no_finite_package (l : List Nat) :
    ¬ (∀ t : Nat, ∃ a : Nat, a ∈ l ∧ Region a t) := by
  exact fixed_package_no_go finite_leak l (by intros; trivial)

#print axioms residual_decreases
#print axioms covered_of_zero_residual
#print axioms residual_eventually_zero
#print axioms exhausted
#print axioms member_le_foldmax
#print axioms finite_leak
#print axioms no_finite_package

end SixBirdsFoundationsVI.Instances.MovingCover
