import SixBirdsFoundationsVI.Laws.G8OdometerAbelianization
import Std

namespace SixBirdsFoundationsVI.Instances.StarSandpile
open SixBirdsFoundationsVI.Laws.G8OdometerAbelianization

/-- Three non-sink leaves, each joined by one edge to the sink. -/
abbrev Config := Fin 3 → Nat
abbrev Site := Fin 3

def legal (v : Site) (c : Config) : Prop := 0 < c v
def topple (v : Site) (c : Config) : Config :=
  fun w => if w = v then c w - 1 else c w

def chips (c : Config) : Nat := c 0 + c 1 + c 2

private theorem site_cases (v : Site) : v = 0 ∨ v = 1 ∨ v = 2 := by
  have h := v.isLt
  have hv : v.val = 0 ∨ v.val = 1 ∨ v.val = 2 := by omega
  rcases hv with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

theorem legal_preserved (c : Config) (v w : Site)
    (hne : v ≠ w) (hw : legal w c) : legal w (topple v c) := by
  simpa [legal, topple, Ne.symm hne] using hw

theorem topple_commute (c : Config) (v w : Site) (hne : v ≠ w) :
    topple w (topple v c) = topple v (topple w c) := by
  funext q
  by_cases hqv : q = v
  · subst q
    simp [topple, hne]
  · by_cases hqw : q = w
    · subst q
      simp [topple, Ne.symm hne]
    · simp [topple, hqv, hqw]

theorem h1 : AbelianCompatible topple legal := by
  intro c v w hne _hv hw
  exact ⟨legal_preserved c v w hne hw,
    legal_preserved c w v (Ne.symm hne) _hv,
    topple_commute c v w hne⟩

theorem chips_decrease (c : Config) (v : Site) (hv : legal v c) :
    chips (topple v c) < chips c := by
  rcases site_cases v with h | h | h <;> subst v <;>
    simp [chips, topple, legal] at * <;> omega

theorem h2 (c : Config) : TerminatesFrom topple legal c := by
  have hw : WellFounded (InvImage Nat.lt chips) :=
    InvImage.wf chips Nat.lt_wfRel.wf
  exact Acc.ndrecOn (C := fun x => TerminatesFrom topple legal x) (hw.apply c)
    (fun x _ ih => by
      constructor
      intro y hstep
      obtain ⟨v, hv, rfl⟩ := hstep
      exact ih _ (chips_decrease x v hv))

theorem stabilizes (c : Config) :
    ∃ f : Config, ∃ r : List Site, LegalRun topple legal c r f ∧ Stable legal f := by
  classical
  let wf : WellFounded (InvImage Nat.lt chips) :=
    InvImage.wf chips Nat.lt_wfRel.wf
  exact wf.fix (C := fun c =>
    ∃ f : Config, ∃ r : List Site, LegalRun topple legal c r f ∧ Stable legal f)
    (fun x rec => by
      by_cases hs : Stable legal x
      · exact ⟨x, [], LegalRun.nil x, hs⟩
      · have hex : ∃ v, legal v x := Classical.byContradiction (fun hn =>
          hs (fun v hv => hn ⟨v, hv⟩))
        obtain ⟨v, hv⟩ := hex
        obtain ⟨f, r, hr, hf⟩ := rec (topple v x) (chips_decrease x v hv)
        exact ⟨f, v :: r, LegalRun.cons hv hr, hf⟩) c

/-- Every configuration has one stable result and one firing-count vector. -/
theorem canonical_stabilization (c : Config) :
    ∃ f : Config, ∃ u : Site → Nat,
      (∃ r : List Site, LegalRun topple legal c r f ∧ Stable legal f ∧
        ∀ v, RunCounter r v = u v) ∧
      ∀ f' r', LegalRun topple legal c r' f' → Stable legal f' →
        f' = f ∧ ∀ v, RunCounter r' v = u v := by
  obtain ⟨f, r, hr, hs⟩ := stabilizes c
  refine ⟨f, RunCounter r, ⟨r, hr, hs, fun _ => rfl⟩, ?_⟩
  intro f' r' hr' hs'
  obtain ⟨he, hu⟩ := partA_order_independent_and_odometer h1 (h2 c)
    hr' hs' hr hs
  exact ⟨he, hu⟩

/-- G8 gives a unique final configuration and firing count for any two stabilizations. -/
theorem unique_stable_and_odometer {c f₁ f₂ : Config} {r₁ r₂ : List Site}
    (hr₁ : LegalRun topple legal c r₁ f₁) (hs₁ : Stable legal f₁)
    (hr₂ : LegalRun topple legal c r₂ f₂) (hs₂ : Stable legal f₂) :
    f₁ = f₂ ∧ ∀ v : Site, RunCounter r₁ v = RunCounter r₂ v :=
  partA_order_independent_and_odometer h1 (h2 c) hr₁ hs₁ hr₂ hs₂

#print axioms site_cases
#print axioms legal_preserved
#print axioms topple_commute
#print axioms h1
#print axioms chips_decrease
#print axioms h2
#print axioms stabilizes
#print axioms canonical_stabilization
#print axioms unique_stable_and_odometer
end SixBirdsFoundationsVI.Instances.StarSandpile
