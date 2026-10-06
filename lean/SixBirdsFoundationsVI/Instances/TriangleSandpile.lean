import SixBirdsFoundationsVI.Laws.G8OdometerAbelianization
import Std

namespace SixBirdsFoundationsVI.Instances.TriangleSandpile
open SixBirdsFoundationsVI.Laws.G8OdometerAbelianization

/-- Three mutually adjacent non-sink sites, each also adjacent to the sink. -/
abbrev Site := Fin 3
abbrev Config := Site → Nat

def legal (v : Site) (c : Config) : Prop := 3 ≤ c v

/-- Legal toppling sends one chip to each other site and one to the sink. -/
def topple (v : Site) (c : Config) : Config :=
  fun w => if w = v then c w - 3 else c w + 1

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
  simp only [legal] at hw ⊢
  simp [topple, Ne.symm hne]
  omega

theorem topple_commute (c : Config) (v w : Site) (hne : v ≠ w)
    (hv : legal v c) (hw : legal w c) :
    topple w (topple v c) = topple v (topple w c) := by
  funext q
  by_cases hqv : q = v
  · subst q
    simp [topple, hne, legal] at *
    omega
  · by_cases hqw : q = w
    · subst q
      simp [topple, hne, Ne.symm hne, legal] at *
      omega
    · simp [topple, hqv, hqw]

theorem h1 : AbelianCompatible topple legal := by
  intro c v w hne hv hw
  exact ⟨legal_preserved c v w hne hw,
    legal_preserved c w v (Ne.symm hne) hv,
    topple_commute c v w hne hv hw⟩

/-- Every legal toppling loses exactly one chip to the sink. -/
theorem chips_drop_one (c : Config) (v : Site) (hv : legal v c) :
    chips (topple v c) + 1 = chips c := by
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
      apply ih
      change chips (topple v x) < chips x
      have hd := chips_drop_one x v hv
      omega)

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
        have hd : chips (topple v x) < chips x := by
          have he := chips_drop_one x v hv
          omega
        obtain ⟨f, r, hr, hf⟩ := rec (topple v x) hd
        exact ⟨f, v :: r, LegalRun.cons hv hr, hf⟩) c

theorem canonical_stabilization (c : Config) :
    ∃ f : Config, ∃ u : Site → Nat,
      (∃ r : List Site, LegalRun topple legal c r f ∧ Stable legal f ∧
        ∀ v, RunCounter r v = u v) ∧
      ∀ f' r', LegalRun topple legal c r' f' → Stable legal f' →
        f' = f ∧ ∀ v, RunCounter r' v = u v := by
  obtain ⟨f, r, hr, hs⟩ := stabilizes c
  refine ⟨f, RunCounter r, ⟨r, hr, hs, fun _ => rfl⟩, ?_⟩
  intro f' r' hr' hs'
  exact partA_order_independent_and_odometer h1 (h2 c) hr' hs' hr hs

#print axioms site_cases
#print axioms legal_preserved
#print axioms topple_commute
#print axioms h1
#print axioms chips_drop_one
#print axioms h2
#print axioms stabilizes
#print axioms canonical_stabilization
end SixBirdsFoundationsVI.Instances.TriangleSandpile
