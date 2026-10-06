import Std

namespace SixBirdsFoundationsVI.Instances.IntegerDucci4

abbrev Vec := Fin 4 → Nat

def diff (a b : Nat) : Nat := (a - b) + (b - a)
def step (x : Vec) : Vec := fun i => diff (x i) (x (i + 1))
def maximum (x : Vec) : Nat := max (x 0) (max (x 1) (max (x 2) (x 3)))

private theorem fin4_cases (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have h := i.isLt
  have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases hv with h | h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))

private theorem diff_le (a b m : Nat) (ha : a ≤ m) (hb : b ≤ m) :
    diff a b ≤ m := by
  unfold diff
  omega

theorem component_le_max (x : Vec) (i : Fin 4) : x i ≤ maximum x := by
  rcases fin4_cases i with h | h | h | h <;> subst i <;>
    simp [maximum] <;> omega

theorem maximum_nonincreasing (x : Vec) : maximum (step x) ≤ maximum x := by
  have hh (i : Fin 4) : step x i ≤ maximum x := by
    exact diff_le _ _ _ (component_le_max x i) (component_le_max x (i + 1))
  change max (step x 0) (max (step x 1) (max (step x 2) (step x 3))) ≤ maximum x
  exact Nat.max_le.mpr ⟨hh 0, Nat.max_le.mpr ⟨hh 1, Nat.max_le.mpr ⟨hh 2, hh 3⟩⟩⟩

#print axioms fin4_cases
#print axioms diff_le
#print axioms component_le_max
#print axioms maximum_nonincreasing
end SixBirdsFoundationsVI.Instances.IntegerDucci4

namespace SixBirdsFoundationsVI.Instances.IntegerDucci4
private theorem diff_mod2 (a b : Nat) : diff a b % 2 = (a % 2 + b % 2) % 2 := by
  unfold diff
  omega
#print axioms diff_mod2
end SixBirdsFoundationsVI.Instances.IntegerDucci4

namespace SixBirdsFoundationsVI.Instances.IntegerDucci4
private theorem two_steps_mod2 (x : Vec) (i : Fin 4) :
    step (step x) i % 2 = (x i + x (i + 2)) % 2 := by
  simp only [step, diff_mod2]
  have hidx : (i + 1) + 1 = i + 2 := by apply Fin.ext; simp [Fin.val_add]
  rw [hidx]
  omega
#print axioms two_steps_mod2
end SixBirdsFoundationsVI.Instances.IntegerDucci4

namespace SixBirdsFoundationsVI.Instances.IntegerDucci4
theorem four_steps_even (x : Vec) (i : Fin 4) :
    step (step (step (step x))) i % 2 = 0 := by
  rw [two_steps_mod2]
  have h₁ := two_steps_mod2 x i
  have h₂ := two_steps_mod2 x (i + 2)
  have hidx : (i + 2) + 2 = i := by
    apply Fin.ext
    simp [Fin.val_add]
    have hi := i.isLt
    omega
  rw [hidx] at h₂
  omega
#print axioms four_steps_even
end SixBirdsFoundationsVI.Instances.IntegerDucci4

namespace SixBirdsFoundationsVI.Instances.IntegerDucci4

def double (x : Vec) : Vec := fun i => 2 * x i

def iterate : Nat → Vec → Vec
  | 0, x => x
  | n + 1, x => step (iterate n x)

private theorem diff_double (a b : Nat) : diff (2 * a) (2 * b) = 2 * diff a b := by
  unfold diff
  omega

theorem step_double (x : Vec) : step (double x) = double (step x) := by
  funext i
  exact diff_double (x i) (x (i + 1))

theorem iterate_add (a b : Nat) (x : Vec) :
    iterate (a + b) x = iterate b (iterate a x) := by
  induction b with
  | zero => simp [iterate]
  | succ b ih => simp [iterate, ih]

theorem iterate_double (n : Nat) (x : Vec) :
    iterate n (double x) = double (iterate n x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iterate, ih, step_double]

theorem four_steps_double (x : Vec) :
    ∃ y : Vec, iterate 4 x = double y := by
  let y : Vec := fun i => iterate 4 x i / 2
  refine ⟨y, ?_⟩
  funext i
  have he : iterate 4 x i % 2 = 0 := by
    simpa [iterate] using four_steps_even x i
  simp only [double, y]
  omega

#print axioms diff_double
#print axioms step_double
#print axioms iterate_add
#print axioms iterate_double
#print axioms four_steps_double
end SixBirdsFoundationsVI.Instances.IntegerDucci4

namespace SixBirdsFoundationsVI.Instances.IntegerDucci4

def doublePow : Nat → Vec → Vec
  | 0, x => x
  | k + 1, x => double (doublePow k x)

theorem iterate_doublePow (n k : Nat) (x : Vec) :
    iterate n (doublePow k x) = doublePow k (iterate n x) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [doublePow, iterate_double, ih]

theorem repeated_four_divisibility (k : Nat) (x : Vec) :
    ∃ y : Vec, iterate (4 * k) x = doublePow k y := by
  induction k generalizing x with
  | zero => exact ⟨x, rfl⟩
  | succ k ih =>
      obtain ⟨z, hz⟩ := four_steps_double x
      obtain ⟨y, hy⟩ := ih z
      refine ⟨y, ?_⟩
      have hn : 4 * (k + 1) = 4 + 4 * k := by omega
      rw [hn, iterate_add, hz, iterate_double, hy]
      rfl

theorem maximum_iterate_le (n : Nat) (x : Vec) :
    maximum (iterate n x) ≤ maximum x := by
  induction n with
  | zero => simp [iterate]
  | succ n ih =>
      exact Nat.le_trans (maximum_nonincreasing (iterate n x)) ih

private theorem doublePow_positive_large (k : Nat) (y : Vec) (i : Fin 4)
    (h : 0 < doublePow k y i) : k < doublePow k y i := by
  induction k with
  | zero => exact h
  | succ k ih =>
      change 0 < 2 * doublePow k y i at h
      have hp : 0 < doublePow k y i := by omega
      have hk := ih hp
      change k + 1 < 2 * doublePow k y i
      omega

/-- Every natural four-tuple is zero after at most four times its initial maximum steps. -/
theorem reaches_zero (x : Vec) :
    iterate (4 * maximum x) x = fun _ => 0 := by
  obtain ⟨y, hy⟩ := repeated_four_divisibility (maximum x) x
  have hm := maximum_iterate_le (4 * maximum x) x
  rw [hy] at hm
  funext i
  have hc := component_le_max (iterate (4 * maximum x) x) i
  rw [hy] at hc
  have hz : doublePow (maximum x) y i = 0 := by
    by_cases hp : 0 < doublePow (maximum x) y i
    · have hlarge := doublePow_positive_large (maximum x) y i hp
      omega
    · omega
  simpa [hy] using hz

#print axioms iterate_doublePow
#print axioms repeated_four_divisibility
#print axioms maximum_iterate_le
#print axioms doublePow_positive_large
#print axioms reaches_zero
end SixBirdsFoundationsVI.Instances.IntegerDucci4
