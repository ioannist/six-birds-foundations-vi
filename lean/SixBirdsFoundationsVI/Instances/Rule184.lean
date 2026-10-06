import Std

namespace SixBirdsFoundationsVI.Instances.Rule184

/-- Boolean occupancy on a cyclic ring. -/
abbrev Config (n : Nat) := Fin n → Bool

/-- A car stays if its right neighbor is occupied; an empty cell receives a car
from its left neighbor. All sites update simultaneously. -/
def step {n : Nat} [NeZero n] (c : Config n) : Config n :=
  fun i => (c i && c (i + 1)) || (!c i && c (i - 1))

def cars {n : Nat} (c : Config n) : Nat :=
  (List.ofFn c).countP id

/-- The two one-car configurations. -/
def left : Config 2 := fun i => i == 0
def right : Config 2 := fun i => i == 1

private theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  have hi := i.isLt
  have hv : i.val = 0 ∨ i.val = 1 := by omega
  rcases hv with h | h
  · left; exact Fin.ext h
  · right; exact Fin.ext h

theorem step_left : step left = right := by
  funext i
  rcases fin2_cases i with h | h <;> rw [h] <;> decide

theorem step_right : step right = left := by
  funext i
  rcases fin2_cases i with h | h <;> rw [h] <;> decide

/-- Conservation holds for every configuration of the two-site ring. -/
theorem cars_conserved_two (c : Config 2) : cars (step c) = cars c := by
  have h : c = fun i => if i == (0 : Fin 2) then c 0 else c 1 := by
    funext i
    rcases fin2_cases i with hi | hi
    · subst i; simp
    · subst i; simp
  rw [h]
  cases h0 : c 0 <;> cases h1 : c 1 <;> simp [cars, step]

/-- A one-car orbit, with an explicitly derived period-two recurrence. -/
def orbit : Nat → Config 2
  | 0 => left
  | t + 1 => step (orbit t)

theorem orbit_even_odd (t : Nat) :
    (orbit (2 * t) = left) ∧ (orbit (2 * t + 1) = right) := by
  induction t with
  | zero => simp [orbit, step_left]
  | succ t ih =>
      obtain ⟨he, ho⟩ := ih
      constructor
      · have h : 2 * (t + 1) = (2 * t + 1) + 1 := by omega
        rw [h, orbit, ho, step_right]
      · have h : 2 * (t + 1) + 1 = (2 * (t + 1)) + 1 := rfl
        rw [h, orbit]
        have he' : orbit (2 * (t + 1)) = left := by
          have h2 : 2 * (t + 1) = (2 * t + 1) + 1 := by omega
          rw [h2, orbit, ho, step_right]
        rw [he', step_left]

theorem orbit_car_conservation (t : Nat) : cars (orbit (t + 1)) = cars (orbit t) := by
  exact cars_conserved_two (orbit t)

theorem orbit_one_car (t : Nat) : cars (orbit t) = 1 := by
  induction t with
  | zero => decide
  | succ t ih => rw [orbit_car_conservation, ih]

/-- Every car moves by one site each step, including through the period wrap. -/
theorem recurrence (t : Nat) (i : Fin 2) :
    orbit (t + 1) (i + 1) = orbit t i := by
  have ht : t % 2 = 0 ∨ t % 2 = 1 := by omega
  rcases ht with he | ho
  · have h : t = 2 * (t / 2) := by omega
    have hnext : t + 1 = 2 * (t / 2) + 1 := by omega
    rw [hnext, (orbit_even_odd (t / 2)).2, h, (orbit_even_odd (t / 2)).1]
    rcases fin2_cases i with hi | hi <;> rw [hi] <;> decide
  · have h : t = 2 * (t / 2) + 1 := by omega
    have hnext : t + 1 = 2 * (t / 2 + 1) := by omega
    rw [hnext, (orbit_even_odd (t / 2 + 1)).1, h, (orbit_even_odd (t / 2)).2]
    rcases fin2_cases i with hi | hi <;> rw [hi] <;> decide

/-- A blocked car is a local `11` defect relative to free flow. -/
def blockedCars {n : Nat} [NeZero n] (c : Config n) : Nat :=
  (List.ofFn (fun i => c i && c (i + 1))).countP id

/-- A jam defect is an occupied site whose next site is occupied. -/
def Jam {n : Nat} [NeZero n] (c : Config n) (i : Fin n) : Prop :=
  c i = true ∧ c (i + 1) = true

def JamFree {n : Nat} [NeZero n] (c : Config n) : Prop :=
  ∀ i, ¬ Jam c i

def LowDensity {n : Nat} (c : Config n) : Prop := 2 * cars c ≤ n

private theorem next_prev {n : Nat} [NeZero n] (hn : 2 ≤ n) (i : Fin n) :
    (i + 1) - 1 = i := by
  apply Fin.ext
  have h1 : ((1 : Fin n) : Nat) = 1 := by
    cases n with
    | zero => omega
    | succ n =>
        cases n with
        | zero => omega
        | succ n => exact Fin.val_one n
  simp only [Fin.val_sub, Fin.val_add, h1]
  have hi := i.isLt
  by_cases hlt : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt]
    have heq : n - 1 + (i.val + 1) = n + i.val := by omega
    rw [heq, Nat.add_mod]
    simp [Nat.mod_eq_of_lt hi]
  · have heq : i.val + 1 = n := by omega
    rw [heq, Nat.mod_self]
    have hval : i.val = n - 1 := by omega
    rw [hval]
    simp [Nat.mod_eq_of_lt (by omega : n - 1 < n)]

private theorem prev_next {n : Nat} [NeZero n] (hn : 2 ≤ n) (i : Fin n) :
    (i - 1) + 1 = i := by
  apply Fin.ext
  have h1 : ((1 : Fin n) : Nat) = 1 := by
    cases n with
    | zero => omega
    | succ n =>
        cases n with
        | zero => omega
        | succ n => exact Fin.val_one n
  simp only [Fin.val_sub, Fin.val_add, h1]
  have hi := i.isLt
  by_cases hz : i.val = 0
  · rw [hz]
    have hlt : n - 1 < n := by omega
    simp only [Nat.add_zero]
    rw [Nat.mod_eq_of_lt hlt]
    have heq : n - 1 + 1 = n := by omega
    rw [heq, Nat.mod_self]
  · have hle : n ≤ n - 1 + i.val := by omega
    rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by omega : n - 1 + i.val - n < n)]
    have heq : n - 1 + i.val - n = i.val - 1 := by omega
    rw [heq]
    have heq2 : i.val - 1 + 1 = i.val := by omega
    rw [heq2, Nat.mod_eq_of_lt hi]

/-- Once every car is unblocked, the next rule-184 state is a one-site shift. -/
theorem free_flow_shift {n : Nat} [NeZero n] (hn : 2 ≤ n)
    (c : Config n) (hfree : JamFree c) (i : Fin n) :
    step c (i + 1) = c i := by
  have hprev := next_prev hn i
  unfold step
  rw [hprev]
  cases hci : c i with
  | false =>
      cases hnext : c (i + 1) with
      | false => simp
      | true =>
          have hnextnext : c ((i + 1) + 1) = false := by
            have hj := hfree (i + 1)
            simp [Jam, hnext] at hj
            exact hj
          simp [hnextnext]
  | true =>
      have hnext : c (i + 1) = false := by
        have hj := hfree i
        simp [Jam, hci] at hj
        exact hj
      simp [hnext]

/-- Free flow is forward invariant under rule 184. -/
theorem free_flow_invariant {n : Nat} [NeZero n] (hn : 2 ≤ n)
    (c : Config n) (hfree : JamFree c) : JamFree (step c) := by
  intro i hjam
  have hleft := free_flow_shift hn c hfree (i - 1)
  have hright := free_flow_shift hn c hfree i
  rw [prev_next hn i] at hleft
  have hci : c i = true := hright.symm.trans hjam.2
  apply hfree (i - 1)
  exact ⟨hleft.symm.trans hjam.1, by simpa [prev_next hn i] using hci⟩

theorem blocked_zero_iff_jam_free {n : Nat} [NeZero n] (c : Config n) :
    blockedCars c = 0 ↔ JamFree c := by
  constructor
  · intro h i hjam
    have hmem : true ∈ List.ofFn (fun j : Fin n => c j && c (j + 1)) :=
      List.mem_ofFn.mpr ⟨i, by simp [hjam.1, hjam.2]⟩
    have hnone := (List.countP_eq_zero.mp h) true hmem
    exact hnone rfl
  · intro hfree
    apply List.countP_eq_zero.mpr
    intro a ha hp
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp ha
    have hand : (c i && c (i + 1)) = true := hi.trans hp
    have hleft : c i = true := (Bool.and_eq_true _ _).mp hand |>.1
    have hright : c (i + 1) = true := (Bool.and_eq_true _ _).mp hand |>.2
    exact hfree i ⟨hleft, hright⟩

/-- Iteration of rule 184 from any finite-ring configuration. -/
def runFrom {n : Nat} [NeZero n] (c : Config n) : Nat → Config n
  | 0 => c
  | t + 1 => step (runFrom c t)

/-- This is the proved tail half of the density-≤1/2 evacuation claim. -/
theorem free_flow_tail {n : Nat} [NeZero n] (hn : 2 ≤ n)
    (c : Config n) (t₀ : Nat) (hstart : JamFree (runFrom c t₀)) :
    ∀ k : Nat, JamFree (runFrom c (t₀ + k)) ∧
      ∀ i : Fin n, runFrom c (t₀ + k + 1) (i + 1) = runFrom c (t₀ + k) i := by
  intro k
  induction k with
  | zero =>
      constructor
      · simpa using hstart
      · intro i
        simpa [runFrom] using free_flow_shift hn (runFrom c t₀) hstart i
  | succ k ih =>
      have hprev : JamFree (runFrom c (t₀ + k)) := ih.1
      have hnext : JamFree (runFrom c (t₀ + (k + 1))) := by
        have heq : t₀ + (k + 1) = (t₀ + k) + 1 := by omega
        rw [heq, runFrom]
        exact free_flow_invariant hn _ hprev
      constructor
      · exact hnext
      · intro i
        have heq : t₀ + (k + 1) + 1 = (t₀ + (k + 1)) + 1 := rfl
        rw [heq, runFrom]
        exact free_flow_shift hn _ hnext i

/-- At density one half, a nonempty jam count need not decrease in one step.
This six-site state is `001011`. -/
def plateau : Config 6 := fun i => (i == 2) || (i == 4) || (i == 5)

theorem plateau_low_density : LowDensity plateau := by unfold LowDensity; decide
theorem plateau_has_jam : Jam plateau 4 := by unfold Jam; decide
theorem plateau_jam_count_stalls :
    blockedCars (step plateau) = blockedCars plateau := by decide

def unresolved (t : Nat) : Nat := blockedCars (orbit t)

theorem unresolved_zero (t : Nat) : unresolved t = 0 := by
  have ht : t % 2 = 0 ∨ t % 2 = 1 := by omega
  rcases ht with he | ho
  · have h : t = 2 * (t / 2) := by omega
    rw [unresolved, h, (orbit_even_odd (t / 2)).1]
    decide
  · have h : t = 2 * (t / 2) + 1 := by omega
    rw [unresolved, h, (orbit_even_odd (t / 2)).2]
    decide

theorem unresolved_nonincreasing (t : Nat) : unresolved (t + 1) ≤ unresolved t := by
  simp [unresolved_zero]

/-! A four-site jam that evacuates after one update. -/
private theorem fin4_cases (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have hi := i.isLt
  have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases hv with h | h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))

def jam : Config 4 := fun i => (i == 0) || (i == 1)
def freeA : Config 4 := fun i => (i == 0) || (i == 2)
def freeB : Config 4 := fun i => (i == 1) || (i == 3)

theorem step_jam : step jam = freeA := by
  funext i
  rcases fin4_cases i with h | h | h | h <;> rw [h] <;> decide

theorem step_freeA : step freeA = freeB := by
  funext i
  rcases fin4_cases i with h | h | h | h <;> rw [h] <;> decide

theorem step_freeB : step freeB = freeA := by
  funext i
  rcases fin4_cases i with h | h | h | h <;> rw [h] <;> decide

def orbit4 : Nat → Config 4
  | 0 => jam
  | t + 1 => step (orbit4 t)

theorem orbit4_tail (t : Nat) : orbit4 (t + 1) = freeA ∨ orbit4 (t + 1) = freeB := by
  induction t with
  | zero => left; exact step_jam
  | succ t ih =>
      rcases ih with h | h
      · right
        have hs : (t + 1) + 1 = t + 1 + 1 := rfl
        rw [orbit4, h, step_freeA]
      · left
        rw [orbit4, h, step_freeB]

theorem jam_has_one_blocked : blockedCars jam = 1 := by decide

theorem orbit4_blocked_zero (t : Nat) : blockedCars (orbit4 (t+1)) = 0 := by
  rcases orbit4_tail t with h | h <;> rw [h] <;> decide

theorem jam_blocked_nonincreasing_after_one (n : Nat) (hn : 1 ≤ n) :
    blockedCars (orbit4 (n + 1)) ≤ blockedCars (orbit4 n) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  have hzero := orbit4_blocked_zero k
  have hzero' : blockedCars (orbit4 n) = 0 := by
    rw [hk]
    simpa [Nat.add_comm] using hzero
  have hnext := orbit4_blocked_zero n
  simp [hzero', hnext]

theorem orbit4_car_conservation (t : Nat) : cars (orbit4 t) = 2 := by
  cases t with
  | zero => decide
  | succ t =>
      rcases orbit4_tail t with h | h <;> rw [h] <;> decide

theorem orbit4_car_step_conserved (t : Nat) :
    cars (orbit4 (t+1)) = cars (orbit4 t) := by
  rw [orbit4_car_conservation (t+1), orbit4_car_conservation t]

private theorem shift_freeA (i : Fin 4) : freeB (i+1) = freeA i := by
  rcases fin4_cases i with h | h | h | h <;> rw [h] <;> decide

private theorem shift_freeB (i : Fin 4) : freeA (i+1) = freeB i := by
  rcases fin4_cases i with h | h | h | h <;> rw [h] <;> decide

/-- After the jam clears, each of the two cars moves one site every step. -/
theorem jam_eventual_recurrence (t : Nat) (i : Fin 4) :
    orbit4 (t + 1 + 1) (i + 1) = orbit4 (t + 1) i := by
  rcases orbit4_tail t with h | h
  · rw [orbit4, h, step_freeA]
    exact shift_freeA i
  · rw [orbit4, h, step_freeB]
    exact shift_freeB i

/-- Every low-density four-cell state clears its jams after one update. -/
theorem low_density_four_one_step (c : Config 4) (h : LowDensity c) :
    JamFree (step c) := by
  have hc : c = fun i =>
      if i == (0 : Fin 4) then c 0 else
      if i == (1 : Fin 4) then c 1 else
      if i == (2 : Fin 4) then c 2 else c 3 := by
    funext i
    rcases fin4_cases i with hi | hi | hi | hi <;> subst i <;> simp
  rw [hc] at h ⊢
  cases h0 : c 0 <;> cases h1 : c 1 <;> cases h2 : c 2 <;>
    cases h3 : c 3 <;> simp [LowDensity, cars, h0, h1, h2, h3] at h <;>
    (intro i; rcases fin4_cases i with hi | hi | hi | hi <;> subst i <;>
      simp [Jam, step, h0, h1, h2, h3] at *)

theorem low_density_four_tail (c : Config 4) (h : LowDensity c) (k : Nat) :
    JamFree (runFrom c (k + 1)) ∧
      ∀ i : Fin 4, runFrom c (k + 2) (i + 1) = runFrom c (k + 1) i := by
  have hstart : JamFree (runFrom c 1) := by
    simpa [runFrom] using low_density_four_one_step c h
  have ht := free_flow_tail (n := 4) (by omega) c 1 hstart k
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ht

#print axioms low_density_four_tail
#print axioms low_density_four_one_step

#print axioms next_prev
#print axioms prev_next
#print axioms free_flow_shift
#print axioms free_flow_invariant
#print axioms blocked_zero_iff_jam_free
#print axioms free_flow_tail
#print axioms plateau_low_density
#print axioms plateau_has_jam
#print axioms plateau_jam_count_stalls
#print axioms fin2_cases
#print axioms fin4_cases
#print axioms step_jam
#print axioms step_freeA
#print axioms step_freeB
#print axioms orbit4_tail
#print axioms jam_has_one_blocked
#print axioms orbit4_blocked_zero
#print axioms jam_blocked_nonincreasing_after_one
#print axioms orbit4_car_conservation
#print axioms orbit4_car_step_conserved
#print axioms shift_freeA
#print axioms shift_freeB
#print axioms jam_eventual_recurrence

#print axioms step_left
#print axioms step_right
#print axioms cars_conserved_two
#print axioms orbit_even_odd
#print axioms orbit_car_conservation
#print axioms orbit_one_car
#print axioms recurrence
#print axioms unresolved_zero
#print axioms unresolved_nonincreasing

end SixBirdsFoundationsVI.Instances.Rule184
