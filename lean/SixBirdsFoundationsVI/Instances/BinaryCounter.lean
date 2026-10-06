import SixBirdsFoundationsVI.Laws.G3AmortizedCurrency

namespace SixBirdsFoundationsVI.Instances.BinaryCounter
open SixBirdsFoundationsVI.Laws.G3AmortizedCurrency

def increment : List Bool → List Bool
  | [] => [true]
  | false :: xs => true :: xs
  | true :: xs => false :: increment xs

def cost : List Bool → Int
  | [] => 1
  | false :: _ => 1
  | true :: xs => 1 + cost xs

/-- Bit changes, counting a newly created high bit as one change. -/
def changed : List Bool → List Bool → Int
  | [], ys => ys.length
  | xs, [] => xs.length
  | b :: xs, c :: ys => (if b = c then 0 else 1) + changed xs ys

private theorem changed_self (xs : List Bool) : changed xs xs = 0 := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [changed, ih]

theorem cost_is_bit_changes (xs : List Bool) :
    cost xs = changed xs (increment xs) := by
  induction xs with
  | nil => decide
  | cons b xs ih =>
      cases b <;> simp [cost, changed, increment, ih, changed_self]

def potential : List Bool → Int
  | [] => 0
  | false :: xs => potential xs
  | true :: xs => 1 + potential xs

theorem potential_nonnegative (xs : List Bool) : 0 ≤ potential xs := by
  induction xs with
  | nil => simp [potential]
  | cons b xs ih => cases b <;> simp [potential] <;> omega

theorem cost_nonnegative (xs : List Bool) : 0 ≤ cost xs := by
  induction xs with
  | nil => simp [cost]
  | cons b xs ih => cases b <;> simp [cost] <;> omega

theorem amortized_exact (xs : List Bool) :
    cost xs + potential (increment xs) - potential xs = 2 := by
  induction xs with
  | nil => decide
  | cons b xs ih =>
      cases b
      · simp [increment, cost, potential]; omega
      · simp [increment, cost, potential]; omega

def runPrefix (xs : List Bool) : Nat → RunPrefix (List Bool)
  | 0 => []
  | n + 1 => (cost xs, increment xs) :: runPrefix (increment xs) n

theorem prefix_length (xs : List Bool) (n : Nat) : (runPrefix xs n).length = n := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => simp [runPrefix, ih]

theorem prefix_actual (xs : List Bool) (n : Nat) :
    NonnegativeActualCosts (runPrefix xs n) := by
  induction n generalizing xs with
  | zero => trivial
  | succ n ih => exact ⟨cost_nonnegative xs, ih (increment xs)⟩

theorem prefix_h1 (xs : List Bool) (n : Nat) :
    AllLe (AmortizedCostList potential xs (runPrefix xs n)) 2 := by
  induction n generalizing xs with
  | zero => trivial
  | succ n ih =>
      change AmortizedCostAt potential xs (cost xs, increment xs) ≤ 2 ∧
        AllLe (AmortizedCostList potential (increment xs) (runPrefix (increment xs) n)) 2
      exact ⟨by
          have he := amortized_exact xs
          simp only [AmortizedCostAt]
          omega,
        ih (increment xs)⟩

theorem n_increments_from_zero (n : Nat) :
    ActualCostSum (runPrefix [] n) ≤ 2 * (n : Int) := by
  have h := uniform_actual_cost_bound potential potential_nonnegative [] (runPrefix [] n)
    2 (prefix_actual [] n) (prefix_h1 [] n)
  rw [prefix_length] at h
  have hs (k : Nat) : ScaleCost k 2 = 2 * (k : Int) := by
    induction k with
    | zero => simp [ScaleCost]
    | succ n ih =>
        change ScaleCost n 2 + 2 = 2 * (↑n + 1)
        rw [ih]
        omega
  simpa [potential, hs n] using h

#print axioms changed_self
#print axioms cost_is_bit_changes
#print axioms potential_nonnegative
#print axioms cost_nonnegative
#print axioms amortized_exact
#print axioms prefix_length
#print axioms prefix_actual
#print axioms prefix_h1
#print axioms n_increments_from_zero
end SixBirdsFoundationsVI.Instances.BinaryCounter
