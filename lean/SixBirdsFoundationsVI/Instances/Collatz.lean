namespace SixBirdsFoundationsVI.Instances.Collatz

/-- Repeatedly remove factors of two, recording the exponent and odd part. -/
def stripTwos (n : Nat) : Nat × Nat :=
  if h : 0 < n ∧ n % 2 = 0 then
    let p := stripTwos (n / 2)
    (p.1 + 1, p.2)
  else (0, n)
termination_by n
decreasing_by
  exact Nat.div_lt_self (by omega) (by decide)

theorem stripTwos_eq (n : Nat) :
    2 ^ (stripTwos n).1 * (stripTwos n).2 = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases h : 0 < n ∧ n % 2 = 0
      · have hlt : n / 2 < n := Nat.div_lt_self h.1 (by decide)
        have hs := ih (n / 2) hlt
        rw [stripTwos]
        simp only [dif_pos h]
        rw [Nat.pow_succ]
        calc
          2 ^ (stripTwos (n / 2)).1 * 2 * (stripTwos (n / 2)).2
              = 2 * (2 ^ (stripTwos (n / 2)).1 * (stripTwos (n / 2)).2) := by ac_rfl
          _ = 2 * (n / 2) := by rw [hs]
          _ = n := by
            have hd : n / 2 * 2 = n := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h.2)
            omega
      · rw [stripTwos]
        simp [h]

def exponent (n : Nat) : Nat := (stripTwos (3 * n + 1)).1
def accelerated (n : Nat) : Nat := (stripTwos (3 * n + 1)).2

theorem accelerated_step (n : Nat) :
    2 ^ exponent n * accelerated n = 3 * n + 1 := stripTwos_eq _

theorem stripTwos_pow_odd (m q : Nat) (hq : q % 2 = 1) :
    stripTwos (2 ^ m * q) = (m, q) := by
  induction m with
  | zero =>
      simp only [Nat.pow_zero, Nat.one_mul]
      rw [stripTwos]
      simp [hq]
  | succ m ih =>
      have hpos : 0 < 2 ^ m * q :=
        Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
      have hp : 2 ^ (m + 1) * q = 2 * (2 ^ m * q) := by
        rw [Nat.pow_succ]
        ac_rfl
      rw [hp, stripTwos]
      have h : 0 < 2 * (2 ^ m * q) ∧ (2 * (2 ^ m * q)) % 2 = 0 := by
        constructor
        · omega
        · simp
      simp only [dif_pos h]
      have hd : 2 * (2 ^ m * q) / 2 = 2 ^ m * q := by omega
      rw [hd, ih]

def orbit (n : Nat) : Nat → Nat
  | 0 => n
  | k + 1 => accelerated (orbit n k)

def orbitExponent (n : Nat) (k : Nat) : Nat := exponent (orbit n k)

/-- The cumulative accelerated Collatz division exponent. -/
def A (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => A a k + a k

/-- The affine numerator's constant term. -/
def B (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => 3 * B a k + 2 ^ A a k

/-- Every accelerated trajectory with its actual division exponents has the paper's affine ledger. -/
theorem affine_ledger (n a : Nat → Nat)
    (hstep : ∀ j, 2 ^ a j * n (j + 1) = 3 * n j + 1) :
    ∀ k, 2 ^ A a k * n k = 3 ^ k * n 0 + B a k := by
  intro k
  induction k with
  | zero => simp [A, B]
  | succ k ih =>
      rw [A, B, Nat.pow_add]
      have h := hstep k
      calc
        2 ^ A a k * 2 ^ a k * n (k + 1)
            = 2 ^ A a k * (3 * n k + 1) := by rw [Nat.mul_assoc, h]
        _ = 3 * (2 ^ A a k * n k) + 2 ^ A a k := by
          simp only [Nat.mul_add, Nat.mul_one]
          ac_rfl
        _ = 3 * (3 ^ k * n 0 + B a k) + 2 ^ A a k := by rw [ih]
        _ = 3 ^ (k + 1) * n 0 + (3 * B a k + 2 ^ A a k) := by
          rw [Nat.pow_succ]
          simp only [Nat.mul_add]
          ac_rfl

theorem accelerated_affine_ledger (n k : Nat) :
    2 ^ A (orbitExponent n) k * orbit n k =
      3 ^ k * n + B (orbitExponent n) k := by
  have hstep : ∀ j, 2 ^ orbitExponent n j * orbit n (j + 1) =
      3 * orbit n j + 1 := by
    intro j
    exact accelerated_step (orbit n j)
  simpa [orbit] using affine_ledger (orbit n) (orbitExponent n) hstep k

/-- The split pair uses c=2 at even depths and c=1 at odd depths. -/
def c : Nat → Nat
  | 0 => 2
  | 1 => 1
  | m + 2 => c m

def first : Nat → Nat
  | 0 => 1
  | 1 => 1
  | m + 2 => 4 * first m + 1

theorem c_one_or_two (m : Nat) : c m = 1 ∨ c m = 2 := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
      cases m with
      | zero => exact Or.inr rfl
      | succ m =>
          cases m with
          | zero => exact Or.inl rfl
          | succ m => simpa [c] using ih m (by omega)

theorem first_formula (m : Nat) : 3 * first m + 1 = 2 ^ (m + 1) * c m := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
      cases m with
      | zero => decide
      | succ m =>
          cases m with
          | zero => decide
          | succ m =>
              have h := ih m (by omega)
              simp only [first, c]
              have hp : 2 ^ (m + 2 + 1) = 4 * 2 ^ (m + 1) := by
                rw [show m + 2 + 1 = (m + 1) + 2 by omega, Nat.pow_add]
                simp
                ac_rfl
              rw [hp]
              calc
                3 * (4 * first m + 1) + 1 = 4 * (3 * first m + 1) := by omega
                _ = 4 * (2 ^ (m + 1) * c m) := by rw [h]
                _ = 4 * 2 ^ (m + 1) * c m := by ac_rfl

/-- At every positive depth the pair agrees modulo 2^m, while its next valuation differs. -/
theorem split_pair (m : Nat) (_hm : 1 ≤ m) :
    let n₁ := first m
    let n₂ := n₁ + 2 ^ m
    n₁ % 2 ^ m = n₂ % 2 ^ m ∧
    2 ^ (m + 1) ∣ 3 * n₁ + 1 ∧
    (∃ q, q % 2 = 1 ∧ 3 * n₂ + 1 = 2 ^ m * q) := by
  dsimp
  have hf := first_formula m
  have hc := c_one_or_two m
  constructor
  · simp
  constructor
  · exact ⟨c m, hf⟩
  · refine ⟨2 * c m + 3, ?_, ?_⟩
    · rcases hc with h | h <;> rw [h] <;> decide
    ·
      have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
      calc
        3 * (first m + 2 ^ m) + 1
            = (3 * first m + 1) + 3 * 2 ^ m := by omega
        _ = 2 ^ (m + 1) * c m + 3 * 2 ^ m := by rw [hf]
        _ = 2 ^ m * (2 * c m + 3) := by
          rw [hp]
          simp only [Nat.mul_add]
          ac_rfl

theorem split_pair_next_exponent (m : Nat) (hm : 1 ≤ m) :
    exponent (first m + 2 ^ m) = m := by
  rcases (split_pair m hm).2.2 with ⟨q, hodd, hnum⟩
  unfold exponent
  rw [hnum, stripTwos_pow_odd m q hodd]

theorem split_pair_prior_exponent (m : Nat) (_hm : 1 ≤ m) :
    m + 1 ≤ exponent (first m) := by
  unfold exponent
  rw [first_formula]
  rcases c_one_or_two m with h | h
  · rw [h, stripTwos_pow_odd (m + 1) 1 (by decide)]
    omega
  · rw [h]
    have hp : 2 ^ (m + 1) * 2 = 2 ^ (m + 2) * 1 := by
      rw [show m + 2 = (m + 1) + 1 by omega, Nat.pow_succ]
      omega
    rw [hp, stripTwos_pow_odd (m + 2) 1 (by decide)]
    omega

#print axioms affine_ledger
#print axioms stripTwos_eq
#print axioms accelerated_step
#print axioms stripTwos_pow_odd
#print axioms accelerated_affine_ledger
#print axioms c_one_or_two
#print axioms first_formula
#print axioms split_pair
#print axioms split_pair_next_exponent
#print axioms split_pair_prior_exponent

end SixBirdsFoundationsVI.Instances.Collatz
