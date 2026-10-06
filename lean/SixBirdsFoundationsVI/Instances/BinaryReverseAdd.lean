import SixBirdsFoundationsVI.Laws.G5CarryHorizonConfinement

namespace SixBirdsFoundationsVI.Instances.BinaryReverseAdd

/-- Binary digits in most-significant-first order. -/
def Value : List Nat → Nat
  | [] => 0
  | b :: bs => b * 2 ^ bs.length + Value bs

theorem value_append (xs ys : List Nat) :
    Value (xs ++ ys) = Value xs * 2 ^ ys.length + Value ys := by
  induction xs with
  | nil => simp [Value]
  | cons b bs ih =>
      simp only [List.cons_append, Value, List.length_append, ih]
      rw [Nat.pow_add]
      simp only [Nat.add_mul, Nat.mul_assoc]
      omega

theorem value_zeros (r : Nat) : Value (List.replicate r 0) = 0 := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp only [List.replicate, Value, Nat.zero_mul, Nat.zero_add]
      exact ih

theorem value_ones (r : Nat) : Value (List.replicate r 1) + 1 = 2 ^ r := by
  induction r with
  | zero => decide
  | succ r ih =>
      simp only [List.replicate, Value, List.length_replicate]
      rw [Nat.pow_succ]
      omega

def P0 (r : Nat) : List Nat := [1,0] ++ List.replicate r 1 ++ [0,1] ++ List.replicate r 0
def P1 (r : Nat) : List Nat := [1,1] ++ List.replicate (r-2) 0 ++ [1,0,0,0] ++ List.replicate (r-2) 1 ++ [0,1]
def P2 (r : Nat) : List Nat := [1,0] ++ List.replicate r 1 ++ [0,1] ++ List.replicate (r+1) 0
def P3 (r : Nat) : List Nat := [1,1] ++ List.replicate r 0 ++ [1,0] ++ List.replicate (r-1) 1 ++ [0,1]

/-- Numeric base-2 reverse-and-add on a displayed binary word. -/
def ReverseAdd (w : List Nat) : Nat := Value w + Value w.reverse

theorem p0_value (r : Nat) :
    Value (P0 r) = ((2 * 2 ^ r + Value (List.replicate r 1)) * 4 + 1) * 2 ^ r := by
  simp [P0, value_append, value_zeros, Value, Nat.pow_add,
    Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  conv => rhs; rw [show (4 : Nat) = 2 * 2 by decide]
  ac_rfl

theorem p0_reverse_value (r : Nat) :
    Value (P0 r).reverse = (2 * 2 ^ r + Value (List.replicate r 1)) * 4 + 1 := by
  simp [P0, List.reverse_append, value_append, value_zeros, Value,
    Nat.pow_add, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm]
  omega

theorem p0_not_palindrome (r : Nat) (hr : 0 < r) : P0 r ≠ (P0 r).reverse := by
  intro h
  have hh := congrArg List.head? h
  cases r with
  | zero => omega
  | succ r =>
      simp [P0, List.reverse_append] at hh
      simp [List.replicate] at hh

theorem p2_not_palindrome (r : Nat) : P2 r ≠ (P2 r).reverse := by
  intro h
  have hh := congrArg List.head? h
  simp [P2, List.reverse_append] at hh
  simp [List.replicate] at hh

theorem p0_value_closed (r : Nat) :
    Value (P0 r) + 3 * 2 ^ r = 12 * (2 ^ r * 2 ^ r) := by
  rw [p0_value]
  have h := value_ones r
  have hm := congrArg (fun n : Nat => n * 2 ^ r) h
  simp only [Nat.add_mul, Nat.one_mul] at hm
  have hpoly :
      ((2 * 2 ^ r + Value (List.replicate r 1)) * 4 + 1) * 2 ^ r + 3 * 2 ^ r =
        8 * (2 ^ r * 2 ^ r) + 4 * (Value (List.replicate r 1) * 2 ^ r) + 4 * 2 ^ r := by
    have h1 : (2 * 2 ^ r * 4) * 2 ^ r = 8 * (2 ^ r * 2 ^ r) := by
      conv => rhs; rw [show (8 : Nat) = 2 * 4 by decide]
      ac_rfl
    have h2 : (Value (List.replicate r 1) * 4) * 2 ^ r =
        4 * (Value (List.replicate r 1) * 2 ^ r) := by ac_rfl
    simp only [Nat.add_mul, h1, h2, Nat.one_mul]
    omega
  rw [hpoly]
  omega

theorem p0_reverse_value_closed (r : Nat) :
    Value (P0 r).reverse + 3 = 12 * 2 ^ r := by
  rw [p0_reverse_value]
  have h := value_ones r
  omega

theorem p2_value_closed (r : Nat) :
    Value (P2 r) + 6 * 2 ^ r = 24 * (2 ^ r * 2 ^ r) := by
  have hp : P2 r = P0 r ++ [0] := by
    simp [P0, P2, List.replicate_succ', List.append_assoc]
  rw [hp, value_append]
  simp only [List.length_singleton, Nat.pow_one]
  simp only [Value, Nat.zero_mul, Nat.add_zero]
  have h := p0_value_closed r
  omega

theorem p2_reverse_value_closed (r : Nat) :
    Value (P2 r).reverse + 3 = 12 * 2 ^ r := by
  have hp : P2 r = P0 r ++ [0] := by
    simp [P0, P2, List.replicate_succ', List.append_assoc]
  rw [hp, List.reverse_append]
  simpa [Value] using p0_reverse_value_closed r

theorem p1_value_closed (s : Nat) :
    Value (P1 (s + 2)) + 3 = 192 * (2 ^ s * 2 ^ s) + 36 * 2 ^ s := by
  simp [P1, value_append, value_zeros, Value, Nat.pow_add]
  have hpow : 2 ^ s * (2 ^ s * 4 * 2 * 2 * 2 * 2) =
      64 * (2 ^ s * 2 ^ s) := by
    conv => rhs; rw [show (64 : Nat) = 4 * 2 * 2 * 2 * 2 by decide]
    ac_rfl
  have hlin : 2 ^ s * 4 * 2 * 2 * 2 = 32 * 2 ^ s := by
    conv => rhs; rw [show (32 : Nat) = 4 * 2 * 2 * 2 by decide]
    ac_rfl
  rw [hpow, hlin]
  have h := value_ones s
  omega

theorem p1_reverse_value_closed (s : Nat) :
    Value (P1 (s + 2)).reverse + 60 * 2 ^ s =
      192 * (2 ^ s * 2 ^ s) + 3 := by
  simp [P1, List.reverse_append, value_append, value_zeros, Value, Nat.pow_add]
  have hpow : 2 ^ s * (2 ^ s * 4 * 2 * 2 * 2 * 2) =
      64 * (2 ^ s * 2 ^ s) := by
    conv => rhs; rw [show (64 : Nat) = 4 * 2 * 2 * 2 * 2 by decide]
    ac_rfl
  have hprod : Value (List.replicate s 1) * (2 ^ s * 4 * 2 * 2 * 2 * 2) =
      64 * (Value (List.replicate s 1) * 2 ^ s) := by
    conv => rhs; rw [show (64 : Nat) = 4 * 2 * 2 * 2 * 2 by decide]
    ac_rfl
  rw [hpow, hprod]
  have h := value_ones s
  have hm := congrArg (fun n : Nat => n * 2 ^ s) h
  simp only [Nat.add_mul, Nat.one_mul] at hm
  omega

theorem p3_value_closed (s : Nat) :
    Value (P3 (s + 2)) + 3 = 384 * (2 ^ s * 2 ^ s) + 24 * 2 ^ s := by
  simp [P3, value_append, value_zeros, Value, Nat.pow_add]
  have hpow : 2 ^ s * 4 * (2 ^ s * 2 * 4 * 2 * 2) =
      128 * (2 ^ s * 2 ^ s) := by
    conv => rhs; rw [show (128 : Nat) = 4 * 2 * 4 * 2 * 2 by decide]
    ac_rfl
  have hlin : 2 ^ s * 2 * 4 * 2 = 16 * 2 ^ s := by
    conv => rhs; rw [show (16 : Nat) = 2 * 4 * 2 by decide]
    ac_rfl
  rw [hpow, hlin]
  have h := value_ones (s + 1)
  rw [Nat.pow_succ] at h
  omega

theorem p3_reverse_value_closed (s : Nat) :
    Value (P3 (s + 2)).reverse + 48 * 2 ^ s =
      384 * (2 ^ s * 2 ^ s) + 3 := by
  simp [P3, List.reverse_append, value_append, value_zeros, Value, Nat.pow_add]
  have hpow : 2 ^ s * 2 * (2 ^ s * 4 * 4 * 2 * 2) =
      128 * (2 ^ s * 2 ^ s) := by
    conv => rhs; rw [show (128 : Nat) = 2 * 4 * 4 * 2 * 2 by decide]
    ac_rfl
  have hprod : Value (List.replicate (s + 1) 1) * (2 ^ s * 4 * 4 * 2 * 2) =
      64 * (Value (List.replicate (s + 1) 1) * 2 ^ s) := by
    conv => rhs; rw [show (64 : Nat) = 4 * 4 * 2 * 2 by decide]
    ac_rfl
  rw [hpow, hprod]
  have h := value_ones (s + 1)
  rw [Nat.pow_succ] at h
  have hm := congrArg (fun n : Nat => n * 2 ^ s) h
  simp only [Nat.add_mul, Nat.one_mul] at hm
  have htwice : (2 ^ s * 2) * 2 ^ s = 2 * (2 ^ s * 2 ^ s) := by ac_rfl
  rw [htwice] at hm
  omega

private theorem pow_two_shift (s : Nat) : 2 ^ (s + 2) = 4 * 2 ^ s := by
  rw [Nat.pow_add]
  simp
  omega

private theorem square_four (x : Nat) : (4 * x) * (4 * x) = 16 * (x * x) := by
  conv => rhs; rw [show (16 : Nat) = 4 * 4 by decide]
  ac_rfl

private theorem p0_value_at (s : Nat) :
    Value (P0 (s + 2)) + 12 * 2 ^ s = 192 * (2 ^ s * 2 ^ s) := by
  have h := p0_value_closed (s + 2)
  rw [pow_two_shift, square_four] at h
  omega

private theorem p0_reverse_at (s : Nat) :
    Value (P0 (s + 2)).reverse + 3 = 48 * 2 ^ s := by
  have h := p0_reverse_value_closed (s + 2)
  rw [pow_two_shift] at h
  omega

private theorem p2_value_at (s : Nat) :
    Value (P2 (s + 2)) + 24 * 2 ^ s = 384 * (2 ^ s * 2 ^ s) := by
  have h := p2_value_closed (s + 2)
  rw [pow_two_shift, square_four] at h
  omega

private theorem p2_reverse_at (s : Nat) :
    Value (P2 (s + 2)).reverse + 3 = 48 * 2 ^ s := by
  have h := p2_reverse_value_closed (s + 2)
  rw [pow_two_shift] at h
  omega

theorem transition_01 (s : Nat) :
    ReverseAdd (P0 (s + 2)) = Value (P1 (s + 2)) := by
  have h0 := p0_value_at s
  have h0r := p0_reverse_at s
  have h1 := p1_value_closed s
  unfold ReverseAdd
  omega

theorem transition_12 (s : Nat) :
    ReverseAdd (P1 (s + 2)) = Value (P2 (s + 2)) := by
  have h1 := p1_value_closed s
  have h1r := p1_reverse_value_closed s
  have h2 := p2_value_at s
  unfold ReverseAdd
  omega

theorem transition_23 (s : Nat) :
    ReverseAdd (P2 (s + 2)) = Value (P3 (s + 2)) := by
  have h2 := p2_value_at s
  have h2r := p2_reverse_at s
  have h3 := p3_value_closed s
  unfold ReverseAdd
  omega

theorem transition_30 (s : Nat) :
    ReverseAdd (P3 (s + 2)) = Value (P0 (s + 3)) := by
  have h3 := p3_value_closed s
  have h3r := p3_reverse_value_closed s
  have h0 := p0_value_at (s + 1)
  rw [Nat.pow_succ] at h0
  have hsquare : (2 ^ s * 2) * (2 ^ s * 2) = 4 * (2 ^ s * 2 ^ s) := by
    conv => rhs; rw [show (4 : Nat) = 2 * 2 by decide]
    ac_rfl
  rw [hsquare] at h0
  have hindex : s + 1 + 2 = s + 3 := by omega
  rw [hindex] at h0
  unfold ReverseAdd
  omega

theorem p1_not_palindrome (r : Nat) : P1 r ≠ (P1 r).reverse := by
  intro h
  have hh := congrArg (fun w : List Nat => w.tail.head?) h
  simp [P1, List.reverse_append] at hh

theorem p3_not_palindrome (r : Nat) : P3 r ≠ (P3 r).reverse := by
  intro h
  have hh := congrArg (fun w : List Nat => w.tail.head?) h
  simp [P3, List.reverse_append] at hh

theorem pre_entry_values :
    Value [1,0,1,1,0] = 22 ∧
    ReverseAdd [1,0,1,1,0] = Value [1,0,0,0,1,1] ∧
    ReverseAdd [1,0,0,0,1,1] = Value [1,0,1,0,1,0,0] ∧
    ReverseAdd [1,0,1,0,1,0,0] = Value [1,1,0,1,0,0,1] ∧
    ReverseAdd [1,1,0,1,0,0,1] = Value (P0 2) := by
  decide

theorem pre_entry_not_palindromes :
    [1,0,1,1,0] ≠ ([1,0,1,1,0] : List Nat).reverse ∧
    [1,0,0,0,1,1] ≠ ([1,0,0,0,1,1] : List Nat).reverse ∧
    [1,0,1,0,1,0,0] ≠ ([1,0,1,0,1,0,0] : List Nat).reverse ∧
    [1,1,0,1,0,0,1] ≠ ([1,1,0,1,0,0,1] : List Nat).reverse := by
  decide

def Bits (w : List Nat) : Prop := ∀ b ∈ w, b ≤ 1

def Canonical (w : List Nat) : Prop :=
  (∃ t, w = 1 :: t) ∧ Bits w

theorem value_lt_pow_length (w : List Nat) (hw : Bits w) :
    Value w < 2 ^ w.length := by
  induction w with
  | nil => simp [Value]
  | cons b bs ih =>
      have hb : b ≤ 1 := hw b (by simp)
      have hbs : Bits bs := by
        intro x hx
        exact hw x (by simp [hx])
      have ht := ih hbs
      have hbcase : b = 0 ∨ b = 1 := by omega
      rcases hbcase with hb0 | hb1
      · subst b
        simp only [Value, Nat.zero_mul, Nat.zero_add, List.length_cons, Nat.pow_succ]
        omega
      · subst b
        simp only [Value, Nat.one_mul, List.length_cons, Nat.pow_succ]
        omega

theorem value_injective_same_length (xs ys : List Nat)
    (hx : Bits xs) (hy : Bits ys) (hlen : xs.length = ys.length)
    (hv : Value xs = Value ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons _ _ => simp at hlen
  | cons b bs ih =>
      cases ys with
      | nil => simp at hlen
      | cons c cs =>
          have hbt : Bits bs := by
            intro x h; exact hx x (by simp [h])
          have hct : Bits cs := by
            intro x h; exact hy x (by simp [h])
          have hbl := value_lt_pow_length bs hbt
          have hcl := value_lt_pow_length cs hct
          have hl : bs.length = cs.length := by simpa using hlen
          have hpow : 2 ^ bs.length = 2 ^ cs.length := congrArg (2 ^ ·) hl
          have hb : b = 0 ∨ b = 1 := by
            have h := hx b (by simp)
            omega
          have hc : c = 0 ∨ c = 1 := by
            have h := hy c (by simp)
            omega
          rcases hb with hb0 | hb1 <;> rcases hc with hc0 | hc1
          · subst b; subst c
            have hv' : Value bs = Value cs := by simpa [Value] using hv
            simp [ih cs hbt hct hl hv']
          · subst b; subst c
            simp [Value] at hv
            omega
          · subst b; subst c
            simp [Value] at hv
            omega
          · subst b; subst c
            have hv' : Value bs = Value cs := by
              simp only [Value, Nat.one_mul] at hv
              rw [hpow] at hv
              omega
            simp [ih cs hbt hct hl hv']

theorem canonical_unique (xs ys : List Nat)
    (hx : Canonical xs) (hy : Canonical ys)
    (hv : Value xs = Value ys) : xs = ys := by
  rcases hx with ⟨⟨tx, rfl⟩, hxb⟩
  rcases hy with ⟨⟨ty, rfl⟩, hyb⟩
  have htx : Bits tx := by
    intro b hb; exact hxb b (by simp [hb])
  have hty : Bits ty := by
    intro b hb; exact hyb b (by simp [hb])
  have hbx := value_lt_pow_length tx htx
  have hby := value_lt_pow_length ty hty
  have hlen : tx.length = ty.length := by
    by_cases hne : tx.length = ty.length
    · exact hne
    have hlt : tx.length < ty.length ∨ ty.length < tx.length := by omega
    rcases hlt with hlt | hlt
    · have hp := Nat.pow_le_pow_of_le (a := 2) (by decide : 1 < 2) (show tx.length + 1 ≤ ty.length by omega)
      simp only [Value] at hv
      rw [Nat.pow_succ] at hp
      omega
    · have hp := Nat.pow_le_pow_of_le (a := 2) (by decide : 1 < 2) (show ty.length + 1 ≤ tx.length by omega)
      simp only [Value] at hv
      rw [Nat.pow_succ] at hp
      omega
  exact value_injective_same_length (1 :: tx) (1 :: ty) hxb hyb (by simp [hlen]) hv

theorem p0_canonical (r : Nat) : Canonical (P0 r) := by
  constructor
  · refine ⟨[0] ++ List.replicate r 1 ++ [0,1] ++ List.replicate r 0, ?_⟩
    simp [P0]
  · intro b hb
    simp [P0] at hb
    omega

theorem p1_canonical (r : Nat) : Canonical (P1 r) := by
  constructor
  · refine ⟨[1] ++ List.replicate (r-2) 0 ++ [1,0,0,0] ++ List.replicate (r-2) 1 ++ [0,1], ?_⟩
    simp [P1]
  · intro b hb
    simp [P1] at hb
    omega

theorem p2_canonical (r : Nat) : Canonical (P2 r) := by
  constructor
  · refine ⟨[0] ++ List.replicate r 1 ++ [0,1] ++ List.replicate (r+1) 0, ?_⟩
    simp [P2]
  · intro b hb
    simp [P2] at hb
    omega

theorem p3_canonical (r : Nat) : Canonical (P3 r) := by
  constructor
  · refine ⟨[1] ++ List.replicate r 0 ++ [1,0] ++ List.replicate (r-1) 1 ++ [0,1], ?_⟩
    simp [P3]
  · intro b hb
    simp [P3] at hb
    omega

/-- Reverse-and-add on a natural number, using its unique leading-1 binary word. -/
noncomputable def NumericStep (n : Nat) : Nat :=
  by
    classical
    exact if h : ∃ w, Canonical w ∧ Value w = n then
      ReverseAdd (Classical.choose h)
    else n

theorem numeric_step_on (w : List Nat) (hw : Canonical w) :
    NumericStep (Value w) = ReverseAdd w := by
  let h : ∃ v, Canonical v ∧ Value v = Value w := ⟨w, hw, rfl⟩
  unfold NumericStep
  rw [dif_pos h]
  have hs := Classical.choose_spec h
  have heq := canonical_unique (Classical.choose h) w hs.1 hw hs.2
  rw [heq]

/-- The canonical binary word for the reverse-and-add value of a displayed word. -/
noncomputable def WordStep (w : List Nat) : List Nat := by
  classical
  exact if h : ∃ v, Canonical v ∧ Value v = ReverseAdd w then
    Classical.choose h
  else []

theorem word_step_on (w v : List Nat) (hv : Canonical v)
    (hvalue : ReverseAdd w = Value v) : WordStep w = v := by
  let h : ∃ u, Canonical u ∧ Value u = ReverseAdd w := ⟨v, hv, hvalue.symm⟩
  unfold WordStep
  rw [dif_pos h]
  have hs := Classical.choose_spec h
  exact canonical_unique (Classical.choose h) v hs.1 hv (hs.2.trans hvalue)

theorem word_transition_01 (s : Nat) :
    WordStep (P0 (s + 2)) = P1 (s + 2) :=
  word_step_on _ _ (p1_canonical _) (transition_01 s)

theorem word_transition_12 (s : Nat) :
    WordStep (P1 (s + 2)) = P2 (s + 2) :=
  word_step_on _ _ (p2_canonical _) (transition_12 s)

theorem word_transition_23 (s : Nat) :
    WordStep (P2 (s + 2)) = P3 (s + 2) :=
  word_step_on _ _ (p3_canonical _) (transition_23 s)

theorem word_transition_30 (s : Nat) :
    WordStep (P3 (s + 2)) = P0 (s + 3) :=
  word_step_on _ _ (p0_canonical _) (transition_30 s)

#print axioms word_step_on
#print axioms word_transition_01
#print axioms word_transition_12
#print axioms word_transition_23
#print axioms word_transition_30

def IsPalindrome (n : Nat) : Prop :=
  ∃ w, Canonical w ∧ Value w = n ∧ w = w.reverse

theorem not_palindrome_on (w : List Nat) (hw : Canonical w)
    (hn : w ≠ w.reverse) : ¬ IsPalindrome (Value w) := by
  intro ⟨v, hv, heq, hpal⟩
  have hsame := canonical_unique v w hv hw heq
  subst v
  exact hn hpal

def Family (n : Nat) : Prop :=
  ∃ s : Nat,
    n = Value (P0 (s + 2)) ∨ n = Value (P1 (s + 2)) ∨
    n = Value (P2 (s + 2)) ∨ n = Value (P3 (s + 2))

theorem family_closed :
    SixBirdsFoundationsVI.Laws.G5CarryHorizonConfinement.ClosedUnderR
      NumericStep Family := by
  intro n ⟨s, h⟩
  rcases h with h | h | h | h
  · refine ⟨s, Or.inr (Or.inl ?_)⟩
    rw [h, numeric_step_on _ (p0_canonical _), transition_01]
  · refine ⟨s, Or.inr (Or.inr (Or.inl ?_))⟩
    rw [h, numeric_step_on _ (p1_canonical _), transition_12]
  · refine ⟨s, Or.inr (Or.inr (Or.inr ?_))⟩
    rw [h, numeric_step_on _ (p2_canonical _), transition_23]
  · refine ⟨s + 1, Or.inl ?_⟩
    rw [h, numeric_step_on _ (p3_canonical _), transition_30]

theorem family_target_free :
    SixBirdsFoundationsVI.Laws.G5CarryHorizonConfinement.TargetFree
      IsPalindrome Family := by
  intro n ⟨s, h⟩
  rcases h with h | h | h | h
  · rw [h]
    exact not_palindrome_on _ (p0_canonical _) (p0_not_palindrome _ (by omega))
  · rw [h]
    exact not_palindrome_on _ (p1_canonical _) (p1_not_palindrome _)
  · rw [h]
    exact not_palindrome_on _ (p2_canonical _) (p2_not_palindrome _)
  · rw [h]
    exact not_palindrome_on _ (p3_canonical _) (p3_not_palindrome _)

private theorem c0 : Canonical [1,0,1,1,0] := by
  constructor
  · exact ⟨[0,1,1,0], rfl⟩
  · simp [Bits]

private theorem c1 : Canonical [1,0,0,0,1,1] := by
  constructor
  · exact ⟨[0,0,0,1,1], rfl⟩
  · simp [Bits]

private theorem c2 : Canonical [1,0,1,0,1,0,0] := by
  constructor
  · exact ⟨[0,1,0,1,0,0], rfl⟩
  · simp [Bits]

private theorem c3 : Canonical [1,1,0,1,0,0,1] := by
  constructor
  · exact ⟨[1,0,1,0,0,1], rfl⟩
  · simp [Bits]

theorem pre_entry_word_transitions :
    WordStep [1,0,1,1,0] = [1,0,0,0,1,1] ∧
    WordStep [1,0,0,0,1,1] = [1,0,1,0,1,0,0] ∧
    WordStep [1,0,1,0,1,0,0] = [1,1,0,1,0,0,1] ∧
    WordStep [1,1,0,1,0,0,1] = P0 2 := by
  rcases pre_entry_values with ⟨_, h01, h12, h23, h30⟩
  exact ⟨word_step_on _ _ c1 h01,
    word_step_on _ _ c2 h12,
    word_step_on _ _ c3 h23,
    word_step_on _ _ (p0_canonical 2) h30⟩

#print axioms pre_entry_word_transitions

theorem pre_entry_orbit :
    SixBirdsFoundationsVI.Laws.G5CarryHorizonConfinement.Iterate NumericStep 1 22 =
      Value [1,0,0,0,1,1] ∧
    SixBirdsFoundationsVI.Laws.G5CarryHorizonConfinement.Iterate NumericStep 2 22 =
      Value [1,0,1,0,1,0,0] ∧
    SixBirdsFoundationsVI.Laws.G5CarryHorizonConfinement.Iterate NumericStep 3 22 =
      Value [1,1,0,1,0,0,1] ∧
    SixBirdsFoundationsVI.Laws.G5CarryHorizonConfinement.Iterate NumericStep 4 22 =
      Value (P0 2) := by
  rcases pre_entry_values with ⟨hval, h01, h12, h23, h30⟩
  have hs0 : NumericStep 22 = Value [1,0,0,0,1,1] := by
    rw [← hval, numeric_step_on _ c0, h01]
  have hs1 : NumericStep (Value [1,0,0,0,1,1]) = Value [1,0,1,0,1,0,0] := by
    rw [numeric_step_on _ c1, h12]
  have hs2 : NumericStep (Value [1,0,1,0,1,0,0]) = Value [1,1,0,1,0,0,1] := by
    rw [numeric_step_on _ c2, h23]
  have hs3 : NumericStep (Value [1,1,0,1,0,0,1]) = Value (P0 2) := by
    rw [numeric_step_on _ c3, h30]
  constructor
  · simpa [SixBirdsFoundationsVI.Laws.G5CarryHorizonConfinement.Iterate] using hs0
  constructor
  · simpa [SixBirdsFoundationsVI.Laws.G5CarryHorizonConfinement.Iterate, hs0] using hs1
  constructor
  · simpa [SixBirdsFoundationsVI.Laws.G5CarryHorizonConfinement.Iterate, hs0, hs1] using hs2
  · simpa [SixBirdsFoundationsVI.Laws.G5CarryHorizonConfinement.Iterate, hs0, hs1, hs2] using hs3

theorem confined_after_entry (t : Nat) :
    Family (SixBirdsFoundationsVI.Laws.G5CarryHorizonConfinement.Iterate NumericStep (4 + t) 22) ∧
    ¬ IsPalindrome (SixBirdsFoundationsVI.Laws.G5CarryHorizonConfinement.Iterate NumericStep (4 + t) 22) := by
  apply SixBirdsFoundationsVI.Laws.G5CarryHorizonConfinement.closed_pattern_confinement
    NumericStep IsPalindrome Family ⟨family_closed, family_target_free⟩ 22 4
  rw [pre_entry_orbit.2.2.2]
  exact ⟨0, Or.inl rfl⟩

theorem orbit_22_never_palindrome (t : Nat) :
    ¬ IsPalindrome (SixBirdsFoundationsVI.Laws.G5CarryHorizonConfinement.Iterate NumericStep t 22) := by
  by_cases ht : t < 4
  · rcases pre_entry_orbit with ⟨h1, h2, h3, _⟩
    rcases pre_entry_not_palindromes with ⟨hn0, hn1, hn2, hn3⟩
    have hcases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
    rcases hcases with h | h | h | h
    · subst t
      have hv : Value [1,0,1,1,0] = 22 := pre_entry_values.1
      simpa [SixBirdsFoundationsVI.Laws.G5CarryHorizonConfinement.Iterate, hv] using
        not_palindrome_on [1,0,1,1,0] c0 hn0
    · subst t
      rw [h1]
      exact not_palindrome_on _ c1 hn1
    · subst t
      rw [h2]
      exact not_palindrome_on _ c2 hn2
    · subst t
      rw [h3]
      exact not_palindrome_on _ c3 hn3
  · have heq : 4 + (t - 4) = t := by omega
    rw [← heq]
    exact (confined_after_entry (t - 4)).2

#print axioms confined_after_entry
#print axioms orbit_22_never_palindrome

#print axioms pre_entry_orbit
#print axioms c0
#print axioms c1
#print axioms c2
#print axioms c3

#print axioms numeric_step_on
#print axioms not_palindrome_on
#print axioms family_closed
#print axioms family_target_free

#print axioms p0_canonical
#print axioms p1_canonical
#print axioms p2_canonical
#print axioms p3_canonical

#print axioms value_lt_pow_length
#print axioms value_injective_same_length
#print axioms canonical_unique

#print axioms pre_entry_values
#print axioms pre_entry_not_palindromes

#print axioms p1_not_palindrome
#print axioms p3_not_palindrome

#print axioms transition_01
#print axioms transition_12
#print axioms transition_23
#print axioms transition_30
#print axioms pow_two_shift
#print axioms square_four
#print axioms p0_value_at
#print axioms p0_reverse_at
#print axioms p2_value_at
#print axioms p2_reverse_at

#print axioms p0_value_closed
#print axioms p0_reverse_value_closed
#print axioms p2_value_closed
#print axioms p2_reverse_value_closed
#print axioms p1_value_closed
#print axioms p1_reverse_value_closed
#print axioms p3_value_closed
#print axioms p3_reverse_value_closed

#print axioms value_append
#print axioms value_zeros
#print axioms value_ones
#print axioms p0_value
#print axioms p0_reverse_value
#print axioms p0_not_palindrome
#print axioms p2_not_palindrome

end SixBirdsFoundationsVI.Instances.BinaryReverseAdd
