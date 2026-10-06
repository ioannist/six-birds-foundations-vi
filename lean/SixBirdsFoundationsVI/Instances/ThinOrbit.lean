import SixBirdsFoundationsVI.Laws.G13ThinOrbitSaturation

namespace SixBirdsFoundationsVI.Instances.ThinOrbit

open SixBirdsFoundationsVI.Laws.G13ThinOrbitSaturation

/-- A finite list enumerates exactly the actual members of a family up to `N`.
No duplicates ensures its length is the actual cardinality. -/
structure CountedFamily where
  family : Nat → Prop
  members : Nat → List Nat
  member_iff : ∀ N m, m ∈ members N ↔ m ≤ N ∧ family m
  nodup : ∀ N, (members N).Nodup

def CountedFamily.count (F : CountedFamily) (N : Nat) : Nat := (F.members N).length

/-- A sublinear count of actual missed admissible values can still be infinite;
any such value refutes full local-global coverage. -/
theorem counted_exceptions (F : CountedFamily) (admissible represented : Nat → Prop)
    (hinf : InfiniteFamily F.family)
    (hmiss : ∀ m, F.family m → admissible m ∧ ¬ represented m)
    (hsub : EventuallySublinear F.count) :
    InfiniteFamily (fun m => admissible m ∧ ¬ represented m) ∧
    EventuallySublinear F.count ∧
    ¬ (∀ m, admissible m → represented m) := by
  constructor
  · intro N
    obtain ⟨M, hMN, hM⟩ := hinf N
    exact ⟨M, hMN, hmiss M hM⟩
  constructor
  · exact hsub
  · intro hfull
    obtain ⟨M, _, hM⟩ := hinf 0
    exact (hmiss M hM).2 (hfull M (hmiss M hM).1)

private theorem two_pow_ge_succ (k : Nat) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
      rw [Nat.pow_succ]
      omega

private theorem exp_base (j : Nat) : (2*j+1)*j ≤ 2^(2*j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      cases j with
      | zero => decide
      | succ j =>
          have hj : 1 ≤ j+1 := by omega
          have hsquare : j+1 ≤ (j+1)*(j+1) := by
            simpa using Nat.mul_le_mul_right (j+1) hj
          have hp : 2^(2*(j+1+1)) = 4 * 2^(2*(j+1)) := by
            rw [show 2*(j+1+1) = 2*(j+1)+2 by omega, Nat.pow_add]
            omega
          rw [hp]
          simp only [Nat.add_mul, Nat.mul_add] at *
          omega

private theorem exp_scale (j k : Nat) (h : 2*j ≤ k) : j*(k+1) ≤ 2^k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using exp_base j
  | succ d ih =>
      have hp : 2^(2*j+(d+1)) = 2 * 2^(2*j+d) := by
        rw [show 2*j+(d+1) = (2*j+d)+1 by omega, Nat.pow_succ]
        omega
      rw [hp]
      simp only [Nat.mul_add] at *
      omega

private theorem pow_injective {a b : Nat} (h : 2^a = 2^b) : a = b := by
  by_cases hab : a < b
  · have := Nat.pow_lt_pow_right (by decide : 1 < 2) hab
    omega
  · by_cases hba : b < a
    · have := Nat.pow_lt_pow_right (by decide : 1 < 2) hba
      omega
    · omega

/-- One actual value `2^k` for each qualifying exponent. -/
def powerMembers (N : Nat) : List Nat :=
  ((List.range (N+1)).filter (fun k => decide (2^k ≤ N))).map (fun k => 2^k)

theorem power_members_iff (N m : Nat) :
    m ∈ powerMembers N ↔ m ≤ N ∧ Nat.isPowerOfTwo m := by
  constructor
  · intro h
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
    have hbound : 2^k ≤ N := of_decide_eq_true (List.mem_filter.mp hk).2
    exact ⟨hbound, ⟨k, rfl⟩⟩
  · rintro ⟨hm, ⟨k, rfl⟩⟩
    have hN : N ≠ 0 := by
      have hp : 0 < 2^k := Nat.pow_pos (by decide)
      omega
    have hklog : k ≤ N.log2 := (Nat.le_log2 hN).2 hm
    have hkN : k ≤ N := Nat.le_trans hklog (Nat.log2_le_self N)
    apply List.mem_map.mpr
    refine ⟨k, List.mem_filter.mpr ?_, rfl⟩
    exact ⟨List.mem_range.mpr (by omega), decide_eq_true hm⟩

theorem power_members_nodup (N : Nat) : (powerMembers N).Nodup := by
  unfold powerMembers
  have hfilter : ((List.range (N+1)).filter (fun k => decide (2^k ≤ N))).Nodup :=
    List.Pairwise.filter _ List.nodup_range
  exact List.Pairwise.map (fun k : Nat => 2^k)
    (by intro a b hab heq; exact hab (pow_injective heq)) hfilter

def powers : CountedFamily where
  family := Nat.isPowerOfTwo
  members := powerMembers
  member_iff := power_members_iff
  nodup := power_members_nodup

private theorem countP_range_le (p : Nat → Bool) (M N : Nat)
    (hfalse : ∀ k, M ≤ k → p k = false) :
    List.countP p (List.range N) ≤ M := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [List.range_succ, List.countP_append]
      simp only [List.countP_singleton]
      by_cases h : N < M
      · have hlen : List.countP p (List.range N) ≤ N := by
          simpa using List.countP_le_length (p := p) (l := List.range N)
        cases hp : p N <;> simp [hp] at * <;> omega
      · have hp := hfalse N (by omega)
        simp [hp]
        exact ih

private theorem power_count_bound (N : Nat) : powers.count N ≤ N.log2 + 1 := by
  by_cases hN : N = 0
  · subst N; decide
  · have hfalse : ∀ k, N.log2 + 1 ≤ k → decide (2^k ≤ N) = false := by
      intro k hk
      apply decide_eq_false
      intro hpow
      have hlog := (Nat.le_log2 hN).2 hpow
      omega
    have hbound := countP_range_le (fun k => decide (2^k ≤ N)) (N.log2+1) (N+1) hfalse
    simpa [CountedFamily.count, powers, powerMembers, List.countP_eq_length_filter] using hbound

theorem power_count_sublinear : EventuallySublinear powers.count := by
  intro j hj
  refine ⟨2^(2*j), ?_⟩
  intro N hN
  have hNpos : 0 < N := Nat.lt_of_lt_of_le (Nat.pow_pos (by decide)) hN
  have hlog : 2*j ≤ N.log2 :=
    (Nat.le_log2 (by omega)).2 hN
  have hscale := exp_scale j N.log2 hlog
  have hpow : 2^N.log2 ≤ N := Nat.log2_self_le (by omega)
  have hcount := power_count_bound N
  have hmul := Nat.mul_le_mul_left j hcount
  calc
    powers.count N * j = j * powers.count N := Nat.mul_comm _ _
    _ ≤ j * (N.log2 + 1) := hmul
    _ ≤ 2^N.log2 := hscale
    _ ≤ N := hpow

theorem powers_infinite : InfiniteFamily Nat.isPowerOfTwo := by
  intro N
  refine ⟨2^(N+1), ?_, ⟨N+1, rfl⟩⟩
  have := two_pow_ge_succ (N+1)
  omega

theorem powers_relative_zero : EventuallyRelativelyNegligible powers.count (fun N => N) := by
  apply relative_density_theorem power_count_sublinear
  exact ⟨1, 1, by decide, by decide, by intro N; simp⟩

/-- The represented arithmetic set omits precisely powers of two. Thus it has
an infinite zero-density exception family, despite covering density one. -/
theorem concrete_zero_density_failure :
    InfiniteFamily Nat.isPowerOfTwo ∧
    EventuallySublinear powers.count ∧
    ¬ (∀ m, 0 < m → ¬ Nat.isPowerOfTwo m) := by
  obtain ⟨_, hsub, hfail⟩ := counted_exceptions powers (fun m => 0 < m)
    (fun m => ¬ Nat.isPowerOfTwo m) powers_infinite
    (by intro m hm; exact ⟨Nat.pos_of_isPowerOfTwo hm, fun hn => hn hm⟩) power_count_sublinear
  exact ⟨powers_infinite, hsub, hfail⟩

#print axioms counted_exceptions
#print axioms two_pow_ge_succ
#print axioms exp_base
#print axioms exp_scale
#print axioms pow_injective
#print axioms power_members_iff
#print axioms power_members_nodup
#print axioms countP_range_le
#print axioms power_count_bound
#print axioms power_count_sublinear
#print axioms powers_infinite
#print axioms powers_relative_zero
#print axioms concrete_zero_density_failure

end SixBirdsFoundationsVI.Instances.ThinOrbit
