import SixBirdsFoundationsVI.Instances.Rule184

namespace SixBirdsFoundationsVI.Instances.Rule184Small
open SixBirdsFoundationsVI.Instances.Rule184

private theorem site_cases_2 (v : Fin 2) : v = 0 ∨ v = 1 := by
  have hv : v.val = 0 ∨ v.val = 1 := by have hi := v.isLt; omega
  rcases hv with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

private theorem repr_2 (c : Config 2) :
    c = fun i => if i == (0 : Fin 2) then c 0 else c 1 := by
  funext i
  rcases site_cases_2 i with hi | hi <;> subst i <;> simp

private theorem early_2 (c : Config 2) (h : LowDensity c) :
    JamFree (runFrom c 0) := by
  apply (blocked_zero_iff_jam_free (runFrom c 0)).mp
  rw [repr_2 c] at h ⊢
  cases h0 : c 0 <;> cases h1 : c 1 <;>
    simp [LowDensity, cars, h0, h1] at h <;>
    decide

theorem clears_2 (c : Config 2) (h : LowDensity c) :
    JamFree (runFrom c 2) := by
  have ht := free_flow_tail (n := 2) (by omega) c 0 (early_2 c h) 2
  simpa using ht.1

#print axioms site_cases_2
#print axioms repr_2
#print axioms early_2
#print axioms clears_2

private theorem site_cases_3 (v : Fin 3) : v = 0 ∨ v = 1 ∨ v = 2 := by
  have hv : v.val = 0 ∨ v.val = 1 ∨ v.val = 2 := by have hi := v.isLt; omega
  rcases hv with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

private theorem repr_3 (c : Config 3) :
    c = fun i => if i == (0 : Fin 3) then c 0 else
      if i == (1 : Fin 3) then c 1 else c 2 := by
  funext i
  rcases site_cases_3 i with hi | hi | hi <;> subst i <;> simp

private theorem early_3 (c : Config 3) (h : LowDensity c) :
    JamFree (runFrom c 0) := by
  apply (blocked_zero_iff_jam_free (runFrom c 0)).mp
  rw [repr_3 c] at h ⊢
  cases h0 : c 0 <;> cases h1 : c 1 <;> cases h2 : c 2 <;>
    simp [LowDensity, cars, h0, h1, h2] at h <;>
    decide

theorem clears_3 (c : Config 3) (h : LowDensity c) :
    JamFree (runFrom c 3) := by
  have ht := free_flow_tail (n := 3) (by omega) c 0 (early_3 c h) 3
  simpa using ht.1

#print axioms site_cases_3
#print axioms repr_3
#print axioms early_3
#print axioms clears_3

private theorem site_cases_4 (v : Fin 4) : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by
  have hv : v.val = 0 ∨ v.val = 1 ∨ v.val = 2 ∨ v.val = 3 := by have hi := v.isLt; omega
  rcases hv with h | h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))

private theorem repr_4 (c : Config 4) :
    c = fun i => if i == (0 : Fin 4) then c 0 else
      if i == (1 : Fin 4) then c 1 else
      if i == (2 : Fin 4) then c 2 else c 3 := by
  funext i
  rcases site_cases_4 i with hi | hi | hi | hi <;> subst i <;> simp

private theorem early_4 (c : Config 4) (h : LowDensity c) :
    JamFree (runFrom c 1) := by
  apply (blocked_zero_iff_jam_free (runFrom c 1)).mp
  rw [repr_4 c] at h ⊢
  cases h0 : c 0 <;> cases h1 : c 1 <;> cases h2 : c 2 <;> cases h3 : c 3 <;>
    simp [LowDensity, cars, h0, h1, h2, h3] at h <;>
    decide

theorem clears_4 (c : Config 4) (h : LowDensity c) :
    JamFree (runFrom c 4) := by
  have ht := free_flow_tail (n := 4) (by omega) c 1 (early_4 c h) 3
  simpa using ht.1

#print axioms site_cases_4
#print axioms repr_4
#print axioms early_4
#print axioms clears_4

private theorem site_cases_5 (v : Fin 5) : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 := by
  have hv : v.val = 0 ∨ v.val = 1 ∨ v.val = 2 ∨ v.val = 3 ∨ v.val = 4 := by have hi := v.isLt; omega
  rcases hv with h | h | h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h))))

private theorem repr_5 (c : Config 5) :
    c = fun i => if i == (0 : Fin 5) then c 0 else
      if i == (1 : Fin 5) then c 1 else
      if i == (2 : Fin 5) then c 2 else
      if i == (3 : Fin 5) then c 3 else c 4 := by
  funext i
  rcases site_cases_5 i with hi | hi | hi | hi | hi <;> subst i <;> simp

private theorem early_5 (c : Config 5) (h : LowDensity c) :
    JamFree (runFrom c 1) := by
  apply (blocked_zero_iff_jam_free (runFrom c 1)).mp
  rw [repr_5 c] at h ⊢
  cases h0 : c 0 <;> cases h1 : c 1 <;> cases h2 : c 2 <;> cases h3 : c 3 <;> cases h4 : c 4 <;>
    simp [LowDensity, cars, h0, h1, h2, h3, h4] at h <;>
    decide

theorem clears_5 (c : Config 5) (h : LowDensity c) :
    JamFree (runFrom c 5) := by
  have ht := free_flow_tail (n := 5) (by omega) c 1 (early_5 c h) 4
  simpa using ht.1

#print axioms site_cases_5
#print axioms repr_5
#print axioms early_5
#print axioms clears_5

private theorem site_cases_6 (v : Fin 6) : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 := by
  have hv : v.val = 0 ∨ v.val = 1 ∨ v.val = 2 ∨ v.val = 3 ∨ v.val = 4 ∨ v.val = 5 := by have hi := v.isLt; omega
  rcases hv with h | h | h | h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h)))))

private theorem repr_6 (c : Config 6) :
    c = fun i => if i == (0 : Fin 6) then c 0 else
      if i == (1 : Fin 6) then c 1 else
      if i == (2 : Fin 6) then c 2 else
      if i == (3 : Fin 6) then c 3 else
      if i == (4 : Fin 6) then c 4 else c 5 := by
  funext i
  rcases site_cases_6 i with hi | hi | hi | hi | hi | hi <;> subst i <;> simp

private theorem early_6 (c : Config 6) (h : LowDensity c) :
    JamFree (runFrom c 2) := by
  apply (blocked_zero_iff_jam_free (runFrom c 2)).mp
  rw [repr_6 c] at h ⊢
  cases h0 : c 0 <;> cases h1 : c 1 <;> cases h2 : c 2 <;> cases h3 : c 3 <;> cases h4 : c 4 <;> cases h5 : c 5 <;>
    simp [LowDensity, cars, h0, h1, h2, h3, h4, h5] at h <;>
    decide

theorem clears_6 (c : Config 6) (h : LowDensity c) :
    JamFree (runFrom c 6) := by
  have ht := free_flow_tail (n := 6) (by omega) c 2 (early_6 c h) 4
  simpa using ht.1

#print axioms site_cases_6
#print axioms repr_6
#print axioms early_6
#print axioms clears_6

private theorem site_cases_7 (v : Fin 7) : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 := by
  have hv : v.val = 0 ∨ v.val = 1 ∨ v.val = 2 ∨ v.val = 3 ∨ v.val = 4 ∨ v.val = 5 ∨ v.val = 6 := by have hi := v.isLt; omega
  rcases hv with h | h | h | h | h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h))))))

private theorem repr_7 (c : Config 7) :
    c = fun i => if i == (0 : Fin 7) then c 0 else
      if i == (1 : Fin 7) then c 1 else
      if i == (2 : Fin 7) then c 2 else
      if i == (3 : Fin 7) then c 3 else
      if i == (4 : Fin 7) then c 4 else
      if i == (5 : Fin 7) then c 5 else c 6 := by
  funext i
  rcases site_cases_7 i with hi | hi | hi | hi | hi | hi | hi <;> subst i <;> simp

private theorem early_7 (c : Config 7) (h : LowDensity c) :
    JamFree (runFrom c 2) := by
  apply (blocked_zero_iff_jam_free (runFrom c 2)).mp
  rw [repr_7 c] at h ⊢
  cases h0 : c 0 <;> cases h1 : c 1 <;> cases h2 : c 2 <;> cases h3 : c 3 <;> cases h4 : c 4 <;> cases h5 : c 5 <;> cases h6 : c 6 <;>
    simp [LowDensity, cars, h0, h1, h2, h3, h4, h5, h6] at h <;>
    decide

theorem clears_7 (c : Config 7) (h : LowDensity c) :
    JamFree (runFrom c 7) := by
  have ht := free_flow_tail (n := 7) (by omega) c 2 (early_7 c h) 5
  simpa using ht.1

#print axioms site_cases_7
#print axioms repr_7
#print axioms early_7
#print axioms clears_7

private theorem site_cases_8 (v : Fin 8) : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 := by
  have hv : v.val = 0 ∨ v.val = 1 ∨ v.val = 2 ∨ v.val = 3 ∨ v.val = 4 ∨ v.val = 5 ∨ v.val = 6 ∨ v.val = 7 := by have hi := v.isLt; omega
  rcases hv with h | h | h | h | h | h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h)))))))

private theorem repr_8 (c : Config 8) :
    c = fun i => if i == (0 : Fin 8) then c 0 else
      if i == (1 : Fin 8) then c 1 else
      if i == (2 : Fin 8) then c 2 else
      if i == (3 : Fin 8) then c 3 else
      if i == (4 : Fin 8) then c 4 else
      if i == (5 : Fin 8) then c 5 else
      if i == (6 : Fin 8) then c 6 else c 7 := by
  funext i
  rcases site_cases_8 i with hi | hi | hi | hi | hi | hi | hi | hi <;> subst i <;> simp

set_option maxHeartbeats 3000000 in
private theorem early_8 (c : Config 8) (h : LowDensity c) :
    JamFree (runFrom c 3) := by
  apply (blocked_zero_iff_jam_free (runFrom c 3)).mp
  rw [repr_8 c] at h ⊢
  cases h0 : c 0 <;> cases h1 : c 1 <;> cases h2 : c 2 <;> cases h3 : c 3 <;> cases h4 : c 4 <;> cases h5 : c 5 <;> cases h6 : c 6 <;> cases h7 : c 7 <;>
    simp [LowDensity, cars, h0, h1, h2, h3, h4, h5, h6, h7] at h <;>
    decide

theorem clears_8 (c : Config 8) (h : LowDensity c) :
    JamFree (runFrom c 8) := by
  have ht := free_flow_tail (n := 8) (by omega) c 3 (early_8 c h) 5
  simpa using ht.1

#print axioms site_cases_8
#print axioms repr_8
#print axioms early_8
#print axioms clears_8

theorem clears_up_to_eight (n : Nat) [NeZero n] (hn : 2 ≤ n) (h8 : n ≤ 8)
    (c : Config n) (h : LowDensity c) : JamFree (runFrom c n) := by
  have hc : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
  rcases hc with he | he | he | he | he | he | he
  · subst n
    exact clears_2 c h
  · subst n
    exact clears_3 c h
  · subst n
    exact clears_4 c h
  · subst n
    exact clears_5 c h
  · subst n
    exact clears_6 c h
  · subst n
    exact clears_7 c h
  · subst n
    exact clears_8 c h

#print axioms clears_up_to_eight
end SixBirdsFoundationsVI.Instances.Rule184Small
