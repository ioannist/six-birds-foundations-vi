/- Binary cyclic words are represented by their periodic extension to Nat. -/
namespace SixBirdsFoundationsVI.Instances.Ducci

def Shift (f : Nat → Bool) (i : Nat) : Bool := f (i + 1)
def D (f : Nat → Bool) (i : Nat) : Bool := f i ^^ Shift f i
def Iter : Nat → (Nat → Bool) → (Nat → Bool)
  | 0, f => f
  | m + 1, f => D (Iter m f)
def Periodic (n : Nat) (f : Nat → Bool) : Prop := ∀ i, f (i + n) = f i

theorem iter_add (a b : Nat) (f : Nat → Bool) :
    Iter (a + b) f = Iter b (Iter a f) := by
  induction b with
  | zero => rfl
  | succ b ih => simp [Iter, ih]

theorem iter_pow_two (k : Nat) (f : Nat → Bool) (i : Nat) :
    Iter (2 ^ k) f i = (f i ^^ f (i + 2 ^ k)) := by
  induction k generalizing f i with
  | zero => simp [Iter, D, Shift]
  | succ k ih =>
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
        rw [Nat.pow_succ]; omega
      rw [hpow, iter_add]
      have hshift : ∀ g : Nat → Bool, ∀ j,
          Iter (2 ^ k) g j = (g j ^^ g (j + 2 ^ k)) := by
        intro g j
        exact ih g j
      rw [hshift, hshift]
      simp only [ih]
      have hadd : i + 2 ^ k + 2 ^ k = i + (2 ^ k + 2 ^ k) := by omega
      rw [hadd]
      have hx : ∀ a b c : Bool, ((a ^^ b) ^^ (b ^^ c)) = (a ^^ c) := by
        intro a b c
        rw [Bool.xor_assoc, ← Bool.xor_assoc b b c, Bool.xor_self, Bool.false_xor]
      exact hx _ _ _

theorem ducci_nilpotent (k : Nat) (f : Nat → Bool)
    (hperiod : Periodic (2 ^ k) f) :
    Iter (2 ^ k) f = fun _ => false := by
  funext i
  rw [iter_pow_two, hperiod i, Bool.xor_self]

/-- A finite binary cyclic vector, indexed modulo its length. -/
def Vec (n : Nat) := Fin n → Bool

def liftVec (n : Nat) (hn : 0 < n) (v : Vec n) (i : Nat) : Bool :=
  v ⟨i % n, Nat.mod_lt i hn⟩

def Dvec (n : Nat) (hn : 0 < n) (v : Vec n) (i : Fin n) : Bool :=
  v i ^^ v ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

def IterVec (n : Nat) (hn : 0 < n) : Nat → Vec n → Vec n
  | 0, v => v
  | j + 1, v => Dvec n hn (IterVec n hn j v)

theorem lift_periodic (n : Nat) (hn : 0 < n) (v : Vec n) :
    Periodic n (liftVec n hn v) := by
  intro i
  simp [liftVec]

theorem lift_Dvec (n : Nat) (hn : 0 < n) (v : Vec n) :
    liftVec n hn (Dvec n hn v) = D (liftVec n hn v) := by
  funext i
  simp only [liftVec, Dvec, D, Shift]
  congr 1
  apply congrArg v
  apply Fin.ext
  simp [Nat.add_mod]

theorem lift_iterVec (n : Nat) (hn : 0 < n) (j : Nat) (v : Vec n) :
    liftVec n hn (IterVec n hn j v) = Iter j (liftVec n hn v) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [IterVec, Iter]
      rw [lift_Dvec, ih]

/-- The Ducci operator on (F₂)^(2^k) is zero after 2^k steps. -/
theorem ducci_vector_nilpotent (k : Nat) (v : Vec (2 ^ k)) :
    IterVec (2 ^ k) (Nat.pow_pos (by decide)) (2 ^ k) v = fun _ => false := by
  let hn : 0 < 2 ^ k := Nat.pow_pos (by decide)
  have hz := ducci_nilpotent k (liftVec (2 ^ k) hn v) (lift_periodic _ hn v)
  have hl := lift_iterVec (2 ^ k) hn (2 ^ k) v
  funext i
  have hi := congrFun (hl.trans hz) i.val
  simpa [liftVec, Nat.mod_eq_of_lt i.isLt] using hi

#print axioms iter_add
#print axioms iter_pow_two
#print axioms ducci_nilpotent
#print axioms lift_periodic
#print axioms lift_Dvec
#print axioms lift_iterVec
#print axioms ducci_vector_nilpotent

end SixBirdsFoundationsVI.Instances.Ducci
