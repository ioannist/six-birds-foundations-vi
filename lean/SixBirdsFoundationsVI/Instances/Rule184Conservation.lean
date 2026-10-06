import SixBirdsFoundationsVI.Instances.Rule184

namespace SixBirdsFoundationsVI.Instances.Rule184Conservation
open SixBirdsFoundationsVI.Instances.Rule184

def sumFin (n : Nat) (f : Fin n → Nat) : Nat := (List.ofFn f).sum

private theorem sumFin_add (n : Nat) (f g : Fin n → Nat) :
    sumFin n (fun i => f i + g i) = sumFin n f + sumFin n g := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
      simp only [sumFin, List.ofFn_succ, List.sum_cons]
      have ht := ih (fun i => f i.succ) (fun i => g i.succ)
      simp only [sumFin] at ht
      rw [ht]
      omega

private theorem sumFin_shift (m : Nat) (f : Fin (m+1) → Nat) :
    sumFin (m+1) (fun i => f (i+1)) = sumFin (m+1) f := by
  have hs (i : Fin m) : (i.castSucc : Fin (m+1)) + 1 = i.succ := by
    apply Fin.ext
    simp
  have hl : (Fin.last m : Fin (m+1)) + 1 = 0 := by
    apply Fin.ext
    simp
  have ht : List.ofFn (fun i : Fin m => f ((i.castSucc : Fin (m+1)) + 1)) =
      List.ofFn (fun i : Fin m => f i.succ) := by
    congr 1
    funext i
    rw [hs i]
  unfold sumFin
  rw [List.ofFn_succ_last, ht, hl, List.sum_append_nat, List.sum_cons, List.sum_nil]
  rw [List.ofFn_succ, List.sum_cons]
  omega

private theorem countP_as_sum (l : List Bool) :
    l.countP id = (l.map Bool.toNat).sum := by
  induction l with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [ih] <;> omega

theorem cars_as_sum (n : Nat) (c : Config n) :
    cars c = sumFin n (fun i => (c i).toNat) := by
  unfold cars sumFin
  rw [countP_as_sum]
  have hm (m : Nat) (f : Fin m → Bool) :
      (List.ofFn f).map Bool.toNat = List.ofFn (fun i => (f i).toNat) := by
    induction m with
    | zero => simp
    | succ m ih => simp [List.ofFn_succ, ih]
  rw [hm]

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

private theorem local_conservation (a b d : Bool) :
    (((a && b) || (!a && d)).toNat) =
      (a && b).toNat + (!a && d).toNat := by
  cases a <;> cases b <;> cases d <;> decide

private theorem local_partition (a b : Bool) :
    a.toNat = (a && b).toNat + (a && !b).toNat := by
  cases a <;> cases b <;> decide

theorem cars_conserved {n : Nat} [NeZero n] (hn : 2 ≤ n) (c : Config n) :
    cars (step c) = cars c := by
  let blocked : Fin n → Nat := fun i => (c i && c (i + 1)).toNat
  let incoming : Fin n → Nat := fun i => (!c i && c (i - 1)).toNat
  let outgoing : Fin n → Nat := fun i => (c i && !c (i + 1)).toNat
  have hp (i : Fin n) : (step c i).toNat = blocked i + incoming i := by
    exact local_conservation (c i) (c (i + 1)) (c (i - 1))
  have hsplit : sumFin n (fun i => (step c i).toNat) =
      sumFin n blocked + sumFin n incoming := by
    calc
      sumFin n (fun i => (step c i).toNat) =
          sumFin n (fun i => blocked i + incoming i) := by
            congr 1; funext i; exact hp i
      _ = _ := sumFin_add n blocked incoming
  have hshift : sumFin n incoming = sumFin n outgoing := by
    cases n with
    | zero => omega
    | succ m =>
        have hs := sumFin_shift m incoming
        have heq : (fun i : Fin (m + 1) => incoming (i + 1)) = outgoing := by
          funext i
          simp only [incoming, outgoing, next_prev hn i]
          cases c i <;> cases c (i + 1) <;> decide
        rw [heq] at hs
        exact hs.symm
  have hpart : sumFin n (fun i => (c i).toNat) =
      sumFin n blocked + sumFin n outgoing := by
    calc
      sumFin n (fun i => (c i).toNat) =
          sumFin n (fun i => blocked i + outgoing i) := by
            congr 1; funext i; exact local_partition (c i) (c (i + 1))
      _ = _ := sumFin_add n blocked outgoing
  rw [cars_as_sum n (step c), cars_as_sum n c]
  omega

#print axioms next_prev
#print axioms local_conservation
#print axioms local_partition
#print axioms cars_conserved
#print axioms sumFin_add
#print axioms sumFin_shift
#print axioms countP_as_sum
#print axioms cars_as_sum
end SixBirdsFoundationsVI.Instances.Rule184Conservation
