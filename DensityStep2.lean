import GeneralDivisorTheorem

namespace GeneralDivisorTheorem

/-- The canonical natural representative of an integer modulo m. -/
def residue (a : Int) (m : Nat) : Nat :=
  (a % (m : Int)).toNat

example (a : Int) (m : Nat) (hm : 0 < m) :
    residue a m < m := by
  unfold residue
  have hpos : (0 : Int) ≤ a % (m : Int) :=
    Int.emod_nonneg _ (by omega)
  have hlt : a % (m : Int) < (m : Int) :=
    Int.emod_lt_of_pos _ (by omega)
  omega


example (a : Int) (N m k : Nat)
    (hN : 0 < N) (hm : 0 < m)
    (hk : k < R_param N m) :
    residue a m + m * k < T_min N m := by
  have hr : residue a m < m := by
    unfold residue
    have hpos : (0 : Int) ≤ a % (m : Int) :=
      Int.emod_nonneg _ (by omega)
    have hlt : a % (m : Int) < (m : Int) :=
      Int.emod_lt_of_pos _ (by omega)
    omega
  have hstep : m * (k + 1) ≤ m * R_param N m := by
    exact Nat.mul_le_mul_left m (Nat.succ_le_of_lt hk)
  have hexpand : m * (k + 1) = m * k + m := by
    simp [Nat.mul_succ, Nat.add_comm]
  rw [hexpand] at hstep
  unfold T_min
  omega

end GeneralDivisorTheorem
