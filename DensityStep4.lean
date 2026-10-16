import GeneralDivisorTheorem

namespace GeneralDivisorTheorem

/-- The arithmetic progression has distinct entries. -/
theorem progression_injective (r m : Nat)
    (hm : 0 < m) :
    Function.Injective (fun k : Nat => r + m * k) := by
  intro k₁ k₂ h
  have hmul : m * k₁ = m * k₂ :=
    Nat.add_left_cancel h
  exact Nat.eq_of_mul_eq_mul_left hm hmul

end GeneralDivisorTheorem
