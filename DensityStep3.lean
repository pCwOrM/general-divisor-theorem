import GeneralDivisorTheorem

namespace GeneralDivisorTheorem

def residue3 (a : Int) (m : Nat) : Nat :=
  (a % (m : Int)).toNat

/-- Congruent integers have the same canonical natural remainder. -/
private theorem residue3_eq_mod (a : Int) (m n : Nat)
    (hm : 0 < m)
    (hc : (n : Int) ≡ a [ZMOD (m : Int)]) :
    n % m = residue3 a m := by
  unfold residue3
  have hmod :
      (n : Int) % (m : Int) = a % (m : Int) := by
    exact hc
  have hn :
      ((n : Int) % (m : Int)).toNat = n % m := by
    omega
  rw [← hn, hmod]

/-- Every congruent n in the period has a progression index k < R. -/
theorem progression_surjective (N m n : Nat) (a : Int)
    (hm : 0 < m)
    (hn : n < T_min N m)
    (hc : (n : Int) ≡ a [ZMOD (m : Int)]) :
    ∃ k : Nat,
      k < R_param N m ∧
      n = residue3 a m + m * k := by
  refine ⟨n / m, ?_, ?_⟩
  · unfold T_min at hn
    exact (Nat.div_lt_iff_lt_mul hm).2 (by
      simpa [Nat.mul_comm] using hn)
  · have hr := residue3_eq_mod a m n hm hc
    have hdecomp := Nat.mod_add_div n m
    omega

end GeneralDivisorTheorem
