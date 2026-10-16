import GeneralDivisorTheorem

namespace GeneralDivisorTheorem

/-- Euler's totient factors across the shared and unshared
    radical parts because d and R are coprime. -/
theorem totient_rad_eq_d_mul_R
    (N m : Nat)
    (hN : 0 < N) (hm : 0 < m) :
    Nat.totient (rad N) =
      Nat.totient (d_param N m) *
        Nat.totient (R_param N m) := by
  rw [rad_eq_d_mul_R N m]
  exact Nat.totient_mul (coprime_d_R N m hN hm)

/-- Integer correction identity underlying the GDT density factor. -/
theorem gdt_correction_identity
    (N m : Nat)
    (hN : 0 < N) (hm : 0 < m) :
    Nat.totient (R_param N m) *
        N *
        Nat.totient (d_param N m) =
      d_param N m *
        R_param N m *
        Nat.totient N := by

  have hNtot :
      (Nat.totient N : Rat) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hN).ne'

  have hR : 0 < R_param N m :=
    R_param_pos N m hN hm

  have hdR :
      0 < d_param N m * R_param N m := by
    rw [← rad_eq_d_mul_R N m]
    unfold rad
    simp only [if_neg (Nat.ne_of_gt hN)]
    exact Finset.prod_pos fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).pos

  have hrad : 0 < rad N := by
    simpa [rad_eq_d_mul_R N m] using hdR

  have hradtot :
      (Nat.totient (rad N) : Rat) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hrad).ne'

  have hblind := exponent_blindness N hN

  have hcross :
      (N : Rat) * Nat.totient (rad N) =
        (rad N : Rat) * Nat.totient N := by
    field_simp [hNtot, hradtot] at hblind
    exact hblind

  rw [rad_eq_d_mul_R N m] at hcross
  rw [Nat.totient_mul (coprime_d_R N m hN hm)] at hcross

  have hcrossNat :
      N *
          (Nat.totient (d_param N m) *
            Nat.totient (R_param N m)) =
        d_param N m *
          R_param N m *
          Nat.totient N := by
    exact_mod_cast hcross

  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hcrossNat

end GeneralDivisorTheorem
