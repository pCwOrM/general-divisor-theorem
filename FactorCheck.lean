import Mathlib

private theorem factor_product_identity (d : Nat) (hd : d > 0) :
    (d : Rat) / (Nat.totient d : Rat) =
      d.primeFactors.prod
        (fun p => (p : Rat) / ((p : Rat) - 1)) := by
  have hd0 : (d : Rat) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hd)
  have htot : (Nat.totient d : Rat) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hd).ne'
  have hprod := Nat.totient_eq_mul_prod_factors d
  have hfactor :
      ∀ p ∈ d.primeFactors,
        (1 - (p : Rat)⁻¹) *
          ((p : Rat) / ((p : Rat) - 1)) = 1 := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hp0 : (p : Rat) ≠ 0 := by
      exact_mod_cast hprime.ne_zero
    have hp1 : (p : Rat) - 1 ≠ 0 := by
      have h : p ≠ 1 := hprime.ne_one
      exact sub_ne_zero.mpr (by exact_mod_cast h)
    field_simp
    <;> ring
  have hproducts :
      (d.primeFactors.prod
        (fun p => 1 - (p : Rat)⁻¹)) *
      (d.primeFactors.prod
        (fun p => (p : Rat) / ((p : Rat) - 1))) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p hp
    exact hfactor p hp
  apply (div_eq_iff htot).mpr
  rw [hprod]
  calc
    (d : Rat) =
        (d : Rat) * 1 := (mul_one _).symm
    _ = (d : Rat) *
        ((d.primeFactors.prod
          (fun p => 1 - (p : Rat)⁻¹)) *
         (d.primeFactors.prod
          (fun p => (p : Rat) / ((p : Rat) - 1)))) := by
      rw [hproducts]
    _ = (d.primeFactors.prod
          (fun p => (p : Rat) / ((p : Rat) - 1))) *
        ((d : Rat) *
         (d.primeFactors.prod
          (fun p => 1 - (p : Rat)⁻¹))) := by
      ring
