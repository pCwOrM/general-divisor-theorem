import Mathlib

private def rad (n : Nat) : Nat :=
  if n = 0 then 0 else n.primeFactors.prod id

private theorem rad_primeFactors (k : Nat) (hk : k > 0) :
    (rad k).primeFactors = k.primeFactors := by
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  unfold rad
  simp only [if_neg hk0]
  apply Nat.primeFactors_prod
  intro p hp
  exact Nat.prime_of_mem_primeFactors hp

private theorem exponent_product_eq (k : Nat) (hk : k > 0) :
    (Nat.totient k : Rat) * (rad k : Rat) =
      (Nat.totient (rad k) : Rat) * (k : Rat) := by
  have hprod := Nat.totient_eq_mul_prod_factors k
  have hrad := Nat.totient_eq_mul_prod_factors (rad k)
  rw [rad_primeFactors k hk] at hrad
  rw [hprod, hrad]
  ring

private theorem exponent_blindness (k : Nat) (hk : k > 0) :
    (k : Rat) / (Nat.totient k : Rat) =
      (rad k : Rat) / (Nat.totient (rad k) : Rat) := by
  have hk0 : (Nat.totient k : Rat) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hk).ne'
  have hrpos : 0 < rad k := by
    unfold rad
    simp only [if_neg (Nat.ne_of_gt hk)]
    exact Finset.prod_pos fun p hp =>
      Nat.pos_of_mem_primeFactors hp
  have hr0 : (Nat.totient (rad k) : Rat) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hrpos).ne'
  apply (div_eq_div_iff hk0 hr0).mpr
  linear_combination -(exponent_product_eq k hk)
