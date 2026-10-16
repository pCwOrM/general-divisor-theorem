import Mathlib

private theorem primorial_squarefree
    (N : Nat)
    (h_sqf : ∀ p, p^2 ∣ N → p = 1) :
    Squarefree N := by
  intro p hp
  rw [h_sqf p (by simpa [pow_two] using hp)]
  exact isUnit_one

private theorem primorial_positive
    (N : Nat)
    (h_sqf : ∀ p, p^2 ∣ N → p = 1) :
    N > 0 := by
  have hN : N ≠ 0 := by
    intro hz
    have h : (2 : Nat)^2 ∣ N := by
      rw [hz]
      exact dvd_zero _
    have heq := h_sqf 2 h
    omega
  omega


private theorem primorial_divisor_squarefree
    (N m : Nat) (hN : Squarefree N)
    (hm : m ∣ N) :
    Squarefree m := by
  intro x hx
  apply hN x
  exact dvd_trans hx hm

private theorem primorial_quotient_squarefree
    (N m : Nat) (hN : Squarefree N)
    (hm : m ∣ N) :
    Squarefree (N / m) := by
  intro x hx
  apply hN x
  exact dvd_trans hx (Nat.div_dvd_of_dvd hm)

private theorem primorial_coprime
    (N m : Nat) (hN : Squarefree N)
    (hm : m ∣ N) :
    Nat.Coprime m (N / m) := by
  have hmul : m * (N / m) = N :=
    Nat.mul_div_cancel' hm
  have hg : Nat.gcd m (N / m) = 1 := by
    by_contra h
    have hgpos : 0 < Nat.gcd m (N / m) := by
      have hN0 : N ≠ 0 := by
        intro hz
        have hzero : Squarefree (0 : Nat) := by
          rw [hz] at hN
          exact hN
        have hu := hzero 2 (dvd_zero _)
        have heq : (2 : Nat) = 1 := Nat.isUnit_iff.mp hu
        omega
      have hm0 : m ≠ 0 := by
        intro hz
        have : N = 0 := by
          rw [← hmul, hz]
          simp
        exact hN0 this
      exact Nat.pos_of_ne_zero (by
        intro hz
        have := Nat.gcd_eq_zero_iff.mp hz
        exact hm0 this.1)
    have hg2 : 2 ≤ Nat.gcd m (N / m) := by omega
    obtain ⟨p, hp, hpdvd⟩ :=
      Nat.exists_prime_and_dvd (by omega : Nat.gcd m (N / m) ≠ 1)
    have hpm : p ∣ m :=
      dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
    have hpq : p ∣ N / m :=
      dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
    have hp2 : p * p ∣ N := by
      rw [← hmul]
      exact mul_dvd_mul hpm hpq
    have hu := hN p hp2
    have hp1 : p = 1 := Nat.isUnit_iff.mp hu
    exact hp.ne_one hp1
  exact hg

