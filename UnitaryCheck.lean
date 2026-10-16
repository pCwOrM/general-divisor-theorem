import Mathlib

namespace UnitaryCheck

def rad (n : Nat) : Nat :=
  if n = 0 then 0 else n.primeFactors.prod id

private theorem rad_mul_coprime
    (a b : Nat) (ha : a > 0) (hb : b > 0)
    (hab : Nat.Coprime a b) :
    rad (a * b) = rad a * rad b := by
  have ha0 : a ≠ 0 := Nat.ne_of_gt ha
  have hb0 : b ≠ 0 := Nat.ne_of_gt hb
  have hab0 : a * b ≠ 0 := mul_ne_zero ha0 hb0
  have hdisj :
      Disjoint a.primeFactors b.primeFactors := by
    apply Finset.disjoint_left.mpr
    intro p hpa hpb
    have hp : Nat.Prime p :=
      Nat.prime_of_mem_primeFactors hpa
    have hdiva : p ∣ a :=
      (Nat.mem_primeFactors.mp hpa).2.1
    have hdivb : p ∣ b :=
      (Nat.mem_primeFactors.mp hpb).2.1
    have hdivgcd : p ∣ Nat.gcd a b :=
      Nat.dvd_gcd hdiva hdivb
    rw [hab.gcd_eq_one] at hdivgcd
    exact hp.ne_one (Nat.dvd_one.mp hdivgcd)
  unfold rad
  simp only [if_neg ha0, if_neg hb0, if_neg hab0]
  rw [Nat.primeFactors_mul ha0 hb0]
  exact Finset.prod_union hdisj

end UnitaryCheck

namespace UnitaryCheck

private theorem rad_pos (n : Nat) (hn : n > 0) :
    0 < rad n := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  unfold rad
  simp only [if_neg hn0]
  exact Finset.prod_pos (by
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).pos)

private theorem unitary_rad_quotient
    (N m : Nat) (hm : m > 0)
    (h_div : m ∣ N)
    (h_unit : Nat.Coprime m (N / m))
    (hN : N > 0) :
    rad N = rad m * rad (N / m) := by
  have hq : N / m > 0 := by
    have hN0 : N ≠ 0 := Nat.ne_of_gt hN
    have hq0 : N / m ≠ 0 := by
      intro hz
      have heq := Nat.mul_div_cancel' h_div
      rw [hz] at heq
      simp at heq
      exact hN0 heq.symm
    exact Nat.pos_of_ne_zero hq0
  have hNmul : m * (N / m) = N :=
    Nat.mul_div_cancel' h_div
  calc
    rad N = rad (m * (N / m)) := by rw [hNmul]
    _ = rad m * rad (N / m) :=
      rad_mul_coprime m (N / m) hm hq h_unit

end UnitaryCheck

namespace UnitaryCheck

private theorem unitary_gcd
    (N m : Nat) (h_div : m ∣ N) :
    Nat.gcd m N = m := by
  exact Nat.gcd_eq_left_iff_dvd.mpr h_div

private theorem unitary_rad_cancel
    (N m : Nat) (hm : m > 0)
    (h_div : m ∣ N)
    (h_unit : Nat.Coprime m (N / m))
    (hN : N > 0)
    (R : Nat)
    (hR : rad N = rad (Nat.gcd m N) * R) :
    R = rad (N / m) := by
  have hgcd : Nat.gcd m N = m :=
    unitary_gcd N m h_div
  rw [hgcd] at hR
  have hrad :
      rad N = rad m * rad (N / m) :=
    unitary_rad_quotient N m hm h_div h_unit hN
  have hpos : 0 < rad m := rad_pos m hm
  exact Nat.eq_of_mul_eq_mul_left hpos (hR.symm.trans hrad)

end UnitaryCheck
