import DensityLimit
import CorrectionBridge

namespace GeneralDivisorTheorem

/-- For positive N and m, the shared radical d is positive. -/
theorem d_param_pos
    (N m : Nat)
    (hN : 0 < N) (hm : 0 < m) :
    0 < d_param N m := by
  unfold d_param rad

  have hg : Nat.gcd m N ≠ 0 := by
    intro h
    have hz := Nat.gcd_eq_zero_iff.mp h
    exact (Nat.ne_of_gt hm) hz.1

  simp only [if_neg hg]

  exact Finset.prod_pos fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).pos

/-- For positive N and m, admissibility has the exact dichotomy:
    gcd(a,d)=1 or gcd(a,d)>1. -/
theorem admissible_or_inadmissible
    (N m : Nat) (a : Int)
    (hN : 0 < N) (hm : 0 < m) :
    Nat.gcd a.natAbs (d_param N m) = 1 ∨
      Nat.gcd a.natAbs (d_param N m) > 1 := by
  have hd : 0 < d_param N m :=
    d_param_pos N m hN hm

  have hg :
      0 < Nat.gcd a.natAbs (d_param N m) :=
    Nat.gcd_pos_of_pos_right a.natAbs hd

  by_cases h :
      Nat.gcd a.natAbs (d_param N m) = 1
  · exact Or.inl h
  · right
    omega


/-- Unified General Divisor Theorem.

For positive N and m, exactly one of the two arithmetic branches applies.

* Inadmissible: gcd(a,d) > 1, so the constrained set is empty.
* Admissible: gcd(a,d) = 1, giving exact periodicity, the φ(R)
  count per period, the exact arbitrary-bound count, natural density,
  and the correction identity.
-/
theorem general_divisor_theorem
    (N m : Nat) (a : Int)
    (hN : 0 < N) (hm : 0 < m) :
    (∀ n : Nat, ¬ S_indicator N m a n) ∨
    (
      Nat.gcd a.natAbs (d_param N m) = 1 ∧
      (∀ n : Nat,
        S_indicator N m a (n + T_min N m) ↔
          S_indicator N m a n) ∧
      countOnePeriod N m a =
        Nat.totient (R_param N m) ∧
      (∀ q s : Nat,
        countBelow N m a (q * T_min N m + s) =
          q * Nat.totient (R_param N m) +
            countBelow N m a s) ∧
      Filter.Tendsto
        (fun X : Nat =>
          (countBelow N m a X : ℝ) / X)
        Filter.atTop
        (nhds (
          (Nat.totient (R_param N m) : ℝ) /
            T_min N m)) ∧
      Nat.totient (R_param N m) *
          N *
          Nat.totient (d_param N m) =
        d_param N m *
          R_param N m *
          Nat.totient N
    ) := by

  rcases admissible_or_inadmissible N m a hN hm with
    hadm | hinadm

  · right
    refine ⟨hadm, ?_, ?_, ?_, ?_, ?_⟩

    · intro n
      exact T_min_is_period N m a n hadm

    · exact gdt_count_per_period N m a hN hm hadm

    · intro q s
      exact countBelow_mul_T_min_add
        N m a q s hN hm hadm

    · exact density_limit N m a hN hm hadm

    · exact gdt_correction_identity N m hN hm

  · left
    intro n hn
    unfold S_indicator at hn
    exact
      (inadmissible_empty_criterion N m a hinadm n hn.1)
        hn.2

end GeneralDivisorTheorem
