import DensityBridge

namespace GeneralDivisorTheorem

/-- Number of admissible integers below X. -/
noncomputable def countBelow
    (N m : Nat) (a : Int) (X : Nat) : Nat := by
  classical
  exact ((Finset.range X).filter
    (fun n => S_indicator N m a n)).card

/-- The GDT indicator is unchanged after any natural multiple
    of T_min. -/
theorem S_indicator_add_mul_T_min
    (N m : Nat) (a : Int) (n q : Nat)
    (h_adm : Nat.gcd a.natAbs (d_param N m) = 1) :
    S_indicator N m a (n + q * T_min N m) ↔
      S_indicator N m a n := by
  induction q with
  | zero =>
      simp
  | succ q ih =>
      have hstep :=
        T_min_is_period N m a
          (n + q * T_min N m) h_adm
      exact (by
        simpa [Nat.succ_mul, Nat.add_assoc] using
          hstep.trans ih)

/-- The first-period count is the cumulative count at T_min. -/
theorem countBelow_T_min_eq_countOnePeriod
    (N m : Nat) (a : Int) :
    countBelow N m a (T_min N m) =
      countOnePeriod N m a := by
  rfl

/-- An admissible first period contains exactly φ(R) points. -/
theorem countBelow_T_min
    (N m : Nat) (a : Int)
    (hN : 0 < N) (hm : 0 < m)
    (h_adm : Nat.gcd a.natAbs (d_param N m) = 1) :
    countBelow N m a (T_min N m) =
      Nat.totient (R_param N m) := by
  rw [countBelow_T_min_eq_countOnePeriod]
  exact gdt_count_per_period N m a hN hm h_adm


/-- Number of admissible integers in the q-th full T_min block. -/
noncomputable def countBlock
    (N m : Nat) (a : Int) (q : Nat) : Nat := by
  classical
  exact
    ((Finset.Ico
        (q * T_min N m)
        ((q + 1) * T_min N m)).filter
      (fun n => S_indicator N m a n)).card

/-- Every translated full T_min-block contains the same number of
    admissible points as the first period. -/
theorem countBlock_eq_countOnePeriod
    (N m : Nat) (a : Int) (q : Nat)
    (h_adm : Nat.gcd a.natAbs (d_param N m) = 1) :
    countBlock N m a q = countOnePeriod N m a := by
  classical
  unfold countBlock countOnePeriod

  have hend :
      (q + 1) * T_min N m =
        q * T_min N m + T_min N m := by
    simp [Nat.add_mul]

  apply Finset.card_bij
    (fun n _ => n - q * T_min N m)

  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ico] at hn
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rw [hend] at hn
      omega
    · have hshift :
          (n - q * T_min N m) + q * T_min N m = n := by
        omega
      have hs :
          S_indicator N m a
            ((n - q * T_min N m) + q * T_min N m) := by
        rw [hshift]
        exact hn.2
      exact
        (S_indicator_add_mul_T_min
          N m a (n - q * T_min N m) q h_adm).mp hs

  · intro n₁ hn₁ n₂ hn₂ h
    simp only [Finset.mem_filter, Finset.mem_Ico] at hn₁ hn₂
    omega

  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    refine ⟨k + q * T_min N m, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_Ico]
      constructor
      · constructor
        · omega
        · rw [hend]
          omega
      · exact
          (S_indicator_add_mul_T_min
            N m a k q h_adm).mpr hk.2
    · omega


/-- Cumulative count recurrence by adjoining one full T_min block. -/
theorem countBelow_succ_mul_T_min
    (N m : Nat) (a : Int) (q : Nat) :
    countBelow N m a ((q + 1) * T_min N m) =
      countBelow N m a (q * T_min N m) +
        countBlock N m a q := by
  classical
  unfold countBelow countBlock

  let T := T_min N m
  let A := Finset.Ico 0 (q * T)
  let B := Finset.Ico (q * T) ((q + 1) * T)

  have hA :
      Finset.range (q * T) = A := by
    simpa [A] using congrFun Finset.range_eq_Ico (q * T)

  have hAll :
      Finset.range ((q + 1) * T) = A ∪ B := by
    rw [Finset.range_eq_Ico]
    unfold A B
    symm
    exact Finset.Ico_union_Ico_eq_Ico
      (Nat.zero_le (q * T))
      (Nat.mul_le_mul_right T (Nat.le_add_right q 1))

  have hdisj : Disjoint A B := by
    unfold A B
    exact Finset.disjoint_left.mpr (by
      intro x hxA hxB
      simp only [Finset.mem_Ico] at hxA hxB
      omega)

  rw [hAll, Finset.filter_union]
  rw [Finset.card_union_of_disjoint]
  · rw [← hA]
  · exact hdisj.mono
      (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)




/-- The first q complete periods contain exactly q * φ(R)
    admissible integers. -/
theorem countBelow_mul_T_min
    (N m : Nat) (a : Int) (q : Nat)
    (hN : 0 < N) (hm : 0 < m)
    (h_adm : Nat.gcd a.natAbs (d_param N m) = 1) :
    countBelow N m a (q * T_min N m) =
      q * Nat.totient (R_param N m) := by
  induction q with
  | zero =>
      simp [countBelow]
  | succ q ih =>
      calc
        countBelow N m a (Nat.succ q * T_min N m) =
            countBelow N m a (q * T_min N m) +
              countBlock N m a q := by
          simpa [Nat.succ_eq_add_one] using
            countBelow_succ_mul_T_min N m a q
        _ =
            q * Nat.totient (R_param N m) +
              Nat.totient (R_param N m) := by
          rw [ih]
          rw [countBlock_eq_countOnePeriod N m a q h_adm]
          rw [gdt_count_per_period N m a hN hm h_adm]
        _ =
            Nat.succ q * Nat.totient (R_param N m) := by
          simp [Nat.succ_mul]


/-- Exact quotient/remainder count below q*T_min + s. -/
theorem countBelow_mul_T_min_add
    (N m : Nat) (a : Int) (q s : Nat)
    (hN : 0 < N) (hm : 0 < m)
    (h_adm : Nat.gcd a.natAbs (d_param N m) = 1) :
    countBelow N m a (q * T_min N m + s) =
      q * Nat.totient (R_param N m) +
        countBelow N m a s := by
  classical

  let T := T_min N m
  let A := Finset.Ico 0 (q * T)
  let B := Finset.Ico (q * T) (q * T + s)

  have hA :
      Finset.range (q * T) = A := by
    simpa [A] using congrFun Finset.range_eq_Ico (q * T)

  have hAll :
      Finset.range (q * T + s) = A ∪ B := by
    rw [Finset.range_eq_Ico]
    unfold A B
    symm
    exact Finset.Ico_union_Ico_eq_Ico
      (Nat.zero_le (q * T))
      (Nat.le_add_right (q * T) s)

  have hdisj : Disjoint A B := by
    unfold A B
    exact Finset.disjoint_left.mpr (by
      intro x hxA hxB
      simp only [Finset.mem_Ico] at hxA hxB
      omega)

  have htail :
      ((B.filter (fun n => S_indicator N m a n)).card) =
        countBelow N m a s := by
    unfold B countBelow
    apply Finset.card_bij
      (fun n _ => n - q * T)

    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ico] at hn
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · omega
      · have hshift :
            (n - q * T) + q * T = n := by
          omega
        have hsind :
            S_indicator N m a
              ((n - q * T) + q * T) := by
          rw [hshift]
          exact hn.2
        exact
          (S_indicator_add_mul_T_min
            N m a (n - q * T) q h_adm).mp hsind

    · intro n₁ hn₁ n₂ hn₂ h
      simp only [Finset.mem_filter, Finset.mem_Ico] at hn₁ hn₂
      omega

    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      refine ⟨k + q * T, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_Ico]
        constructor
        · constructor
          · omega
          · omega
        · exact
            (S_indicator_add_mul_T_min
              N m a k q h_adm).mpr hk.2
      · omega

  unfold countBelow
  rw [hAll, Finset.filter_union]
  rw [Finset.card_union_of_disjoint]
  · rw [← hA]
    rw [← countBelow]
    rw [countBelow_mul_T_min N m a q hN hm h_adm]
    rw [htail]
    rfl
  · exact hdisj.mono
      (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)

end GeneralDivisorTheorem
