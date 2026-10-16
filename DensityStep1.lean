import GeneralDivisorTheorem

namespace GeneralDivisorTheorem

example (N m : Nat)
    (hN : 0 < N) (hm : 0 < m) :
    0 < R_param N m := by
  have hcop := coprime_m_R N m hN hm
  have hrad : 0 < rad N := by
    unfold rad
    have hN0 : N ≠ 0 := Nat.ne_of_gt hN
    simp only [if_neg hN0]
    exact Finset.prod_pos fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).pos
  have hT : T_min N m = Nat.lcm m (rad N) :=
    T_min_eq_lcm N m hN hm
  have hlcm : 0 < Nat.lcm m (rad N) :=
    Nat.lcm_pos hm hrad
  have hmul : 0 < m * R_param N m := by
    change 0 < T_min N m
    rw [hT]
    exact hlcm
  rcases (mul_pos_iff.mp hmul) with h | h
  · exact h.2
  · omega

end GeneralDivisorTheorem
