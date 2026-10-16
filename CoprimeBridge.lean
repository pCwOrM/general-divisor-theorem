import GeneralDivisorTheorem

namespace GeneralDivisorTheorem

/-- Compatibility bridge to the kernel-checked core coprimality theorem. -/
theorem coprime_m_R_bridge (N m : Nat)
    (hN : 0 < N) (hm : 0 < m) :
    Nat.Coprime m (R_param N m) := by
  exact coprime_m_R N m hN hm

end GeneralDivisorTheorem
