import GeneralDivisorTheorem

namespace GeneralDivisorTheorem

/-- Multiplication by m followed by translation by r. -/
def affinePermutation (N m r : Nat)
    (hN : 0 < N) (hm : 0 < m) :
    ZMod (R_param N m) ≃ ZMod (R_param N m) :=
  (MulAction.toPerm
    (ZMod.unitOfCoprime m (coprime_m_R N m hN hm))).trans
    (Equiv.addRight (r : ZMod (R_param N m)))

/-- The permutation computes r + m*k modulo R. -/
theorem affinePermutation_apply (N m r k : Nat)
    (hN : 0 < N) (hm : 0 < m) :
    affinePermutation N m r hN hm (k : ZMod (R_param N m)) =
      (r + m * k : ZMod (R_param N m)) := by
  simp [affinePermutation, Equiv.addRight,
    MulAction.toPerm_apply, Units.smul_def,
    ZMod.coe_unitOfCoprime, add_comm]

end GeneralDivisorTheorem
