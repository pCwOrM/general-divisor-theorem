import GeneralDivisorTheorem

namespace GeneralDivisorTheorem

/-- The modulus m is a unit modulo the residual radical R. -/
def modulusUnit (N m : Nat)
    (hN : 0 < N) (hm : 0 < m) :
    (ZMod (R_param N m))ˣ :=
  ZMod.unitOfCoprime m (coprime_m_R N m hN hm)

/-- Multiplication by m is invertible modulo R. -/
example (N m : Nat)
    (hN : 0 < N) (hm : 0 < m) :
    IsUnit (m : ZMod (R_param N m)) := by
  exact (ZMod.isUnit_iff_coprime m (R_param N m)).mpr
    (coprime_m_R N m hN hm)

/-- The constructed unit represents m modulo R. -/
example (N m : Nat)
    (hN : 0 < N) (hm : 0 < m) :
    ((modulusUnit N m hN hm : (ZMod (R_param N m))ˣ) :
      ZMod (R_param N m)) = (m : ZMod (R_param N m)) := by
  exact ZMod.coe_unitOfCoprime m (coprime_m_R N m hN hm)

end GeneralDivisorTheorem
