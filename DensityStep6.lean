import GeneralDivisorTheorem

namespace GeneralDivisorTheorem

/-- Multiplication by m permutes the residues modulo R. -/
def mulPermutation (N m : Nat)
    (hN : 0 < N) (hm : 0 < m) :
    ZMod (R_param N m) ≃ ZMod (R_param N m) :=
  MulAction.toPerm
    (ZMod.unitOfCoprime m (coprime_m_R N m hN hm))

end GeneralDivisorTheorem
