import GeneralDivisorTheorem

namespace GeneralDivisorTheorem

/-- Count coprime representatives of ZMod n using Euler's totient. -/
example (n : Nat) [NeZero n] :
    (Finset.univ.filter (fun x : ZMod n =>
      Nat.Coprime x.val n)).card = Nat.totient n := by
  classical
  let e := (ZMod.finEquiv n).toEquiv
  have hcard :
      (Finset.univ.filter (fun x : ZMod n =>
        Nat.Coprime x.val n)).card =
      (Finset.univ.filter (fun k : Fin n =>
        Nat.Coprime k.val n)).card := by
    exact Finset.card_bij
      (fun x _ => e.symm x)
      (by
        intro x hx
        simpa [e, ZMod.finEquiv] using hx)
      (by
        intro x hx y hy h
        exact e.symm.injective h)
      (by
        intro k hk
        refine ⟨e k, ?_, ?_⟩
        · simpa [e, ZMod.finEquiv] using hk
        · simp)
  rw [hcard]
  simpa [Nat.totient_eq_card_coprime, Finset.card_filter] 

end GeneralDivisorTheorem
