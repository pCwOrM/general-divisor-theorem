import GeneralDivisorTheorem

namespace GeneralDivisorTheorem

/-- Coprime residues modulo n are counted by Euler's totient. -/
theorem coprime_zmod_card (n : Nat) [NeZero n] :
    (Finset.univ.filter (fun x : ZMod n =>
      Nat.Coprime x.val n)).card = Nat.totient n := by
  cases n with
  | zero =>
      exact (NeZero.ne 0 rfl).elim
  | succ n =>
      change
        (Finset.univ.filter (fun x : Fin (n + 1) =>
          Nat.Coprime x.val (n + 1))).card =
        Nat.totient (n + 1)
      rw [Nat.totient_eq_card_coprime]
      apply Finset.card_bij (fun x _ => x.val)
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨x.isLt, hx.symm⟩
      · intro x hx y hy h
        exact Fin.ext h
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_range] at ha
        refine ⟨⟨a, ha.1⟩, ?_, rfl⟩
        simpa [Nat.coprime_comm] using ha.2

end GeneralDivisorTheorem
