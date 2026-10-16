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


/-- Multiplication by m followed by translation by r. -/
def affinePermutation8 (N m r : Nat)
    (hN : 0 < N) (hm : 0 < m) :
    ZMod (R_param N m) ≃ ZMod (R_param N m) :=
  (MulAction.toPerm
    (ZMod.unitOfCoprime m (coprime_m_R N m hN hm))).trans
    (Equiv.addRight (r : ZMod (R_param N m)))

/-- Exactly totient(R) inputs map to residues coprime to R. -/
theorem affine_coprime_count (N m r : Nat)
    (hN : 0 < N) (hm : 0 < m)
    [NeZero (R_param N m)] :
    (Finset.univ.filter (fun k : ZMod (R_param N m) =>
      Nat.Coprime
        (affinePermutation8 N m r hN hm k).val
        (R_param N m))).card =
      Nat.totient (R_param N m) := by
  let e := affinePermutation8 N m r hN hm
  have hcard :
      (Finset.univ.filter (fun k : ZMod (R_param N m) =>
        Nat.Coprime (e k).val (R_param N m))).card =
      (Finset.univ.filter (fun x : ZMod (R_param N m) =>
        Nat.Coprime x.val (R_param N m))).card := by
    exact Finset.card_bij
      (fun k _ => e k)
      (by intro k hk; simpa using hk)
      (by intro k₁ hk₁ k₂ hk₂ h; exact e.injective h)
      (by
        intro x hx
        refine ⟨e.symm x, ?_, ?_⟩
        · simpa using hx
        · simp)
  rw [hcard]
  exact coprime_zmod_card (R_param N m)

end GeneralDivisorTheorem
