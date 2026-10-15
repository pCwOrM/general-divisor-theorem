import GeneralDivisorTheorem

namespace GeneralDivisorTheorem

-- Source: DensityStep3.lean
def residue3 (a : Int) (m : Nat) : Nat :=
  (a % (m : Int)).toNat

/-- Congruent integers have the same canonical natural remainder. -/
private theorem residue3_eq_mod (a : Int) (m n : Nat)
    (hm : 0 < m)
    (hc : (n : Int) ≡ a [ZMOD (m : Int)]) :
    n % m = residue3 a m := by
  unfold residue3
  have hmod :
      (n : Int) % (m : Int) = a % (m : Int) := by
    exact hc
  have hn :
      ((n : Int) % (m : Int)).toNat = n % m := by
    omega
  rw [← hn, hmod]

/-- Every congruent n in the period has a progression index k < R. -/
theorem progression_surjective (N m n : Nat) (a : Int)
    (hm : 0 < m)
    (hn : n < T_min N m)
    (hc : (n : Int) ≡ a [ZMOD (m : Int)]) :
    ∃ k : Nat,
      k < R_param N m ∧
      n = residue3 a m + m * k := by
  refine ⟨n / m, ?_, ?_⟩
  · unfold T_min at hn
    exact (Nat.div_lt_iff_lt_mul hm).2 (by
      simpa [Nat.mul_comm] using hn)
  · have hr := residue3_eq_mod a m n hm hc
    have hdecomp := Nat.mod_add_div n m
    omega

-- Source: DensityStep4.lean
/-- The arithmetic progression has distinct entries. -/
theorem progression_injective (r m : Nat)
    (hm : 0 < m) :
    Function.Injective (fun k : Nat => r + m * k) := by
  intro k₁ k₂ h
  have hmul : m * k₁ = m * k₂ :=
    Nat.add_left_cancel h
  exact Nat.eq_of_mul_eq_mul_left hm hmul

-- Source: DensityStep7.lean
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

-- Source: DensityStep8.lean
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

-- Source: DensityBridge.lean
/-- Number of admissible integers in the first proposed period. -/
noncomputable def countOnePeriod (N m : Nat) (a : Int) : Nat := by
  classical
  exact ((Finset.range (T_min N m)).filter
    (fun n => S_indicator N m a n)).card


/-- Every progression entry satisfies the prescribed congruence. -/
theorem progression_modEq (a : Int) (m k : Nat)
    (hm : 0 < m) :
    ((residue3 a m + m * k : Nat) : Int) ≡ a [ZMOD (m : Int)] := by
  have hr : residue3 a m < m := by
    unfold residue3
    have hnonneg : 0 ≤ a % (m : Int) :=
      Int.emod_nonneg _ (by omega)
    have hlt : a % (m : Int) < (m : Int) :=
      Int.emod_lt_of_pos _ (by omega)
    omega
  change
    (((residue3 a m + m * k : Nat) : Int) % (m : Int)) =
      a % (m : Int)
  have hcast :
      ((residue3 a m : Nat) : Int) = a % (m : Int) := by
    unfold residue3
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  rw [Nat.cast_add, Nat.cast_mul, Int.add_mul_emod_self_left]
  have hr0 : (0 : Int) ≤ (residue3 a m : Int) := by omega
  have hrm : (residue3 a m : Int) < (m : Int) := by exact_mod_cast hr
  rw [Int.emod_eq_of_lt hr0 hrm]
  exact hcast


/-- A progression index below R produces an integer below T_min. -/
theorem progression_bounded (N m k : Nat) (a : Int)
    (hm : 0 < m)
    (hk : k < R_param N m) :
    residue3 a m + m * k < T_min N m := by
  have hr : residue3 a m < m := by
    unfold residue3
    have hnonneg : 0 ≤ a % (m : Int) :=
      Int.emod_nonneg _ (by omega)
    have hlt : a % (m : Int) < (m : Int) :=
      Int.emod_lt_of_pos _ (by omega)
    omega
  unfold T_min
  have hstep : k + 1 ≤ R_param N m := Nat.succ_le_of_lt hk
  have hmul : m * (k + 1) ≤ m * R_param N m :=
    Nat.mul_le_mul_left m hstep
  have hexpand : m * (k + 1) = m * k + m := by
    simp [Nat.mul_add]
  omega


/-- On the prescribed progression, the GDT indicator reduces to
    coprimality with R. -/
theorem progression_indicator_iff (N m k : Nat) (a : Int)
    (hN : 0 < N) (hm : 0 < m)
    (h_adm : Nat.gcd a.natAbs (d_param N m) = 1) :
    S_indicator N m a (residue3 a m + m * k) ↔
      Nat.Coprime (residue3 a m + m * k) (R_param N m) := by
  unfold S_indicator
  have hc := progression_modEq a m k hm
  constructor
  · intro h
    exact (indicator_factorization N m a
      (residue3 a m + m * k) h_adm hc).mp h.2
  · intro h
    exact ⟨hc,
      (indicator_factorization N m a
        (residue3 a m + m * k) h_adm hc).mpr h⟩


/-- Recover the progression index by division by m. -/
theorem progression_div (a : Int) (m k : Nat)
    (hm : 0 < m) :
    (residue3 a m + m * k) / m = k := by
  have hr : residue3 a m < m := by
    unfold residue3
    have hnonneg : 0 ≤ a % (m : Int) :=
      Int.emod_nonneg _ (by omega)
    have hlt : a % (m : Int) < (m : Int) :=
      Int.emod_lt_of_pos _ (by omega)
    omega
  rw [Nat.add_mul_div_left _ _ hm]
  simp [Nat.div_eq_of_lt hr]

/-- The indicator count equals the coprime progression count. -/
theorem countOnePeriod_eq_progression (N m : Nat) (a : Int)
    (hN : 0 < N) (hm : 0 < m)
    (h_adm : Nat.gcd a.natAbs (d_param N m) = 1) :
    countOnePeriod N m a =
      ((Finset.range (R_param N m)).filter
        (fun k => Nat.Coprime
          (residue3 a m + m * k) (R_param N m))).card := by
  classical
  unfold countOnePeriod
  apply Finset.card_bij (fun n _ => n / m)
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
    obtain ⟨k, hk, heq⟩ :=
      progression_surjective N m n a hm hn.1 hn.2.1
    have hdiv : n / m = k := by
      rw [heq]
      exact progression_div a m k hm
    rw [hdiv]
    exact ⟨hk,
      (progression_indicator_iff N m k a hN hm h_adm).mp
        (heq ▸ hn.2)⟩
  · intro n₁ hn₁ n₂ hn₂ h
    simp only [Finset.mem_filter, Finset.mem_range] at hn₁ hn₂
    have hmod₁ : n₁ % m = residue3 a m :=
      residue3_eq_mod a m n₁ hm hn₁.2.1
    have hmod₂ : n₂ % m = residue3 a m :=
      residue3_eq_mod a m n₂ hm hn₂.2.1
    have h₁ := Nat.mod_add_div n₁ m
    have h₂ := Nat.mod_add_div n₂ m
    rw [hmod₁] at h₁
    rw [hmod₂] at h₂
    rw [h] at h₁
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    refine ⟨residue3 a m + m * k, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨progression_bounded N m k a hm hk.1,
        (progression_indicator_iff N m k a hN hm h_adm).mpr hk.2⟩
    · exact progression_div a m k hm


/-- Coprimality depends only on the residue modulo R. -/
theorem coprime_mod_iff (n R : Nat) (hR : 0 < R) :
    Nat.Coprime n R ↔ Nat.Coprime (n % R) R := by
  simp only [Nat.Coprime]
  rw [Nat.gcd_comm n R]
  rw [Nat.gcd_rec R n]


/-- The progression contains exactly totient(R) coprime entries. -/
theorem progression_totient (N m : Nat) (a : Int)
    (hN : 0 < N) (hm : 0 < m) :
    ((Finset.range (R_param N m)).filter
      (fun k => Nat.Coprime
        (residue3 a m + m * k) (R_param N m))).card =
      Nat.totient (R_param N m) := by
  classical
  let R := R_param N m
  let r := residue3 a m
  have hR : 0 < R := R_param_pos N m hN hm
  letI : NeZero R := ⟨Nat.ne_of_gt hR⟩
  have hcard :
      ((Finset.range R).filter
        (fun k => Nat.Coprime (r + m * k) R)).card =
      (Finset.univ.filter (fun x : ZMod R =>
        Nat.Coprime
          (affinePermutation8 N m r hN hm x).val R)).card := by
    apply Finset.card_bij
      (fun (k : Nat) (_ : k ∈
        (Finset.range R).filter
          (fun j => Nat.Coprime (r + m * j) R)) =>
        (k : ZMod R))
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hval :
          ((r + m * k : Nat) : ZMod R).val =
            (r + m * k) % R := ZMod.val_natCast R _
      have haff :
          affinePermutation8 N m r hN hm (k : ZMod R) =
            (r + m * k : ZMod R) := by
        simp [affinePermutation8, Equiv.addRight,
          MulAction.toPerm_apply, Units.smul_def,
          ZMod.coe_unitOfCoprime, add_comm]
      rw [haff]
      norm_cast
      rw [ZMod.val_natCast]
      exact (coprime_mod_iff (r + m * k) R hR).mp hk.2
    · intro k₁ hk₁ k₂ hk₂ heq
      simp only [Finset.mem_filter, Finset.mem_range] at hk₁ hk₂
      have hval := congrArg ZMod.val heq
      simp only [ZMod.val_natCast] at hval
      have hmod₁ : k₁ % R = k₁ := Nat.mod_eq_of_lt hk₁.1
      have hmod₂ : k₂ % R = k₂ := Nat.mod_eq_of_lt hk₂.1
      rw [hmod₁, hmod₂] at hval
      exact hval
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      refine ⟨x.val, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · exact ZMod.val_lt x
        · have haff :
              affinePermutation8 N m r hN hm x =
                (r + m * x.val : ZMod R) := by
            rw [← ZMod.natCast_zmod_val x]
            simp [affinePermutation8, Equiv.addRight,
              MulAction.toPerm_apply, Units.smul_def,
              ZMod.coe_unitOfCoprime, add_comm]
          rw [haff] at hx
          norm_cast at hx
          rw [ZMod.val_natCast] at hx
          exact (coprime_mod_iff (r + m * x.val) R hR).mpr hx
      · exact ZMod.natCast_zmod_val x
  rw [hcard]
  exact affine_coprime_count N m r hN hm

/-- Exact GDT count per period. -/
theorem gdt_count_per_period (N m : Nat) (a : Int)
    (hN : 0 < N) (hm : 0 < m)
    (h_adm : Nat.gcd a.natAbs (d_param N m) = 1) :
    countOnePeriod N m a = Nat.totient (R_param N m) := by
  rw [countOnePeriod_eq_progression N m a hN hm h_adm]
  exact progression_totient N m a hN hm

end GeneralDivisorTheorem
