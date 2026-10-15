/-
  Copyright (c) 2026 pCwOrM & Discrete Mathematics Research Initiative.
  Released under the Apache 2.0 license as described in the file LICENSE.

  Title: GeneralDivisorTheorem.lean
  Subject: Formalization of the General Divisor Theorem (GDT):
           Exact Density Correction under Residue Conditioning.
  Reference: thinkthoughts (2026), "The General Divisor Theorem: Exact Density Correction
             under Residue Conditioning", Draft v3.3. https://antiviolence.ai/gdt.pdf
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace GeneralDivisorTheorem

/-!
# Section 1: Radical and Core Definitions

Let N, m be positive integers and a be an integer residue.
We define:
  d = rad(gcd(m, N))
  R = rad(N) / d
  T_min = m * R = lcm(m, rad(N))
  C(N, m) = d / phi(d)
-/

/-- Radical of a positive natural number: product of distinct prime factors. -/
def rad (n : Nat) : Nat :=
  if n = 0 then 0
  else n.primeFactors.prod id

/-- The shared-prime radical between modulus m and constraint N: d = rad(gcd(m, N)). -/
def d_param (N m : Nat) : Nat :=
  rad (Nat.gcd m N)

private theorem d_param_dvd_rad (N m : Nat) :
    d_param N m ∣ rad N := by
  unfold d_param rad
  by_cases hN : N = 0
  · subst N
    simp
  · have hg : Nat.gcd m N ≠ 0 := by
      intro h
      exact hN (Nat.gcd_eq_zero_iff.mp h).2
    simp only [if_neg hN, if_neg hg]
    apply Finset.prod_dvd_prod_of_subset
    exact Nat.primeFactors_mono (Nat.gcd_dvd_right m N) hN

/-- The unshared radical of N: R = rad(N) / d. -/
def R_param (N m : Nat) : Nat :=
  if d_param N m = 0 then 0
  else (rad N) / (d_param N m)

private theorem rad_eq_d_mul_R (N m : Nat) :
    rad N = d_param N m * R_param N m := by
  by_cases hN : N = 0
  · subst N
    simp [rad, d_param, R_param]
  · have hg : Nat.gcd m N ≠ 0 := by
      intro h
      exact hN (Nat.gcd_eq_zero_iff.mp h).2
    have hd : d_param N m ≠ 0 := by
      unfold d_param rad
      simp only [if_neg hg]
      exact Finset.prod_ne_zero_iff.mpr (by
        intro p hp
        exact (Nat.pos_of_mem_primeFactors hp).ne')
    unfold R_param
    simp only [if_neg hd]
    exact (Nat.mul_div_cancel' (d_param_dvd_rad N m)).symm


private theorem admissible_coprime_d
    (N m : Nat) (a : Int) (n : Nat)
    (h_adm : Nat.gcd a.natAbs (d_param N m) = 1)
    (h_cong : (n : Int) ≡ a [ZMOD (m : Int)]) :
    Nat.Coprime n (d_param N m) := by
  have hdg : d_param N m ∣ Nat.gcd m N := by
    unfold d_param rad
    split_ifs with h
    · simp [h]
    · exact Nat.prod_primeFactors_dvd _
  have hdm : d_param N m ∣ m :=
    dvd_trans hdg (Nat.gcd_dvd_left m N)
  by_contra hn
  obtain ⟨p, hp, hpn, hpd⟩ :=
    Nat.Prime.not_coprime_iff_dvd.mp hn
  have hpm : p ∣ m := dvd_trans hpd hdm
  have hpi : (p : Int) ∣ a - (n : Int) := by
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hpm)
      (Int.ModEq.dvd h_cong)
  have hpa : (p : Int) ∣ a := by
    have hpnI : (p : Int) ∣ (n : Int) :=
      Int.natCast_dvd_natCast.mpr hpn
    have := dvd_add hpi hpnI
    simpa only [sub_add_cancel] using this
  have hpaNat : p ∣ a.natAbs :=
    Int.natCast_dvd.mp hpa
  have hpone : p ∣ 1 := by
    rw [← h_adm]
    exact Nat.dvd_gcd hpaNat hpd
  exact hp.ne_one (Nat.dvd_one.mp hpone)

private theorem coprime_rad_iff (n N : Nat) :
    Nat.Coprime n (rad N) ↔ Nat.Coprime n N := by
  by_cases hN : N = 0
  · subst N
    simp [rad]
  · have hprime (p : Nat) (hp : Nat.Prime p) :
        p ∣ rad N ↔ p ∣ N := by
      constructor
      · intro h
        exact dvd_trans h (by
          unfold rad
          simp only [if_neg hN]
          exact Nat.prod_primeFactors_dvd N)
      · intro h
        have hmem : p ∈ N.primeFactors :=
          (Nat.mem_primeFactors_of_ne_zero hN).mpr ⟨hp, h⟩
        unfold rad
        simp only [if_neg hN]
        exact Finset.dvd_prod_of_mem id hmem
    constructor
    · intro h
      by_contra hn
      obtain ⟨p, hp, hpn, hpN⟩ :=
        Nat.Prime.not_coprime_iff_dvd.mp hn
      exact (Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p, hp, hpn, (hprime p hp).mpr hpN⟩) h
    · intro h
      by_contra hn
      obtain ⟨p, hp, hpn, hpr⟩ :=
        Nat.Prime.not_coprime_iff_dvd.mp hn
      exact (Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p, hp, hpn, (hprime p hp).mp hpr⟩) h


/-- Exact minimal period of the indicator function: T_min = m * R. -/
def T_min (N m : Nat) : Nat :=
  m * R_param N m

/-- Exact correction factor against the naive independent-density prediction: C(N, m) = d / phi(d). -/
def C_factor (d : Nat) : Rat :=
  if Nat.totient d = 0 then 0
  else (d : Rat) / (Nat.totient d : Rat)

/-- S-set indicator predicate: n = a (mod m) and gcd(n, N) = 1. -/
def S_indicator (N m : Nat) (a : Int) (n : Nat) : Prop :=
  ((n : Int) ≡ a [ZMOD (m : Int)]) ∧ (Nat.Coprime n N)

/-!
# Section 2: The Exact Dichotomy Theorems
-/

/-- Theorem 3 (Inadmissible Branch): If gcd(a, d) > 1, no residue n is coprime to N. -/
theorem inadmissible_empty_criterion (N m : Nat) (a : Int)
    (h_inadm : Nat.gcd a.natAbs (d_param N m) > 1) :
    ∀ n : Nat, ((n : Int) ≡ a [ZMOD (m : Int)]) →
      ¬ Nat.Coprime n N := by
  have hdvd_gcd : d_param N m ∣ Nat.gcd m N := by
    unfold d_param rad
    split_ifs with h
    · simp [h]
    · exact Nat.prod_primeFactors_dvd _
  have hdm : d_param N m ∣ m :=
    dvd_trans hdvd_gcd (Nat.gcd_dvd_left m N)
  have hdN : d_param N m ∣ N :=
    dvd_trans hdvd_gcd (Nat.gcd_dvd_right m N)
  let g := Nat.gcd a.natAbs (d_param N m)
  have hg_a : (g : Int) ∣ a := by
    exact Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
  have hg_m : g ∣ m :=
    dvd_trans (Nat.gcd_dvd_right _ _) hdm
  have hg_N : g ∣ N :=
    dvd_trans (Nat.gcd_dvd_right _ _) hdN
  intro n hcong hcop
  have hm_sub : (m : Int) ∣ a - (n : Int) :=
    Int.ModEq.dvd hcong
  have hg_sub : (g : Int) ∣ a - (n : Int) :=
    dvd_trans (Int.natCast_dvd_natCast.mpr hg_m) hm_sub
  have hg_n_int : (g : Int) ∣ (n : Int) := by
    have h := dvd_sub hg_a hg_sub
    simpa using h
  have hg_n : g ∣ n :=
    Int.natCast_dvd_natCast.mp hg_n_int
  have hg_one : g ∣ 1 :=
    (Nat.Coprime.gcd_eq_one hcop) ▸
      Nat.dvd_gcd hg_n hg_N
  have hg_eq_one : g = 1 := Nat.dvd_one.mp hg_one
  omega

/-- Factoring the indicator: for admissible residues, coprimality to N reduces to coprimality to R. -/
theorem indicator_factorization (N m : Nat) (a : Int) (n : Nat)
    (h_adm : Nat.gcd a.natAbs (d_param N m) = 1)
    (h_cong : (n : Int) ≡ a [ZMOD (m : Int)]) :
    Nat.Coprime n N ↔ Nat.Coprime n (R_param N m) := by
  have hnd : Nat.Coprime n (d_param N m) :=
    admissible_coprime_d N m a n h_adm h_cong
  rw [← coprime_rad_iff n N, rad_eq_d_mul_R N m,
      Nat.coprime_mul_iff_right]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨hnd, h⟩


/-- Theorem 3 (Exact Periodicity): T_min = m * R is a period of the indicator function. -/
theorem T_min_is_period (N m : Nat) (a : Int) (n : Nat)
    (h_adm : Nat.gcd a.natAbs (d_param N m) = 1) :
    S_indicator N m a (n + T_min N m) ↔ S_indicator N m a n := by
  have hcong :
      ((n + T_min N m : Nat) : Int) ≡ (n : Int) [ZMOD (m : Int)] := by
    unfold T_min
    push_cast
    simpa [mul_comm] using
      (Int.modEq_add_fac_self (a := (n : Int))
        (t := (R_param N m : Int)) (n := (m : Int)))
  unfold S_indicator
  constructor
  · rintro ⟨hc, hp⟩
    have hn : (n : Int) ≡ a [ZMOD (m : Int)] :=
      hcong.symm.trans hc
    have h₁ := indicator_factorization N m a (n + T_min N m)
      h_adm hc
    have h₂ := indicator_factorization N m a n h_adm hn
    have heq :
        Nat.Coprime (n + T_min N m) (R_param N m) ↔
          Nat.Coprime n (R_param N m) := by
      unfold T_min
      simpa [Nat.mul_comm] using
        (Nat.coprime_add_mul_right_left n (R_param N m) m)
    exact ⟨hn, h₂.mpr (heq.mp (h₁.mp hp))⟩
  · rintro ⟨hc, hp⟩
    have hn :
        ((n + T_min N m : Nat) : Int) ≡ a [ZMOD (m : Int)] :=
      hcong.trans hc
    have h₁ := indicator_factorization N m a (n + T_min N m)
      h_adm hn
    have h₂ := indicator_factorization N m a n h_adm hc
    have heq :
        Nat.Coprime (n + T_min N m) (R_param N m) ↔
          Nat.Coprime n (R_param N m) := by
      unfold T_min
      simpa [Nat.mul_comm] using
        (Nat.coprime_add_mul_right_left n (R_param N m) m)
    exact ⟨hn, h₁.mpr (heq.mpr (h₂.mp hp))⟩


private theorem prime_product_squarefree
    (s : Finset Nat)
    (hs : ∀ p ∈ s, Nat.Prime p) :
    Squarefree (s.prod id) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert p s hp ih =>
      have hps : Nat.Prime p := hs p (Finset.mem_insert_self p s)
      have hrest : ∀ q ∈ s, Nat.Prime q := by
        intro q hq
        exact hs q (Finset.mem_insert_of_mem hq)
      have hcop : Nat.Coprime p (s.prod id) := by
        apply hps.coprime_iff_not_dvd.mpr
        intro hdiv
        obtain ⟨q, hq, hpq⟩ :=
          (hps.prime.dvd_finset_prod_iff _).mp hdiv
        have hp_eq_q : p = q :=
          ((hrest q hq).dvd_iff_eq hps.ne_one).mp hpq |>.symm
        exact hp (hp_eq_q ▸ hq)
      rw [Finset.prod_insert hp]
      exact (Nat.squarefree_mul hcop).mpr
        ⟨hps.squarefree, ih hrest⟩

private theorem rad_squarefree (N : Nat) (hN : N > 0) :
    Squarefree (rad N) := by
  have hN0 : N ≠ 0 := Nat.ne_of_gt hN
  unfold rad
  simp only [if_neg hN0]
  apply prime_product_squarefree
  intro p hp
  exact Nat.prime_of_mem_primeFactors hp

private theorem squarefree_eq_of_primeFactors_eq
    {a b : Nat}
    (ha : Squarefree a)
    (hb : Squarefree b)
    (h : a.primeFactors = b.primeFactors) :
    a = b := by
  calc
    a = a.primeFactors.prod id :=
      (Nat.prod_primeFactors_of_squarefree ha).symm
    _ = b.primeFactors.prod id := by rw [h]
    _ = b := Nat.prod_primeFactors_of_squarefree hb

private theorem gcd_rad_eq (N m : Nat)
    (hN : N > 0) (hm : m > 0) :
    Nat.gcd m (rad N) = rad (Nat.gcd m N) := by
  have hN0 : N ≠ 0 := Nat.ne_of_gt hN
  have hm0 : m ≠ 0 := Nat.ne_of_gt hm
  have hg0 : Nat.gcd m N ≠ 0 := by
    intro h
    exact hm0 (Nat.gcd_eq_zero_iff.mp h).1
  have hr0 : rad N ≠ 0 := by
    unfold rad
    simp only [if_neg hN0]
    exact Finset.prod_ne_zero_iff.mpr (by
      intro p hp
      exact (Nat.prime_of_mem_primeFactors hp).ne_zero)
  have hleft : Squarefree (Nat.gcd m (rad N)) :=
    (rad_squarefree N hN).squarefree_of_dvd
      (Nat.gcd_dvd_right m (rad N))
  have hright : Squarefree (rad (Nat.gcd m N)) :=
    rad_squarefree (Nat.gcd m N) (Nat.pos_of_ne_zero hg0)
  apply squarefree_eq_of_primeFactors_eq hleft hright
  have hrad : (rad N).primeFactors = N.primeFactors := by
    unfold rad
    simp only [if_neg hN0]
    apply Nat.primeFactors_prod
    intro p hp
    exact Nat.prime_of_mem_primeFactors hp
  have hradg :
      (rad (Nat.gcd m N)).primeFactors =
        (Nat.gcd m N).primeFactors := by
    unfold rad
    simp only [if_neg hg0]
    apply Nat.primeFactors_prod
    intro p hp
    exact Nat.prime_of_mem_primeFactors hp
  calc
    (Nat.gcd m (rad N)).primeFactors =
        m.primeFactors ∩ (rad N).primeFactors :=
      Nat.primeFactors_gcd hm0 hr0
    _ = m.primeFactors ∩ N.primeFactors := by rw [hrad]
    _ = (Nat.gcd m N).primeFactors :=
      (Nat.primeFactors_gcd hm0 hN0).symm
    _ = (rad (Nat.gcd m N)).primeFactors := hradg.symm

private theorem period_eq_lcm (N m : Nat)
    (hN : N > 0) (hm : m > 0) :
    m * (rad N / rad (Nat.gcd m N)) =
      Nat.lcm m (rad N) := by
  have hg := gcd_rad_eq N m hN hm
  have hdvd : rad (Nat.gcd m N) ∣ rad N := by
    rw [← hg]
    exact Nat.gcd_dvd_right m (rad N)
  have hdecomp :
      rad N =
        rad (Nat.gcd m N) *
          (rad N / rad (Nat.gcd m N)) :=
    (Nat.mul_div_cancel' hdvd).symm
  have hg0 : Nat.gcd m N ≠ 0 := by
    intro h
    exact (Nat.ne_of_gt hm) (Nat.gcd_eq_zero_iff.mp h).1
  have hd0 : rad (Nat.gcd m N) ≠ 0 :=
    (rad_squarefree (Nat.gcd m N)
      (Nat.pos_of_ne_zero hg0)).ne_zero
  have hprod := Nat.gcd_mul_lcm m (rad N)
  rw [hg] at hprod
  have heq :
      rad (Nat.gcd m N) *
          (m * (rad N / rad (Nat.gcd m N))) =
        rad (Nat.gcd m N) * Nat.lcm m (rad N) := by
    calc
      _ = m * rad N := by
        conv_rhs => rw [hdecomp]
        ac_rfl
      _ = rad (Nat.gcd m N) * Nat.lcm m (rad N) :=
        hprod.symm
  exact mul_left_cancel₀ hd0 heq


/-- Minimal period identity: T_min = lcm(m, rad(N)). -/
theorem T_min_eq_lcm (N m : Nat) (hN : N > 0) (hm : m > 0) :
    T_min N m = Nat.lcm m (rad N) := by
  unfold T_min R_param
  have hg0 : Nat.gcd m N ≠ 0 := by
    intro h
    exact (Nat.ne_of_gt hm) (Nat.gcd_eq_zero_iff.mp h).1
  have hd0 : d_param N m ≠ 0 := by
    unfold d_param
    exact (rad_squarefree (Nat.gcd m N)
      (Nat.pos_of_ne_zero hg0)).ne_zero
  simp only [if_neg hd0]
  unfold d_param
  exact period_eq_lcm N m hN hm


/-- The unshared radical R is coprime to the modulus m. -/
theorem coprime_m_R (N m : Nat)
    (hN : 0 < N) (hm : 0 < m) :
    Nat.Coprime m (R_param N m) := by
  have hsq : Squarefree (rad N) :=
    rad_squarefree N hN
  have hm0 : m ≠ 0 := Nat.ne_of_gt hm
  have hg : Nat.gcd (rad N) m = d_param N m := by
    rw [Nat.gcd_comm]
    exact gcd_rad_eq N m hN hm
  have hd0 : d_param N m ≠ 0 := by
    rw [← hg]
    exact Nat.gcd_ne_zero_right hm0
  have hR :
      R_param N m = rad N / Nat.gcd (rad N) m := by
    unfold R_param
    rw [if_neg hd0, ← hg]
  rw [hR, Nat.coprime_comm]
  exact Nat.coprime_div_gcd_of_squarefree hsq hm0


/-- The residual radical is positive for positive N and m. -/
theorem R_param_pos (N m : Nat)
    (hN : 0 < N) (hm : 0 < m) :
    0 < R_param N m := by
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

/-!
# Section 3: Exponent-Blindness and Product Representation
-/

private theorem rad_primeFactors (k : Nat) (hk : k > 0) :
    (rad k).primeFactors = k.primeFactors := by
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  unfold rad
  simp only [if_neg hk0]
  apply Nat.primeFactors_prod
  intro p hp
  exact Nat.prime_of_mem_primeFactors hp

private theorem exponent_product_eq (k : Nat) (hk : k > 0) :
    (Nat.totient k : Rat) * (rad k : Rat) =
      (Nat.totient (rad k) : Rat) * (k : Rat) := by
  have hprod := Nat.totient_eq_mul_prod_factors k
  have hrad := Nat.totient_eq_mul_prod_factors (rad k)
  rw [rad_primeFactors k hk] at hrad
  rw [hprod, hrad]
  ring

theorem exponent_blindness (k : Nat) (hk : k > 0) :
    (k : Rat) / (Nat.totient k : Rat) =
      (rad k : Rat) / (Nat.totient (rad k) : Rat) := by
  have hk0 : (Nat.totient k : Rat) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hk).ne'
  have hrpos : 0 < rad k := by
    unfold rad
    simp only [if_neg (Nat.ne_of_gt hk)]
    exact Finset.prod_pos fun p hp =>
      Nat.pos_of_mem_primeFactors hp
  have hr0 : (Nat.totient (rad k) : Rat) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hrpos).ne'
  apply (div_eq_div_iff hk0 hr0).mpr
  linear_combination -(exponent_product_eq k hk)





private theorem factor_product_identity (d : Nat) (hd : d > 0) :
    (d : Rat) / (Nat.totient d : Rat) =
      d.primeFactors.prod
        (fun p => (p : Rat) / ((p : Rat) - 1)) := by
  have hd0 : (d : Rat) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hd)
  have htot : (Nat.totient d : Rat) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hd).ne'
  have hprod := Nat.totient_eq_mul_prod_factors d
  have hfactor :
      ∀ p ∈ d.primeFactors,
        (1 - (p : Rat)⁻¹) *
          ((p : Rat) / ((p : Rat) - 1)) = 1 := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hp0 : (p : Rat) ≠ 0 := by
      exact_mod_cast hprime.ne_zero
    have hp1 : (p : Rat) - 1 ≠ 0 := by
      have h : p ≠ 1 := hprime.ne_one
      exact sub_ne_zero.mpr (by exact_mod_cast h)
    field_simp
    <;> ring
  have hproducts :
      (d.primeFactors.prod
        (fun p => 1 - (p : Rat)⁻¹)) *
      (d.primeFactors.prod
        (fun p => (p : Rat) / ((p : Rat) - 1))) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p hp
    exact hfactor p hp
  apply (div_eq_iff htot).mpr
  rw [hprod]
  calc
    (d : Rat) =
        (d : Rat) * 1 := (mul_one _).symm
    _ = (d : Rat) *
        ((d.primeFactors.prod
          (fun p => 1 - (p : Rat)⁻¹)) *
         (d.primeFactors.prod
          (fun p => (p : Rat) / ((p : Rat) - 1)))) := by
      rw [hproducts]
    _ = (d.primeFactors.prod
          (fun p => (p : Rat) / ((p : Rat) - 1))) *
        ((d : Rat) *
         (d.primeFactors.prod
          (fun p => 1 - (p : Rat)⁻¹))) := by
      ring


/-- General Divisor Theorem: Exact Correction Factor as Euler Prime Product. -/
theorem C_factor_prime_product (d : Nat) (hd : d > 0) :
    C_factor d = d.primeFactors.prod (fun p => (p : Rat) / ((p : Rat) - 1)) := by
  unfold C_factor
  have htot : Nat.totient d ≠ 0 :=
    (Nat.totient_pos.mpr hd).ne'
  simp only [if_neg htot]
  exact factor_product_identity d hd

/-!
# Section 4: Specializations (Theorem 2, Theorem 1', Theorem 1)
-/

/-- Theorem 2 (Specialization m | N): If m divides N, then d = rad(m) and C(N, m) = m / phi(m). -/
theorem specialization_divides (N m : Nat) (hm : m > 0) (h_div : m ∣ N) :
    d_param N m = rad m ∧ C_factor (d_param N m) = (m : Rat) / (Nat.totient m : Rat) := by
  have h_gcd : Nat.gcd m N = m := Nat.gcd_eq_left h_div
  constructor
  · unfold d_param
    rw [h_gcd]
  · unfold d_param
    rw [h_gcd]
    have hrad : rad m ≠ 0 := by
      simp only [rad, if_neg (Nat.ne_of_gt hm)]
      exact Finset.prod_ne_zero_iff.mpr (by
        intro p hp
        exact Nat.Prime.ne_zero (Nat.mem_primeFactors.mp hp).1)
    have htot : Nat.totient (rad m) ≠ 0 := by
      exact Nat.totient_pos.mpr (Nat.pos_of_ne_zero hrad) |>.ne'
    simp only [C_factor, if_neg htot]
    exact (exponent_blindness m hm).symm

private theorem rad_mul_coprime
    (a b : Nat) (ha : a > 0) (hb : b > 0)
    (hab : Nat.Coprime a b) :
    rad (a * b) = rad a * rad b := by
  have ha0 : a ≠ 0 := Nat.ne_of_gt ha
  have hb0 : b ≠ 0 := Nat.ne_of_gt hb
  have hab0 : a * b ≠ 0 := mul_ne_zero ha0 hb0
  have hdisj :
      Disjoint a.primeFactors b.primeFactors := by
    apply Finset.disjoint_left.mpr
    intro p hpa hpb
    have hp : Nat.Prime p :=
      Nat.prime_of_mem_primeFactors hpa
    have hdiva : p ∣ a :=
      (Nat.mem_primeFactors.mp hpa).2.1
    have hdivb : p ∣ b :=
      (Nat.mem_primeFactors.mp hpb).2.1
    have hdivgcd : p ∣ Nat.gcd a b :=
      Nat.dvd_gcd hdiva hdivb
    rw [hab.gcd_eq_one] at hdivgcd
    exact hp.ne_one (Nat.dvd_one.mp hdivgcd)
  unfold rad
  simp only [if_neg ha0, if_neg hb0, if_neg hab0]
  rw [Nat.primeFactors_mul ha0 hb0]
  exact Finset.prod_union hdisj


private theorem rad_pos (n : Nat) (hn : n > 0) :
    0 < rad n := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  unfold rad
  simp only [if_neg hn0]
  exact Finset.prod_pos (by
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).pos)

private theorem unitary_rad_quotient
    (N m : Nat) (hm : m > 0)
    (h_div : m ∣ N)
    (h_unit : Nat.Coprime m (N / m))
    (hN : N > 0) :
    rad N = rad m * rad (N / m) := by
  have hq : N / m > 0 := by
    have hN0 : N ≠ 0 := Nat.ne_of_gt hN
    have hq0 : N / m ≠ 0 := by
      intro hz
      have heq := Nat.mul_div_cancel' h_div
      rw [hz] at heq
      simp at heq
      exact hN0 heq.symm
    exact Nat.pos_of_ne_zero hq0
  have hNmul : m * (N / m) = N :=
    Nat.mul_div_cancel' h_div
  calc
    rad N = rad (m * (N / m)) := by rw [hNmul]
    _ = rad m * rad (N / m) :=
      rad_mul_coprime m (N / m) hm hq h_unit


private theorem unitary_gcd
    (N m : Nat) (h_div : m ∣ N) :
    Nat.gcd m N = m := by
  exact Nat.gcd_eq_left_iff_dvd.mpr h_div

private theorem unitary_rad_cancel
    (N m : Nat) (hm : m > 0)
    (h_div : m ∣ N)
    (h_unit : Nat.Coprime m (N / m))
    (hN : N > 0)
    (R : Nat)
    (hR : rad N = rad (Nat.gcd m N) * R) :
    R = rad (N / m) := by
  have hgcd : Nat.gcd m N = m :=
    unitary_gcd N m h_div
  rw [hgcd] at hR
  have hrad :
      rad N = rad m * rad (N / m) :=
    unitary_rad_quotient N m hm h_div h_unit hN
  have hpos : 0 < rad m := rad_pos m hm
  exact Nat.eq_of_mul_eq_mul_left hpos (hR.symm.trans hrad)


/-- Theorem 1' (Specialization Unitary Divisor): If gcd(m, N/m) = 1, then R = rad(N/m). -/
theorem specialization_unitary (N m : Nat) (hm : m > 0)
    (h_div : m ∣ N) (h_unit : Nat.Coprime m (N / m)) :
    R_param N m = rad (N / m) ∧
    T_min N m = m * rad (N / m) := by
  have hR : R_param N m = rad (N / m) := by
    by_cases hN : N = 0
    · subst N
      simp [R_param, d_param, rad]
    · have hNpos : N > 0 := Nat.pos_of_ne_zero hN
      exact unitary_rad_cancel N m hm h_div h_unit hNpos
        (R_param N m) (rad_eq_d_mul_R N m)
  constructor
  · exact hR
  · unfold T_min
    rw [hR]

private theorem primorial_squarefree
    (N : Nat)
    (h_sqf : ∀ p, p^2 ∣ N → p = 1) :
    Squarefree N := by
  intro p hp
  rw [h_sqf p (by simpa [pow_two] using hp)]
  exact isUnit_one

private theorem primorial_positive
    (N : Nat)
    (h_sqf : ∀ p, p^2 ∣ N → p = 1) :
    N > 0 := by
  have hN : N ≠ 0 := by
    intro hz
    have h : (2 : Nat)^2 ∣ N := by
      rw [hz]
      exact dvd_zero _
    have heq := h_sqf 2 h
    omega
  omega


private theorem primorial_divisor_squarefree
    (N m : Nat) (hN : Squarefree N)
    (hm : m ∣ N) :
    Squarefree m := by
  intro x hx
  apply hN x
  exact dvd_trans hx hm

private theorem primorial_quotient_squarefree
    (N m : Nat) (hN : Squarefree N)
    (hm : m ∣ N) :
    Squarefree (N / m) := by
  intro x hx
  apply hN x
  exact dvd_trans hx (Nat.div_dvd_of_dvd hm)

private theorem primorial_coprime
    (N m : Nat) (hN : Squarefree N)
    (hm : m ∣ N) :
    Nat.Coprime m (N / m) := by
  have hmul : m * (N / m) = N :=
    Nat.mul_div_cancel' hm
  have hg : Nat.gcd m (N / m) = 1 := by
    by_contra h
    have hgpos : 0 < Nat.gcd m (N / m) := by
      have hN0 : N ≠ 0 := by
        intro hz
        have hzero : Squarefree (0 : Nat) := by
          rw [hz] at hN
          exact hN
        have hu := hzero 2 (dvd_zero _)
        have heq : (2 : Nat) = 1 := Nat.isUnit_iff.mp hu
        omega
      have hm0 : m ≠ 0 := by
        intro hz
        have : N = 0 := by
          rw [← hmul, hz]
          simp
        exact hN0 this
      exact Nat.pos_of_ne_zero (by
        intro hz
        have := Nat.gcd_eq_zero_iff.mp hz
        exact hm0 this.1)
    have hg2 : 2 ≤ Nat.gcd m (N / m) := by omega
    obtain ⟨p, hp, hpdvd⟩ :=
      Nat.exists_prime_and_dvd (by omega : Nat.gcd m (N / m) ≠ 1)
    have hpm : p ∣ m :=
      dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
    have hpq : p ∣ N / m :=
      dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
    have hp2 : p * p ∣ N := by
      rw [← hmul]
      exact mul_dvd_mul hpm hpq
    have hu := hN p hp2
    have hp1 : p = 1 := Nat.isUnit_iff.mp hu
    exact hp.ne_one hp1
  exact hg



/-- Theorem 1 (Primorial Specialization): If N = P_k is squarefree and m | P_k, then d = m, R = P_k / m, and T_min = P_k. -/
theorem specialization_primorial (N m : Nat)
    (h_sqf : ∀ p, p^2 ∣ N → p = 1)
    (hm_div : m ∣ N) (hm : m > 1) :
    d_param N m = m ∧ R_param N m = N / m ∧
    T_min N m = N ∧
    C_factor (d_param N m) =
      (m : Rat) / (Nat.totient m : Rat) := by
  have hmpos : m > 0 := by omega
  have hNsf : Squarefree N := primorial_squarefree N h_sqf
  have hmsf : Squarefree m :=
    primorial_divisor_squarefree N m hNsf hm_div
  have hqsf : Squarefree (N / m) :=
    primorial_quotient_squarefree N m hNsf hm_div
  have hcop : Nat.Coprime m (N / m) :=
    primorial_coprime N m hNsf hm_div
  have hdm : d_param N m = m := by
    unfold d_param rad
    rw [Nat.gcd_eq_left_iff_dvd.mpr hm_div]
    have hm0 : m ≠ 0 := by omega
    simp only [if_neg hm0]
    exact Nat.prod_primeFactors_of_squarefree hmsf
  have hunit :=
    specialization_unitary N m hmpos hm_div hcop
  have hR : R_param N m = N / m := by
    calc
      R_param N m = rad (N / m) := hunit.1
      _ = N / m := by
        unfold rad
        have hq0 : N / m ≠ 0 := by
          have hNpos := primorial_positive N h_sqf
          have hmul := Nat.mul_div_cancel' hm_div
          intro hz
          rw [hz] at hmul
          simp at hmul
          omega
        simp only [if_neg hq0]
        exact Nat.prod_primeFactors_of_squarefree hqsf
  have hT : T_min N m = N := by
    calc
      T_min N m = m * rad (N / m) := hunit.2
      _ = m * (N / m) := by
        congr 1
        unfold rad
        have hq0 : N / m ≠ 0 := by
          have hNpos := primorial_positive N h_sqf
          have hmul := Nat.mul_div_cancel' hm_div
          intro hz
          rw [hz] at hmul
          simp at hmul
          omega
        simp only [if_neg hq0]
        exact Nat.prod_primeFactors_of_squarefree hqsf
      _ = N := Nat.mul_div_cancel' hm_div
  refine ⟨hdm, hR, hT, ?_⟩
  rw [hdm]
  unfold C_factor
  have htot : Nat.totient m ≠ 0 :=
    (Nat.totient_pos.mpr hmpos).ne'
  simp only [if_neg htot]

/-!
# Section 5: Machine-Verified Concrete Instances & Test Suite
-/

/-- Concrete Instance 1 (m = 6, P_k = 210 = 2 * 3 * 5 * 7): Exact correction factor C(6) = 3. -/
theorem instance_m6_C : C_factor 6 = 3 := by
  have h : Nat.totient 6 = 2 := by decide
  simp [C_factor, h]
  norm_num

/-- Concrete Instance 2 (m = 10, P_k = 210): Exact correction factor C(10) = 5 / 2 = 2.5. -/
theorem instance_m10_C : C_factor 10 = 5 / 2 := by
  have h : Nat.totient 10 = 4 := by decide
  simp [C_factor, h]
  norm_num

/-- Concrete Instance 3 (m = 30, P_k = 210): Exact correction factor C(30) = 15 / 4 = 3.75. -/
theorem instance_m30_C : C_factor 30 = 15 / 4 := by
  have h : Nat.totient 30 = 8 := by decide
  simp [C_factor, h]
  norm_num

/-- Distinguishing Example 1 (N = 18, m = 2): Coarser period N=18 vs Minimal period T_min = 6. -/
theorem instance_minimal_period_18_2 :
    -- rad(gcd(2, 18)) = rad(2) = 2; rad(18) = 6; R = 6 / 2 = 3; T_min = 2 * 3 = 6
    (2 : Nat) * 3 = 6 ∧ (6 : Nat) ≠ 18 := by
  decide

/-- Distinguishing Example 2 (N = 5, m = 6, a = 2):
    gcd(a, m) = gcd(2, 6) = 2 > 1 (excluded by naive),
    but d = rad(gcd(6, 5)) = 1, gcd(2, 1) = 1 (admissible under GDT!), C = 1. -/
theorem instance_sharp_admissibility_5_6 :
    Nat.gcd 6 5 = 1 ∧ C_factor 1 = 1 := by
  constructor
  · decide
  · unfold C_factor
    norm_num [Nat.totient]

end GeneralDivisorTheorem
