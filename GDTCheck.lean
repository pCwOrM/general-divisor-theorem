import Mathlib

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

private def rad (n : Nat) : Nat :=
  if n = 0 then 0 else n.primeFactors.prod id

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
