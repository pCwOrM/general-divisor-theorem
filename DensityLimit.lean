import DensityCount
import Mathlib

namespace GeneralDivisorTheorem

/-- The number of admissible integers below X is at most X. -/
theorem countBelow_le
    (N m : Nat) (a : Int) (X : Nat) :
    countBelow N m a X ≤ X := by
  classical
  unfold countBelow
  simpa using
    Finset.card_filter_le
      (Finset.range X)
      (fun n => S_indicator N m a n)

/-- Every natural number splits into complete T_min blocks
    plus its canonical remainder. -/
theorem div_mul_T_min_add_mod
    (N m X : Nat) :
    (X / T_min N m) * T_min N m +
        X % T_min N m = X := by
  simpa [Nat.mul_comm] using
    Nat.div_add_mod X (T_min N m)

/-- Exact GDT count expressed using the canonical quotient
    and remainder modulo T_min. -/
theorem countBelow_div_mod
    (N m : Nat) (a : Int) (X : Nat)
    (hN : 0 < N) (hm : 0 < m)
    (h_adm : Nat.gcd a.natAbs (d_param N m) = 1) :
    countBelow N m a X =
      (X / T_min N m) * Nat.totient (R_param N m) +
        countBelow N m a (X % T_min N m) := by
  have hdecomp :
      (X / T_min N m) * T_min N m +
          X % T_min N m = X :=
    div_mul_T_min_add_mod N m X

  calc
    countBelow N m a X =
        countBelow N m a
          ((X / T_min N m) * T_min N m +
            X % T_min N m) := by
      rw [hdecomp]
    _ =
        (X / T_min N m) * Nat.totient (R_param N m) +
          countBelow N m a (X % T_min N m) := by
      exact countBelow_mul_T_min_add
        N m a
        (X / T_min N m)
        (X % T_min N m)
        hN hm h_adm

/-- The remainder contribution is uniformly bounded by T_min. -/
theorem countBelow_mod_lt_T_min
    (N m : Nat) (a : Int) (X : Nat)
    (hN : 0 < N) (hm : 0 < m) :
    countBelow N m a (X % T_min N m) <
      T_min N m := by
  have hT : 0 < T_min N m := by
    unfold T_min
    exact Nat.mul_pos hm (R_param_pos N m hN hm)

  exact lt_of_le_of_lt
    (countBelow_le N m a (X % T_min N m))
    (Nat.mod_lt X hT)


/-- After clearing the denominator T_min, the counting error is uniformly
    bounded by T_min^2. -/
theorem density_error_bound
    (N m : Nat) (a : Int) (X : Nat)
    (hN : 0 < N) (hm : 0 < m)
    (h_adm : Nat.gcd a.natAbs (d_param N m) = 1) :
    abs (
      (T_min N m : ℝ) * (countBelow N m a X : ℝ) -
      (Nat.totient (R_param N m) : ℝ) * X
    ) ≤ (T_min N m : ℝ) ^ 2 := by
  let T := T_min N m
  let phi := Nat.totient (R_param N m)
  let q := X / T
  let r := X % T
  let c := countBelow N m a r

  have hT : 0 < T := by
    unfold T
    unfold T_min
    exact Nat.mul_pos hm (R_param_pos N m hN hm)

  have hr : r < T := by
    exact Nat.mod_lt X hT

  have hc : c ≤ r := by
    exact countBelow_le N m a r

  have hphiR :
      Nat.totient (R_param N m) ≤ R_param N m :=
    Nat.totient_le _

  have hRleT : R_param N m ≤ T := by
    unfold T T_min
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm)
    nlinarith

  have hphi : phi ≤ T := by
    unfold phi
    exact le_trans hphiR hRleT

  have hcount :
      countBelow N m a X = q * phi + c := by
    dsimp [q, phi, c, r, T]
    exact countBelow_div_mod N m a X hN hm h_adm

  have hX :
      q * T + r = X := by
    unfold q r
    exact div_mul_T_min_add_mod N m X

  have hrle : r ≤ T := Nat.le_of_lt hr
  have hcle : c ≤ T := le_trans hc hrle

  have hnonneg1 :
      0 ≤ (T : ℝ) * (c : ℝ) := by positivity

  have hnonneg2 :
      0 ≤ (phi : ℝ) * (r : ℝ) := by positivity

  have hcR : (c : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast hcle

  have hTnonnegR : (0 : ℝ) ≤ (T : ℝ) := by
    positivity

  have hupper1 :
      (T : ℝ) * (c : ℝ) ≤ (T : ℝ) ^ 2 := by
    calc
      (T : ℝ) * (c : ℝ) ≤ (T : ℝ) * (T : ℝ) :=
        mul_le_mul_of_nonneg_left hcR hTnonnegR
      _ = (T : ℝ) ^ 2 := by ring

  have hupper2 :
      (phi : ℝ) * (r : ℝ) ≤ (T : ℝ) ^ 2 := by
    have hphi' : (phi : ℝ) ≤ T := by exact_mod_cast hphi
    have hr' : (r : ℝ) ≤ T := by exact_mod_cast hrle
    nlinarith

  rw [hcount, ← hX]
  push_cast
  ring_nf

  rw [abs_le]
  constructor <;> nlinarith



/-- Natural density of the admissible set. -/
theorem density_limit
    (N m : Nat) (a : Int)
    (hN : 0 < N) (hm : 0 < m)
    (h_adm : Nat.gcd a.natAbs (d_param N m) = 1) :
    Filter.Tendsto
      (fun X : Nat =>
        (countBelow N m a X : ℝ) / X)
      Filter.atTop
      (nhds (
        (Nat.totient (R_param N m) : ℝ) /
          T_min N m)) := by
  let T := T_min N m
  let phi := Nat.totient (R_param N m)

  have hT : 0 < T := by
    unfold T T_min
    exact Nat.mul_pos hm (R_param_pos N m hN hm)

  have hTreal : (0 : ℝ) < (T : ℝ) := by
    exact_mod_cast hT

  have hinv :
      Filter.Tendsto
        (fun X : Nat => ((X : ℝ))⁻¹)
        Filter.atTop
        (nhds 0) := by
    exact tendsto_inv_atTop_zero.comp
      tendsto_natCast_atTop_atTop

  have hmajor :
      Filter.Tendsto
        (fun X : Nat => (T : ℝ) * ((X : ℝ)⁻¹))
        Filter.atTop
        (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul hinv)

  have hpos :
      ∀ᶠ X : Nat in Filter.atTop, 0 < X := by
    exact Filter.eventually_atTop.2
      ⟨1, by
        intro X hX
        omega⟩

  have hbound :
      ∀ᶠ X : Nat in Filter.atTop,
        abs (
          (countBelow N m a X : ℝ) / X -
          (phi : ℝ) / T
        ) ≤
          (T : ℝ) * ((X : ℝ)⁻¹) := by
    filter_upwards [hpos] with X hX
    have hXreal : (0 : ℝ) < (X : ℝ) := by
      exact_mod_cast hX

    have herr :=
      density_error_bound N m a X hN hm h_adm

    have hden :
        (0 : ℝ) < (T : ℝ) * (X : ℝ) :=
      mul_pos hTreal hXreal

    have hfrac :
        (countBelow N m a X : ℝ) / X -
          (phi : ℝ) / T =
        ((T : ℝ) * (countBelow N m a X : ℝ) -
          (phi : ℝ) * X) /
          ((T : ℝ) * X) := by
      field_simp [ne_of_gt hTreal, ne_of_gt hXreal]
      <;> ring

    have heq :
        abs (
          (countBelow N m a X : ℝ) / X -
          (phi : ℝ) / T
        ) =
          abs (
            (T : ℝ) * (countBelow N m a X : ℝ) -
            (phi : ℝ) * X
          ) /
          ((T : ℝ) * X) := by
      rw [hfrac, abs_div, abs_of_pos hden]

    rw [heq]

    calc
      abs (
          (T : ℝ) * (countBelow N m a X : ℝ) -
          (phi : ℝ) * X
        ) /
          ((T : ℝ) * X)
          ≤
        (T : ℝ) ^ 2 /
          ((T : ℝ) * X) := by
            exact div_le_div_of_nonneg_right
              (by
                simpa [T, phi] using herr)
              (le_of_lt hden)
      _ = (T : ℝ) * ((X : ℝ)⁻¹) := by
            field_simp [ne_of_gt hTreal, ne_of_gt hXreal]
            ring

  have habs :
      Filter.Tendsto
        (fun X : Nat =>
          abs (
            (countBelow N m a X : ℝ) / X -
            (phi : ℝ) / T))
        Filter.atTop
        (nhds 0) := by
    exact squeeze_zero'
      (Filter.Eventually.of_forall
        (fun X => abs_nonneg _))
      hbound
      hmajor

  have hsub :
      Filter.Tendsto
        (fun X : Nat =>
          (countBelow N m a X : ℝ) / X -
          (phi : ℝ) / T)
        Filter.atTop
        (nhds 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero
      (fun X : Nat =>
        (countBelow N m a X : ℝ) / X -
        (phi : ℝ) / T)).2
    simpa only [Function.comp_apply] using habs

  have hadd :=
    hsub.add
      (tendsto_const_nhds :
        Filter.Tendsto
          (fun _ : Nat => (phi : ℝ) / T)
          Filter.atTop
          (nhds ((phi : ℝ) / T)))

  simpa [T, phi] using hadd


end GeneralDivisorTheorem
