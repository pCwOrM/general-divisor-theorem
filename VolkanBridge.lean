/-
  Copyright (c) 2026 Volkan Dağlı, Zerrin Dağlı, Dağhan Dağlı & pCwOrM.
  All rights reserved. Released under the Apache 2.0 license.

  Title: VolkanBridge.lean
  Subject: Two-Way Cross-Validation Bridge between Volkan's Functional GDT API
           and Dan's Prime-Support Reading-Point Specification (gdt-readingpoint).
  References:
    1. Dan Hawkley (thinkthoughts / @Precedent_Vice), "The General Divisor Theorem:
       Exact Density Correction under Residue Conditioning", Draft v3.3 (2026).
    2. GitHub: thinkthoughts/gap-lean4-port-gdt (GDTReadingPoint).
    3. Standalone Formalization: pCwOrM/general-divisor-theorem.
    4. Permanent Zenodo Archive: 10.5281/zenodo.23316070.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Totient
import Mathlib
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.NormNum
import GeneralDivisorTheorem

namespace VolkanBridge

open GeneralDivisorTheorem

/-!
# Section 1: Dan's Prime-Support Specification Interface (GDTReadingPoint)

Following Dan Hawkley's reading point layout in `gdt-readingpoint`:
-/

structure DanParams where
  N : Nat
  m : Nat
  a : Nat
  hN : 0 < N
  hm : 0 < m

namespace DanRepresentation

/-- Dan's `radN`: product of prime divisors of N. -/
def radN (P : DanParams) : Nat :=
  ∏ q ∈ Nat.primeFactors P.N, q

/-- Dan's `d`: product of primes shared by N and m. -/
def d (P : DanParams) : Nat :=
  ∏ q ∈ Nat.primeFactors P.N ∩ Nat.primeFactors P.m, q

/-- Dan's prime support contributing to R: primes dividing N but not m. -/
def Rset (P : DanParams) : Finset Nat :=
  Nat.primeFactors P.N \ Nat.primeFactors P.m

/-- Dan's `R`: radical contribution from primes dividing N but not m. -/
def R (P : DanParams) : Nat :=
  ∏ q ∈ Rset P, q

/-- Dan's minimal period `Tmin = m * R`. -/
def Tmin (P : DanParams) : Nat :=
  P.m * R P

/-- Dan's Euler density correction factor. -/
def correctionFactor (P : DanParams) : Rat :=
  (d P : Rat) / (Nat.totient (d P) : Rat)

/-- Dan's admissibility condition: gcd(a, d) = 1. -/
def Admissible (a d : Nat) : Prop :=
  Nat.Coprime a d

/-- Dan's Good predicate: n ≡ a (mod m) and gcd(n, N) = 1. -/
def Good (P : DanParams) (n : Nat) : Prop :=
  n % P.m = P.a % P.m ∧ Nat.Coprime n P.N

end DanRepresentation

/-!
# Section 2: Canonical Mapping and Parameter Equivalences

We formally map Volkan's functional definitions (`GeneralDivisorTheorem.lean`)
to Dan's prime-support set-theoretic definitions.
-/

open DanRepresentation

/-- Conversion morphism mapping positive natural triples (N, m, a) to DanParams. -/
def toDanParams (N m a : Nat) (hN : 0 < N) (hm : 0 < m) : DanParams :=
  ⟨N, m, a, hN, hm⟩

/--
Theorem (d-Agreement):
Volkan's `d_param N m = rad (gcd m N)` equals Dan's `∏ q ∈ primeFactors N ∩ primeFactors m, q`.
-/
theorem d_param_agrees (P : DanParams) :
    d_param P.N P.m = DanRepresentation.d P := by
  have hm : P.m ≠ 0 := Nat.ne_of_gt P.hm
  have hN : P.N ≠ 0 := Nat.ne_of_gt P.hN
  have hgcd : Nat.gcd P.m P.N ≠ 0 := by
    exact Nat.ne_of_gt (Nat.gcd_pos_of_pos_left P.N P.hm)
  simp only [d_param, rad, if_neg hgcd, DanRepresentation.d]
  rw [Nat.primeFactors_gcd hm hN]
  rw [Finset.inter_comm]
  rfl

/--
Theorem (R-Agreement):
Volkan's `R_param N m = rad N / d_param N m` equals Dan's `∏ q ∈ primeFactors N \ primeFactors m, q`.
-/
theorem R_param_agrees (P : DanParams) :
    R_param P.N P.m = DanRepresentation.R P := by
  let A := Nat.primeFactors P.N
  let B := Nat.primeFactors P.m
  let D := A ∩ B
  let E := A \ B

  have hprod : (∏ p ∈ D, p) * (∏ p ∈ E, p) =
      ∏ p ∈ A, p := by
    exact Finset.prod_inter_mul_prod_diff A B id

  have hd : d_param P.N P.m = ∏ p ∈ D, p := by
    rw [d_param_agrees P]
    rfl

  have hrad : rad P.N = ∏ p ∈ A, p := by
    simp [rad, Nat.ne_of_gt P.hN, A]

  have hDpos : 0 < ∏ p ∈ D, p := by
    apply Finset.prod_pos
    intro p hp
    have hpA : p ∈ A := (Finset.mem_inter.mp hp).1
    exact (Nat.mem_primeFactors.mp hpA).1.pos

  have hquot : (∏ p ∈ A, p) / (∏ p ∈ D, p) =
      ∏ p ∈ E, p := by
    rw [← hprod]
    exact Nat.mul_div_cancel_left _ (hDpos)

  simp only [R_param, hd, hrad, if_neg (Nat.ne_of_gt hDpos)]
  rw [hquot]
  rfl

/--
Theorem (T_min-Agreement):
Volkan's `T_min N m = m * R_param N m` equals Dan's `Tmin P = m * R P`.
-/
theorem T_min_agrees (P : DanParams) :
    T_min P.N P.m = DanRepresentation.Tmin P := by
  unfold T_min DanRepresentation.Tmin
  rw [R_param_agrees P]

/--
Theorem (Correction Factor Agreement):
Volkan's `C_factor d = d / phi(d)` equals Dan's `correctionFactor P`.
-/
theorem C_factor_agrees (P : DanParams) :
    C_factor (d_param P.N P.m) =
      DanRepresentation.correctionFactor P := by
  rw [d_param_agrees P]
  unfold C_factor DanRepresentation.correctionFactor
  split_ifs with h
  · simp [h]
  · rfl

/--
Theorem (Indicator and Good-Set Equivalence):
Volkan's `S_indicator` is logically equivalent to Dan's `Good` predicate.
-/
theorem S_indicator_agrees (P : DanParams) (n : Nat) :
    S_indicator P.N P.m (P.a : Int) n ↔ DanRepresentation.Good P n := by
  unfold S_indicator DanRepresentation.Good
  rw [Int.natCast_modEq_iff]
  rfl

/-- Discharging Theorem 3 Inadmissible Branch via Dan's Empty Theorem -/
theorem bridge_inadmissible_empty (P : DanParams)
    (h_inadm : ¬ DanRepresentation.Admissible P.a (DanRepresentation.d P)) :
    ∀ n : Nat, ¬ DanRepresentation.Good P n := by
  have hgcd : 1 < Nat.gcd P.a (DanRepresentation.d P) := by
    unfold DanRepresentation.Admissible at h_inadm
    have hne : Nat.gcd P.a (DanRepresentation.d P) ≠ 1 := by
      intro h
      exact h_inadm h
    have hdpos : 0 < DanRepresentation.d P := by
      unfold DanRepresentation.d
      apply Finset.prod_pos
      intro p hp
      exact (Nat.mem_primeFactors.mp (Finset.mem_inter.mp hp).1).1.pos
    have hpos : 0 < Nat.gcd P.a (DanRepresentation.d P) :=
      Nat.gcd_pos_of_pos_right P.a hdpos
    omega
  intro n hgood
  have hind : S_indicator P.N P.m (P.a : Int) n :=
    (S_indicator_agrees P n).2 hgood
  have hbad := inadmissible_empty_criterion P.N P.m (P.a : Int)
    (by simpa [d_param_agrees P] using hgcd) n hind.1
  exact hbad hind.2

/-- Discharging Theorem 3 Periodicity via Dan's Translation Theorem -/
theorem bridge_periodic (P : DanParams) (n : Nat) :
    DanRepresentation.Good P (n + DanRepresentation.Tmin P) ↔
      DanRepresentation.Good P n := by
  by_cases h : DanRepresentation.Admissible P.a (DanRepresentation.d P)
  · have hadm : Nat.gcd (Int.natAbs (P.a : Int)) (d_param P.N P.m) = 1 := by
      simpa [DanRepresentation.Admissible, Nat.Coprime,
        d_param_agrees P] using h
    have hperiod := T_min_is_period P.N P.m (P.a : Int) n hadm
    rw [← T_min_agrees P]
    exact (S_indicator_agrees P (n + T_min P.N P.m)).symm.trans
      (hperiod.trans (S_indicator_agrees P n))
  · have hempty := bridge_inadmissible_empty P h
    constructor
    · intro hgood
      exact False.elim (hempty (n + DanRepresentation.Tmin P) hgood)
    · intro hgood
      exact False.elim (hempty n hgood)

/-!
# Section 4: Machine-Verified Distinguishing Benchmarks (kernel-checked)

Both representations agree exactly on the distinguishing benchmark instances
from §3.3 of `gdt.pdf`:
-/

/-- Benchmark 1 (§3.3 i): N = 18, m = 2, a = 1.
    Exact minimal period is 6, strictly less than 18. -/
theorem benchmark_N18_m2_agreement :
    let P : DanParams := ⟨18, 2, 1, by decide, by decide⟩
    T_min 18 2 = 6 ∧
    DanRepresentation.Tmin P = 6 ∧
    C_factor (d_param 18 2) = 2 := by
  let P : DanParams := ⟨18, 2, 1, by decide, by decide⟩

  have hpf18 : Nat.primeFactors 18 = {2, 3} := by
    change Nat.primeFactors (2 * 3^2) = {2, 3}
    rw [Nat.primeFactors_mul]
    · rw [Nat.primeFactors_pow]
      · norm_num
        decide
      · decide
    · decide
    · decide

  have hd : d_param 18 2 = 2 := by
    norm_num [d_param, rad]

  have hT : T_min 18 2 = 6 := by
    norm_num [T_min, R_param, d_param, rad, hpf18]

  have hDanT : DanRepresentation.Tmin P = 6 := by
    rw [← T_min_agrees P]
    exact hT

  change T_min 18 2 = 6 ∧
    DanRepresentation.Tmin P = 6 ∧
    C_factor (d_param 18 2) = 2

  constructor
  · exact hT
  constructor
  · exact hDanT
  · rw [hd]
    have ht : Nat.totient 2 = 1 := by decide
    simp [C_factor, ht]

/-- Benchmark 2 (§3.3 ii): N = 5, m = 6, a = 2.
    Admissible with d = 1, despite gcd(a, m) = 2. -/
theorem benchmark_N5_m6_agreement :
    let P : DanParams := ⟨5, 6, 2, by decide, by decide⟩
    d_param 5 6 = 1 ∧
    DanRepresentation.d P = 1 ∧
    T_min 5 6 = 30 ∧
    DanRepresentation.Tmin P = 30 ∧
    C_factor (d_param 5 6) = 1 := by
  let P : DanParams := ⟨5, 6, 2, by decide, by decide⟩

  have hd : d_param 5 6 = 1 := by
    norm_num [d_param, rad]

  have hDanD : DanRepresentation.d P = 1 := by
    rw [← d_param_agrees P]
    exact hd

  have hT : T_min 5 6 = 30 := by
    norm_num [T_min, R_param, d_param, rad]

  have hDanT : DanRepresentation.Tmin P = 30 := by
    rw [← T_min_agrees P]
    exact hT

  change d_param 5 6 = 1 ∧
    DanRepresentation.d P = 1 ∧
    T_min 5 6 = 30 ∧
    DanRepresentation.Tmin P = 30 ∧
    C_factor (d_param 5 6) = 1

  constructor
  · exact hd
  constructor
  · exact hDanD
  constructor
  · exact hT
  constructor
  · exact hDanT
  · rw [hd]
    have ht : Nat.totient 1 = 1 := by decide
    simp [C_factor, ht]

/-- Canonical Euler Density Correction Instances:
    C(6) = 3, C(10) = 2.5, C(30) = 3.75 -/
theorem benchmark_canonical_C_factors :
    C_factor 6 = 3 ∧
    C_factor 10 = 5 / 2 ∧
    C_factor 30 = 15 / 4 := by
  exact ⟨instance_m6_C, instance_m10_C, instance_m30_C⟩

end VolkanBridge
