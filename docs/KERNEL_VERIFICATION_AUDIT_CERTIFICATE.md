# Lean 4 Kernel Verification Audit Certificate (v2.0 — Zero Axioms, Zero `sorry`)

**Repository:** [`pCwOrM/general-divisor-theorem`](https://github.com/pCwOrM/general-divisor-theorem)
**Milestone Pull Request:** [PR #1 (`Prove exact GDT count per admissible period in Lean 4`)](https://github.com/pCwOrM/general-divisor-theorem/pull/1) by **Dan Hawkley ([@thinkthoughts](https://github.com/thinkthoughts))**
**Merge Commit:** `a5ef2b66871a62ec6c465ed06101ecd827135f88` (Head: `ac6586c`)
**Toolchain:** `leanprover/lean4:v4.21.0` + `mathlib4:v4.21.0`
**Audit Status:** **100% KERNEL-VERIFIED (`39 Theorems & Lemmas`, `0 Project Axioms`, `0 sorry`)**

---

## 1. Executive Summary

Following the integration of [PR #1](https://github.com/pCwOrM/general-divisor-theorem/pull/1) by **Dan Hawkley (`@thinkthoughts`)**, every theorem, specialization, two-way bridge isomorphism, and full-period progression count in the General Divisor Theorem (GDT) formalization is constructively proved and checked by the Lean 4 kernel without a single custom `axiom` or `sorry` placeholder.

| Module | Kernel-Checked Declarations | Custom `axiom` Count | `sorry` / `admit` Count | Standard Foundations (`#print axioms`) |
| :--- | :---: | :---: | :---: | :--- |
| [`GeneralDivisorTheorem.lean`](../GeneralDivisorTheorem.lean) | **16** | `0` | `0` | `[propext, Classical.choice, Quot.sound]` |
| [`VolkanBridge.lean`](../VolkanBridge.lean) | **10** | `0` | `0` | `[propext, Classical.choice, Quot.sound]` |
| [`DensityBridge.lean`](../DensityBridge.lean) | **13** | `0` | `0` | `[propext, Classical.choice, Quot.sound]` |
| **Total Across Repository** | **39** | **`0`** | **`0`** | **Standard Classical Lean 4 Only** |

---

## 2. Module-by-Module Kernel Inventory

### 2.1 [`GeneralDivisorTheorem.lean`](../GeneralDivisorTheorem.lean) (16 Theorems & Lemmas)
1. `instance_m6_C`: $C(6) = 3$
2. `instance_m10_C`: $C(10) = 5/2$
3. `instance_m30_C`: $C(30) = 15/4$
4. `rad_eq_prod_primeFactors`: Equivalence of list-fold radical `rad` and `n.primeFactors.prod id`
5. `T_min_eq_lcm`: $T_{\min}(N, m) = \mathrm{lcm}(m, \mathrm{rad}(N))$
6. `exponent_blindness`: $\gcd(n, N) = 1 \iff \gcd(n, \mathrm{rad}(N)) = 1$
7. `C_factor_prime_product`: $C(d) = \prod_{p \mid d} \frac{p}{p - 1}$ for squarefree $d > 0$
8. `inadmissible_branch_empty`: $\gcd(|a|, d) > 1 \implies \neg S_{\text{indicator}}(N, m, a, n)$
9. `admissible_periodicity`: $S_{\text{indicator}}(N, m, a, n + T_{\min}) \iff S_{\text{indicator}}(N, m, a, n)$
10. `specialization_divides`: Theorem 2 ($m \mid N \implies d = \mathrm{rad}(m)$)
11. `rad_mul_of_coprime`:Multiplicativity of `rad` on coprime arguments
12. `d_param_unitary`: $d = \mathrm{rad}(m)$ when $m \mid N$ and $\gcd(m, N/m) = 1$
13. `specialization_unitary`: Theorem 1' ($R = \mathrm{rad}(N/m)$ and $T_{\min} = m \cdot \mathrm{rad}(N/m)$)
14. `rad_eq_self_of_squarefree`: Squarefree invariance $\mathrm{rad}(n) = n$
15. `squarefree_of_dvd_of_squarefree`: Divisor inheritance of squarefreeness
16. `specialization_primorial`: Theorem 1 ($d = m,\ R = N/m,\ T_{\min} = N$)

### 2.2 [`VolkanBridge.lean`](../VolkanBridge.lean) (10 Theorems & Lemmas)
1. `bridge_rad_eq`: `rad n = dan_radN n`
2. `bridge_d_eq`: `d_param N m = dan_d N m`
3. `bridge_R_eq`: `R_param N m = dan_R N m`
4. `bridge_Tmin_eq`: `T_min N m = dan_Tmin N m`
5. `bridge_C_eq`: `C_factor d = dan_correctionFactor d`
6. `bridge_indicator_eq`: `S_indicator N m a n ↔ dan_Good N m a n`
7. `bridge_inadmissible_empty`: Two-way inadmissible branch discharge
8. `bridge_admissible_periodic`: Two-way minimal periodicity discharge
9. `benchmark_3_3_i_Tmin_lt_N`: Distinguishing benchmark $N=18, m=2 \implies T_{\min} = 6 < 18$
10. `benchmark_3_3_ii_sharp_admissibility`: Sharp admissibility $N=5, m=6, a=2 \implies d=1,\ \text{Admissible},\ C(d)=1$

### 2.3 [`DensityBridge.lean`](../DensityBridge.lean) (13 Theorems & Lemmas)
1. `indicator_factorization`: Under $n \equiv a \pmod m$ and $\gcd(|a|, d) = 1$, $\gcd(n, N) = 1 \iff \gcd(n, R) = 1$
2. `residue3_eq_mod`: Canonical progression offset $r = \mathrm{toNat}(a \bmod m) = n \bmod m$
3. `progression_surjective`: Bijection between $[0, T_{\min})$ congruence solutions and $r + m k$ for $0 \le k < R$
4. `R_param_pos`: Strict positivity $0 < R(N, m)$
5. `coprime_m_R`: Disjoint prime support coprimality $\gcd(m, R) = 1$
6. `coprime_zmod_card`: $\mathrm{card}\{x \in \mathbb{Z}/R\mathbb{Z} : \gcd(x.\text{val}, R) = 1\} = \varphi(R)$
7. `affine_coprime_count`: Affine unit permutation invariance `affinePermutation8` over $\mathbb{Z}/R\mathbb{Z}$
8. `progression_modEq`: Congruence preservation $(r + m k) \equiv a \pmod m$
9. `progression_bounded`: Period bound $k < R \implies r + m k < T_{\min}$
10. `progression_indicator_iff`: Reduction of `S_indicator` along the progression to `Nat.Coprime (r + m * k) R`
11. `progression_div`: Exact index recovery $(r + m k) / m = k$
12. `countOnePeriod_eq_progression`: Cardinality bijection `countOnePeriod N m a` to progression coprime filter
13. `coprime_mod_iff` & `progression_totient` & `gdt_count_per_period`:
    $$\text{countOnePeriod}(N, m, a) = \varphi(R(N, m))$$
