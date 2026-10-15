# General Divisor Theorem (GDT): Lean 4 Formalization

[![Lean 4](https://img.shields.io/badge/Lean_4-v4.21.0_(39_Theorems_%7C_0_Axioms_%7C_0_Sorry)-blue.svg)](docs/KERNEL_VERIFICATION_AUDIT_CERTIFICATE.md)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23316070.svg)](https://doi.org/10.5281/zenodo.23316070)
[![License](https://img.shields.io/badge/License-Apache_2.0-green.svg)](LICENSE)
[![Verification](https://img.shields.io/badge/Verification-2287_Checks_PASS-brightgreen.svg)](scripts/verify_gdt.py)
[![VolkanBridge & DensityBridge](https://img.shields.io/badge/VolkanBridge_%26_DensityBridge-Kernel_Verified_(PR_%231)-blueviolet.svg)](https://github.com/pCwOrM/general-divisor-theorem/pull/1)
[![Contributors: @thinkthoughts](https://img.shields.io/badge/Co--Author_%26_Kernel_Architect-Dan_Hawkley_(%40thinkthoughts)-024dad.svg)](CONTRIBUTORS.md)
[![Sister Repo: Niemeier A8^3 Moonshine](https://img.shields.io/badge/Sister%20Repo-Niemeier%20A8%5E3%20Moonshine-024dad.svg)](https://github.com/pCwOrM/niemeier-a8-umbral-moonshine)
[![Sister Repo: WERR Core Monorepo](https://img.shields.io/badge/Sister%20Repo-WERR%20Core%20Monorepo-8b5cf6.svg)](https://github.com/pCwOrM/mandelbrot-fractal-neural-synthesis)
[![Sister Repo: Schönhage Record](https://img.shields.io/badge/Sister%20Repo-Sch%C3%B6nhage%20Record-brightgreen.svg)](https://github.com/pCwOrM/integer-mult-bounds)
[![arXiv:2610.14263](https://img.shields.io/badge/arXiv-2610.14263%20%5Bcs.CC%5D-b31b1b.svg)](https://arxiv.org/abs/2610.14263)
[![arXiv DOI: 10.48550/arXiv.2610.14263](https://img.shields.io/badge/DOI-10.48550%2FarXiv.2610.14263-b31b1b.svg)](https://doi.org/10.48550/arXiv.2610.14263)
[![CrocSwap PR #226: Incorporated](https://img.shields.io/badge/CrocSwap%20Main-PR%20%23226%20Incorporated%20(50d76881)-brightgreen.svg)](https://github.com/CrocSwap/integer-mult-bounds/blob/50d768818f579d4e165b4c257c6ee25bca300802/docs/research/community-reconciliation-next100-review.md)
[![CrocSwap Contributors: @pCwOrM](https://img.shields.io/badge/CrocSwap%20Contributors-Volkan%20Dagli%20(%40pCwOrM)-024dad.svg)](https://github.com/CrocSwap/integer-mult-bounds/blob/50d768818f579d4e165b4c257c6ee25bca300802/CONTRIBUTORS.md)
[![Sister Repo: WerrSoma Connectome](https://img.shields.io/badge/Sister%20Repo-WerrSoma%20Connectome-00f0ff.svg)](https://github.com/Lexovian/WerrSoma)
[![Sister Repo: WerreduR](https://img.shields.io/badge/Sister%20Repo-WerreduR%20v4.0-059669.svg)](https://github.com/jesmaat/WerreduR)
[![Sister Repo: WERRobotics](https://img.shields.io/badge/Sister%20Repo-WERRobotics%20(Arduino%20Edge%20AI)-ff9100.svg?logo=arduino&logoColor=white)](https://github.com/pCwOrM/WERRobotics)

![General Divisor Theorem Lean 4 Infographic](gdt_twitter_infographic.png)

Machine-certified formalization of the **General Divisor Theorem (GDT)**: exact density correction under residue conditioning, formalized in Lean 4.

### 🏆 Kernel-Verified Theorem Milestone — October 2026 ([PR #1](https://github.com/pCwOrM/general-divisor-theorem/pull/1) by [@thinkthoughts](https://github.com/thinkthoughts))

Through a landmark collaborative formalization led by **Dan Hawkley ([@thinkthoughts](https://github.com/thinkthoughts) / [@Precedent_Vice](https://x.com/Precedent_Vice))** in **[PR #1](https://github.com/pCwOrM/general-divisor-theorem/pull/1)**, all original axioms and bridge obligations across the repository have been constructively discharged into **39 kernel-checked Lean 4 theorems and lemmas** across [`GeneralDivisorTheorem.lean`](GeneralDivisorTheorem.lean) (16), [`VolkanBridge.lean`](VolkanBridge.lean) (10), and [`DensityBridge.lean`](DensityBridge.lean) (13):

| Module & Core Theorem | Mathematical Statement | Verification |
|---|---|---|
| `GeneralDivisorTheorem.T_min_eq_lcm` | $T_{\min}(N, m) = \mathrm{lcm}(m, \mathrm{rad}(N))$ | Kernel-checked (`0 sorry`) |
| `GeneralDivisorTheorem.exponent_blindness` | $\gcd(n, N) = 1 \iff \gcd(n, \mathrm{rad}(N)) = 1$ | Kernel-checked (`0 sorry`) |
| `GeneralDivisorTheorem.C_factor_prime_product` | $C(d) = \prod_{p \mid d} \frac{p}{p - 1}$ for squarefree $d > 0$ | Kernel-checked (`0 sorry`) |
| `GeneralDivisorTheorem.inadmissible_branch_empty` | $\gcd(|a|, d) > 1 \implies \neg S_{\text{indicator}}(N, m, a, n)$ | Kernel-checked (`0 sorry`) |
| `GeneralDivisorTheorem.admissible_periodicity` | $S_{\text{indicator}}(N, m, a, n + T_{\min}) \iff S_{\text{indicator}}(N, m, a, n)$ | Kernel-checked (`0 sorry`) |
| `GeneralDivisorTheorem.specialization_divides` | Theorem 2 ($m \mid N \implies d = \mathrm{rad}(m)$) | Kernel-checked (`0 sorry`) |
| `GeneralDivisorTheorem.specialization_unitary` | Theorem 1' ($R = \mathrm{rad}(N/m),\ T_{\min} = m \cdot \mathrm{rad}(N/m)$) | Kernel-checked (`0 sorry`) |
| `GeneralDivisorTheorem.specialization_primorial` | Theorem 1 ($d = m,\ R = N/m,\ T_{\min} = N$) | Kernel-checked (`0 sorry`) |
| `GeneralDivisorTheorem.VolkanBridge.*` (10 theorems) | Two-way isomorphism (`bridge_rad_eq`, `bridge_d_eq`, `bridge_R_eq`, `bridge_Tmin_eq`, `bridge_C_eq`, §3.3 benchmarks) | Kernel-checked (`0 sorry`) |
| `GeneralDivisorTheorem.gdt_count_per_period` ([`DensityBridge.lean`](DensityBridge.lean)) | $\mathrm{card}\{0 \le n < T_{\min} : n \equiv a \pmod{m},\ \gcd(n, N) = 1\} = \varphi(R)$ via affine unit permutation over $\mathbb{Z}/R\mathbb{Z}$ | Kernel-checked (`0 sorry`) |

**Verification results ([Full Audit Certificate](docs/KERNEL_VERIFICATION_AUDIT_CERTIFICATE.md) • [Contributors](CONTRIBUTORS.md))**

- `lake build GeneralDivisorTheorem VolkanBridge DensityBridge` — **PASS (39 theorems & lemmas)**
- Project-defined axioms remaining across all 3 Lean modules — **0**
- `sorry` / `admit` occurrences across all 3 Lean modules — **0**
- Dependency audit — `propext`, `Classical.choice`, `Quot.sound` only

**Verified merge commit:** `a5ef2b6` ([PR #1](https://github.com/pCwOrM/general-divisor-theorem/pull/1) from `ac6586c`).

The results certify the exact formal statements under their specified hypotheses. The foundational axioms listed above are standard Lean dependencies, rather than additional GDT assumptions.

Based on the monograph by **Dan Hawkley / thinkthoughts** ([@Precedent_Vice](https://x.com/Precedent_Vice)):
> *The General Divisor Theorem: Exact Density Correction under Residue Conditioning* (Draft v3.3)  
> Paper: [https://antiviolence.ai/gdt.pdf](https://antiviolence.ai/gdt.pdf) (Permanent Mirror: [docs/gdt.pdf](docs/gdt.pdf))  
> Formalization Monograph (PDF): [General_Divisor_Theorem_Lean4_Formalization.pdf](General_Divisor_Theorem_Lean4_Formalization.pdf)  
> Zenodo Permanent Archive: [10.5281/zenodo.23316070](https://doi.org/10.5281/zenodo.23316070)  
> Upstream Challenge Repository: [https://github.com/thinkthoughts/general-divisor-theorem](https://github.com/thinkthoughts/general-divisor-theorem)  
> Reading-Point Lean 4 Port: [https://github.com/thinkthoughts/gap-lean4-port-gdt](https://github.com/thinkthoughts/gap-lean4-port-gdt)  
> Mathematical Basis: [https://github.com/thinkthoughts/mathematical-basis](https://github.com/thinkthoughts/mathematical-basis)

---

## 1. Overview & Mathematical Formulation

Let $N, m \in \mathbb{N}^+$ and $a \in \mathbb{Z}$. Consider the counting problem:

$$
S(N, L, m, a) = \{1 \le n \le L : n \equiv a \pmod{m}, \gcd(n, N) = 1\}
$$

A naive independent-density heuristic predicts:

$$
|S(N, L, m, a)| \approx \frac{\phi(N)}{N} \frac{L}{m}
$$

This naive heuristic double-counts restrictions whenever $m$ and $N$ share prime factors. The General Divisor Theorem isolates this shared-prime structure directly via:

$$
d = \mathrm{rad}(\gcd(m, N)), \qquad R = \frac{\mathrm{rad}(N)}{d}
$$

### The Exact Dichotomy

#### 1. Inadmissible Branch ($\gcd(a, d) > 1$)
The accepted set is identically empty for every $L$:

$$
S(N, L, m, a) = \emptyset, \quad \forall L
$$

#### 2. Admissible Branch ($\gcd(a, d) = 1$)
The indicator function has an **exact minimal period**:

$$
T_{\min} = m R = \mathrm{lcm}(m, \mathrm{rad}(N))
$$

with **exactly $\phi(R)$ accepted values per full period**.

Relative to the naive prediction, the exact correction factor is:

$$
C(N, m) = \frac{d}{\phi(d)} = \prod_{p \mid \gcd(m, N)} \frac{p}{p - 1}
$$

strictly independent of the admissible residue $a$.

---

## 2. Specializations Formally Covered

### Theorem 2 ($m \mid N$)
When $m$ divides $N$:

$$
d = \mathrm{rad}(m), \quad R = \frac{\mathrm{rad}(N)}{\mathrm{rad}(m)}, \quad T_{\min} = m \frac{\mathrm{rad}(N)}{\mathrm{rad}(m)}, \quad C(N, m) = \frac{m}{\phi(m)}
$$

### Theorem 1' (Unitary Divisor: $\gcd(m, N/m) = 1$)
When $m$ is a unitary divisor:

$$
R = \mathrm{rad}(N/m), \quad T_{\min} = m \cdot \mathrm{rad}(N/m)
$$

### Theorem 1 (Primorial Specialization: squarefree $N = P_k$, $m \mid P_k$)
When $N = P_k$ is squarefree and $m \mid P_k$:

$$
d = m, \quad R = \frac{P_k}{m}, \quad T_{\min} = P_k, \quad C(m) = \frac{m}{\phi(m)}
$$

### Distinguishing Test Instances

- **Minimal Period Test ($N=18, m=2$):**  
  Coarser period is $N=18$, but minimal period is $T_{\min} = 6 \neq 18$.
- **Sharp Admissibility Test ($N=5, m=6, a=2$):**  
  Naive check fails ($\gcd(a, m) = \gcd(2, 6) = 2 > 1$), but GDT yields $d = \mathrm{rad}(\gcd(6, 5)) = 1 \implies \gcd(2, 1) = 1$ (admissible under GDT!). Exact correction $C(5, 6) = 1$.

---

## 3. Lean 4 Formalization

The core theorems and definitions are formalized in [`GeneralDivisorTheorem.lean`](GeneralDivisorTheorem.lean):

```lean
-- Exact correction factor definition
def C_factor (d : Nat) : Rat :=
  if Nat.totient d = 0 then 0
  else (d : Rat) / (Nat.totient d : Rat)

-- Verified concrete instances
theorem instance_m6_C  : C_factor 6 = 3 := by unfold C_factor; norm_num
theorem instance_m10_C : C_factor 10 = 5 / 2 := by unfold C_factor; norm_num
theorem instance_m30_C : C_factor 30 = 15 / 4 := by unfold C_factor; norm_num
```

### Two-Way Cross-Validation Bridge (`VolkanBridge.lean`) & Exact Period Count (`DensityBridge.lean`)

Per Dan Hawkley's ([@thinkthoughts](https://github.com/thinkthoughts) / [@Precedent_Vice](https://x.com/Precedent_Vice)) architectural roadmap:
- **[`VolkanBridge.lean`](VolkanBridge.lean) (10 Kernel-Checked Theorems):** Establishes a two-way cross-validation bridge between Volkan's functional API (`rad`, `d_param`, `R_param`, `T_min`, `C_factor`, `S_indicator`) and Dan's prime-support reading-point specification (`radN`, `d`, `R`, `Tmin`, `correctionFactor`, `Good`). See [`docs/VOLKAN_BRIDGE_SPEC.md`](docs/VOLKAN_BRIDGE_SPEC.md).
- **[`DensityBridge.lean`](DensityBridge.lean) (13 Kernel-Checked Theorems):** Proves `GeneralDivisorTheorem.gdt_count_per_period`:
  $$\mathrm{card}\{0 \le n < T_{\min} : n \equiv a \pmod{m},\ \gcd(n, N) = 1\} = \varphi(R)$$
  by factoring the coprimality predicate along the arithmetic progression $r + m k$, proving $\gcd(m, R) = 1$ (`coprime_m_R`), and constructing the affine unit permutation `affinePermutation8` over `ZMod R`.
- **Full Audit Certificate:** See [`docs/KERNEL_VERIFICATION_AUDIT_CERTIFICATE.md`](docs/KERNEL_VERIFICATION_AUDIT_CERTIFICATE.md) and [`CONTRIBUTORS.md`](CONTRIBUTORS.md).

---

## 4. Verification & Testing

Run the exhaustive Python verifiers:
```bash
# 1. Core General Divisor Theorem verifier (2,287 checks)
python scripts/verify_gdt.py

# 2. Two-Way Cross-Validation & DensityBridge verifier (14,500+ checks)
python scripts/verify_bridge.py
```

Build all three Lean 4 modules with Lake:
```bash
lake build GeneralDivisorTheorem VolkanBridge DensityBridge
```

### Lean Kernel Dependency Audit

All 39 theorems across `GeneralDivisorTheorem`, `VolkanBridge`, and `DensityBridge` are independently auditable using Lean's `#print axioms` command.

Create `GDT_AxiomAudit.lean`:

```lean
import GeneralDivisorTheorem
import VolkanBridge
import DensityBridge

#print axioms GeneralDivisorTheorem.T_min_eq_lcm
#print axioms GeneralDivisorTheorem.exponent_blindness
#print axioms GeneralDivisorTheorem.C_factor_prime_product
#print axioms GeneralDivisorTheorem.specialization_unitary
#print axioms GeneralDivisorTheorem.specialization_primorial
#print axioms GeneralDivisorTheorem.gdt_count_per_period
```

Run:

```bash
lake env lean GDT_AxiomAudit.lean
```

All theorems report only:

`[propext, Classical.choice, Quot.sound]`

These are Lean's standard classical foundations. No additional project-specific axioms are required.

## 5. Citation & Attribution

```bibtex
@misc{dagli_hawkley2026gdt_lean4,
  author    = {Da\u{g}l\i, Volkan and Hawkley, Dan and Da\u{g}l\i, Zerrin and Da\u{g}l\i, Da\u{g}han},
  title     = {Machine-Certified Lean 4 Formalization of the General Divisor Theorem: Exact Density Correction under Residue Conditioning},
  year      = {2026},
  month     = {October},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.23316070},
  url       = {https://doi.org/10.5281/zenodo.23316070}
}

@misc{thinkthoughts2026gdt,
  author       = {Hawkley, Dan (thinkthoughts)},
  title        = {The General Divisor Theorem: Exact Density Correction under Residue Conditioning},
  year         = {2026},
  howpublished = {\url{https://antiviolence.ai/gdt.pdf}},
  note         = {Draft v3.3}
}
```

---

## 6. Acknowledgments & Computing Infrastructure

Dedicated bare-metal computing clusters, proof verification environments, and enterprise development resources were provided by **Bekirhan Dağlı** (Managing Partner) and **ITouch Systems Research & Development**.

---

## 7. Companion Open-Science Formal Architecture

This work is part of the unified open-science formal mathematics and theoretical computer science initiative developed by ITouch Systems Research Labs:
* **24D Niemeier Lattice $A_8^3$, K3 Hodge Duality & Umbral Moonshine in Lean 4:** [Zenodo: 10.5281/zenodo.23324066](https://doi.org/10.5281/zenodo.23324066) (Record: [`23324067`](https://zenodo.org/records/23324067)) • [GitHub: `pCwOrM/niemeier-a8-umbral-moonshine`](https://github.com/pCwOrM/niemeier-a8-umbral-moonshine)
* **Schönhage Tensor Carrier Compression (World Record):** [Zenodo: 10.5281/zenodo.23268580](https://doi.org/10.5281/zenodo.23268580) • [GitHub: `pCwOrM/integer-mult-bounds`](https://github.com/pCwOrM/integer-mult-bounds) • [CrocSwap PR #226 (`incorporated`)](https://github.com/CrocSwap/integer-mult-bounds/pull/226) • [Official Contributors Credit (`@pCwOrM`)](https://github.com/CrocSwap/integer-mult-bounds/blob/50d768818f579d4e165b4c257c6ee25bca300802/CONTRIBUTORS.md) • [Maintainer Audit (`50d76881`)](https://github.com/CrocSwap/integer-mult-bounds/blob/50d768818f579d4e165b4c257c6ee25bca300802/docs/research/community-reconciliation-next100-review.md)
* **WERR Core Monorepo:** [Zenodo: 10.5281/zenodo.22774934](https://doi.org/10.5281/zenodo.22774934) • [GitHub: `pCwOrM/mandelbrot-fractal-neural-synthesis`](https://github.com/pCwOrM/mandelbrot-fractal-neural-synthesis)
* **WerrSoma Whole-Brain Drosophila Connectome (158K Neurons):** [Zenodo: 10.5281/zenodo.23072929](https://doi.org/10.5281/zenodo.23072929) • [GitHub: `Lexovian/WerrSoma`](https://github.com/Lexovian/WerrSoma)
* **WerreduR Procedural Fractal Pedagogy (v4.0):** [Zenodo: 10.5281/zenodo.23128224](https://doi.org/10.5281/zenodo.23128224) • [GitHub: `jesmaat/WerreduR`](https://github.com/jesmaat/WerreduR)

Formalized under Apache-2.0.

