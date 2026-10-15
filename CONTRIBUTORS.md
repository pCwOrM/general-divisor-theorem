# Contributors & Formal Verification Architects

We gratefully acknowledge the mathematicians, formal verification architects, and researchers who have contributed to the **General Divisor Theorem (GDT) Lean 4 Formalization** (`pCwOrM/general-divisor-theorem`).

---

## Core Authors & Principal Architects

* **Volkan Dağlı ([@pCwOrM](https://github.com/pCwOrM))** — *Principal Investigator & WERR Ecosystem Architect*  
  Anadolu University & ITouch Systems Research Labs • ORCID: [`0009-0000-1587-8703`](https://orcid.org/0009-0000-1587-8703)  
  Initial Lean 4 functional specification (`GeneralDivisorTheorem.lean`), two-way cross-validation architecture (`VolkanBridge.lean`), and exhaustive Python verification suites (`scripts/verify_gdt.py`, `scripts/verify_bridge.py`).

* **Dan Hawkley ([@thinkthoughts](https://github.com/thinkthoughts) / [@Precedent_Vice](https://x.com/Precedent_Vice))** — *Author of the General Divisor Theorem Monograph & Principal Lean 4 Kernel Verification Architect*  
  [antiviolence.ai](https://antiviolence.ai/gdt.pdf) • Upstream Repositories: [`thinkthoughts/general-divisor-theorem`](https://github.com/thinkthoughts/general-divisor-theorem), [`thinkthoughts/gap-lean4-port-gdt`](https://github.com/thinkthoughts/gap-lean4-port-gdt), [`thinkthoughts/mathematical-basis`](https://github.com/thinkthoughts/mathematical-basis)  
  **Landmark Contribution ([PR #1](https://github.com/pCwOrM/general-divisor-theorem/pull/1)):**
  * Discharged **all 8 original axioms** in [`GeneralDivisorTheorem.lean`](GeneralDivisorTheorem.lean) (`T_min_eq_lcm`, `exponent_blindness`, `C_factor_prime_product`, `specialization_divides`, `specialization_unitary`, `specialization_primorial`, `inadmissible_branch_empty`, `admissible_periodicity`) into **16 kernel-checked theorems and lemmas** with **0 custom axioms** and **0 `sorry`**.
  * Discharged **all 7 bridge obligations** in [`VolkanBridge.lean`](VolkanBridge.lean) into **10 kernel-checked theorems and lemmas** (`0 axioms`, `0 sorry`).
  * Authored [`DensityBridge.lean`](DensityBridge.lean) (**13 kernel-checked theorems and lemmas**, `0 axioms`, `0 sorry`), constructively proving the exact per-period count `gdt_count_per_period`:
    $$\operatorname{card}\{0 \le n < T_{\min} : n \equiv a \pmod{m},\ \gcd(n, N) = 1\} = \varphi(R)$$
    via affine unit permutations (`affinePermutation8`) over `ZMod R`.

* **Zerrin Dağlı** — *Co-Author & Formal Verification Researcher*  
  Mersin University & Yusuf Kalkavan Anadolu Lisesi • ORCID: [`0000-0001-9490-6425`](https://orcid.org/0000-0001-9490-6425)

* **Dağhan Dağlı** — *Co-Author & Computational Verification Researcher*  
  Toros Science High School, MEV (Toros University) • ORCID: [`0009-0003-2492-8313`](https://orcid.org/0009-0003-2492-8313)

---

## Infrastructure & Institutional Support

* **Bekirhan Dağlı** — *Managing Partner, ITouch Systems Research & Development*  
  Bare-metal computing clusters, proof verification environments, and enterprise development infrastructure.
