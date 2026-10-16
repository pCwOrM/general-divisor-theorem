# GDT Lean Audit — gdt-density-bridge @ 43f3a78

Oct 15, 2026 · @Daniel Thomas Hawkley

The compiled GDT development is free of proof holes, and its headline results are mathematically sound; the branch needs repository cleanup before merge.

## Scope and method

- **Tree audited:** `thinkthoughts/general-divisor-theorem-pCwOrM`, branch `gdt-density-bridge`, tip `43f3a78`. The supplied ZIP's archive comment reads `43f3a78a926b…`, and its contents are byte-identical to a fresh clone of the branch.
- **Earlier ZIP:** the first upload was `main` at `80ca841`, holding only `GeneralDivisorTheorem.lean` and `VolkanBridge.lean`; it was set aside.
- **Evidence used:** Lean sources and build configuration only. README text, commit messages and prior reviews were treated as claims to check.
- **Build:** Lean v4.21.0 installed and mathlib fetched at the pinned commit `308445d`. The prebuilt mathlib cache host (`lakecache.blob.core.windows.net`) is blocked from the audit sandbox, so a full `lake build` was out of reach there; a source build of mathlib on 2 cores would take many hours.
- **What was verified instead:**
  - every compiled module read line by line;
  - all \~35 external mathlib lemma names used by the proofs confirmed present at `308445d`;
  - the author's committed `.lake/build/*.trace` logs show warnings only, at line numbers matching the current sources (e.g. `GeneralDivisorTheorem.lean:520`, `GDTMain.lean:9`) — supporting evidence, short of an independent build.

## 1. Blocking correctness issues

None found in the compiled modules. Each headline result was checked by hand.

| Result | Location | Finding |
| --- | --- | --- |
| Exact count C(qT+s) = qφ(R) + C(s) | `DensityCount.lean`, `countBelow_mul_T_min_add` | Correct; proved under 0\<N, 0\<m, gcd(\|a\|,d)=1. Admissibility is necessary: the inadmissible case has C ≡ 0 while φ(R) ≥ 1. Chain: `gdt_count_per_period` (`DensityBridge.lean:336`) → shift bijection, so every period block has the same count → induction on q → tail bijection for s. |
| Natural density φ(R)/T\_min | `DensityLimit.lean:158`, `density_limit` | Correct. `density_error_bound` (line 72) gives \|T·C(X) − φ(R)·X\| ≤ T²; with X = qT + r this is \|T·c\_r − φ(R)·r\| ≤ T². Dividing by T·X bounds the error by T/X → 0, closed by `squeeze_zero'`. T\_min is defined as m\*R, so φ(R)/(mR) holds by unfolding. |
| Correction identity φ(R)·N·φ(d) = d·R·φ(N) | `CorrectionBridge.lean:17`, `gdt_correction_identity` | Correct. φ(N)/N = φ(rad N)/rad N (`exponent_blindness`), rad N = d·R with d, R coprime, so φ(rad N) = φ(d)φ(R). Equivalent to φ(R)/(mR) = (d/φ(d))·φ(N)/(Nm) for m, N, φ(d) > 0, so it supports the d/φ(d) factor; the rational form itself is unproved (see 3.3). |
| Branch packaging | `GDTMain.lean:53`, `general_divisor_theorem` | Correct. The right disjunct carries gcd = 1 explicitly, so it holds only in the admissible case; the left disjunct comes from `inadmissible_empty_criterion`. |

## 2. Proof-engineering issues

The two items worth fixing first are the committed build cache and `native_decide`; the rest is tidying.

| # | Location | Issue | Fix |
| --- | --- | --- | --- |
| 2.1 | `.lake/build/lib/lean/*.olean`, `*.trace`, `*.hash`; root `DensityCombined.olean` | Compiled build output is tracked in git, with no `.gitignore`. On a fresh clone, Lake may reuse these files rather than re-check the proofs. | Remove them; add `.gitignore` with `.lake/` and `*.olean`. Reviewers run `rm -rf .lake` or `lake clean` first. |
| 2.2 | `VolkanBridge.lean:234, 236, 237, 251, 254` | `native_decide` adds `Lean.ofReduceBool` beyond the standard three axioms; the committed `VolkanBridge.olean` contains `_nativeDecide_1_*` and `ofReduceBool`. GDTMain stays unaffected (it skips VolkanBridge), and `Audit.lean` leaves these benchmarks unaudited. | Use `decide` / `norm_num` / `simp` (the numbers are tiny), or audit them and document the extra axiom. |
| 2.3 | `GeneralDivisorTheorem.lean.pre-{exponent,factor,lcm,primorial,unitary}`; `DensityBridge.lean.bak:16` | Uncompiled backups contain real `axiom` and `sorry` text, which clutters any repo-wide hole scan. | Delete backups. |
| 2.4 | `DensityStep1–8*.lean`, `*Check.lean`, `*Lemmas.lean`, `*Probe.lean`, `DensityCombined.lean`, `DensityAxioms.lean`, `GDT_AxiomAudit.lean`, `GDT_MergeAudit.lean`, `n`, `how --stat af01707` | Scratch and junk files; `DensityCombined.lean` is identical to `DensityBridge.lean`; `n` is empty; `how --stat af01707` is pasted `git show` output. | Delete, or move kept checks to a `scratch/` folder. |
| 2.5 | `DensityBridge.lean:51, 59, 41` | `affinePermutation` duplicates `affinePermutation8` (line 95); `affinePermutation_apply` is unused, its proof re-inlined at lines 297–301 and 321–326; `progression_injective` is unused. `-- Source: DensityStepN.lean` comments and names `residue3` / `affinePermutation8` are scratch leftovers. | Keep one permutation plus its `_apply` lemma; rename to final names. |
| 2.6 | `CorrectionBridge.lean:7, 31` | `totient_rad_eq_d_mul_R` is proved, then redone inline at line 58; `hR` appears unused. | Reuse the lemma; drop `hR`. |
| 2.7 | `CoprimeBridge.lean`, `coprime_m_R_bridge` | Pure alias of `coprime_m_R`, kept as a module and a default target. | Retire the module. |
| 2.8 | `GeneralDivisorTheorem.lean:84, 286, 307, 608`; `GDTMain.lean:7`; `CorrectionBridge.lean:34–43` | `rad_pos`, `rad_squarefree`, `gcd_rad_eq`, `admissible_coprime_d` are `private`, so downstream re-proves positivity; the d ∣ gcd m N argument appears three times (lines 89, 171, 426). | Make these public; add one `d_param_dvd_gcd` lemma. |
| 2.9 | Lint log | Unused variables: `DensityBridge.lean:11, 186, 260`, `GDTMain.lean:9`. Dead `<;> ring`: `GeneralDivisorTheorem.lean:520`. `simpa` → `simp`: `GeneralDivisorTheorem.lean:242, 256`, `DensityCount.lean:127, 200`. Extra `<;>`: `DensityLimit.lean:227`. | Clear the warnings. |
| 2.10 | `DensityLimit.lean`, `VolkanBridge.lean:16–23` | Both import all of `Mathlib`; VolkanBridge also lists redundant specific imports. | Narrow the imports. |
