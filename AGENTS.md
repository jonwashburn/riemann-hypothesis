### Agents and Roles

- **RS (Schur globalization)**
  - File: `rh/RS/SchurGlobalization.lean`
  - Prove:
    - `Rect.isOpen_Ω`
    - `SchurOnRectangles`
    - `NoInteriorZeros`
    - `ZetaNoZerosOnRe1FromSchur`
  - Policy: If a required lemma is deep/missing in mathlib, add a 1-line entry to `BLOCKERS.md` and stop.

- **DF-WP (Weierstrass/product)**
  - Files: `rh/academic_framework/DiagonalFredholm/WeierstrassProduct.lean`, `ProductLemmas.lean`
  - Use: `Mathlib/Analysis/SpecialFunctions/Complex/LogBounds`, `HasProd/Multipliable`, `HasSum.cexp`.
  - Replace deprecated `tprod_*` and nonexistent `Complex.norm_log_one_sub_le`.

- **DF-Comp (Comprehensive)**
  - File: `rh/academic_framework/DiagonalFredholm/Comprehensive.lean`
  - Fix field-notation on predicates; add `[DecidableEq ι] [Countable ι]` only if required; switch to modern lemmas.

- **EPM (Euler product and ζ wrappers)**
  - File: `rh/academic_framework/EulerProductMathlib.lean`
  - Keep mathlib-backed facts: `riemannZeta_eulerProduct_tprod`, trivial zeros, `riemannZeta_ne_zero_of_one_lt_re`.
  - For `Re=1`, delegate to `RS.ZetaNoZerosOnRe1FromSchur` (implemented; no axioms).

 - **Cert-Kξ (Certificate Kξ + P+)**
   - File: `rh/Cert/KxiPPlus.lean`
   - Prove/Define:
     - `PPlus` boundary wedge predicate on the critical line.
     - Abstract Carleson box–energy interface and `KxiBound` (analytic Kξ bound).
     - Target statement shape `PPlusFromCarleson` (no axioms; statement only).
   - Policy: If Carleson energy, Poisson/CR–Green pairing, or VK zero-density are missing in mathlib, add a 1-line entry to `BLOCKERS.md` and stop.

### Global Rules
- Edit only your track files. No new axioms. No deletions or mass renames.
- On deep missing lemma: log to `BLOCKERS.md` and STOP.
- Build once, fix first error in your track; if next error is outside your track, STOP and report.
- Commit small, atomic changes with `fix(track-<name>): <short>`.

### Execution Plan and Dependencies

- RS → EPM: After `RS.ZetaNoZerosOnRe1FromSchur` is implemented and exported, EPM should expose `zeta_nonzero_re_eq_one` delegating to RS (no axioms).
- H′‑Cauchy → Factors: After the uniform `H′` strip bound exists, `rh/Cert/FactorsWitness.lean` should use `FEFactors_from_Hderiv (UniformHDerivBound.of_FGammaPrime ...)` (already scaffolded) so no fallback constants remain.
- Cert‑Kξ runs in parallel; it must not introduce axioms and should only add statements/interfaces.

### Additional Guidance per Agent (deliverables and acceptance)

- RS (Schur globalization)
  - Deliverables:
    - Implement: `Rect.isOpen_Ω`, `SchurOnRectangles`, `NoInteriorZeros`, `ZetaNoZerosOnRe1FromSchur` with no `admit`/`sorry`.
    - Ensure the removable‑singularity bridge used by the pinch is present in `rh/RS/SchurGlobalization.lean` or nearby RS context files.
  - Acceptance:
    - Compiles with no new axioms; only RS track files edited.
    - `ZetaNoZerosOnRe1FromSchur` is available for EPM to import.

- EPM (Euler product and ζ wrappers)
  - Deliverables:
    - Expose `zeta_nonzero_re_eq_one (z : ℂ) (hz : z.re = 1)` delegating to `RS.ZetaNoZerosOnRe1FromSchur` once provided by RS.
    - Remove any `admit`/`sorry` in this module; keep mathlib‑only reasoning here.
  - Acceptance:
    - No axioms; mathlib imports only; builds after RS export is available.

- H′‑Cauchy (Archimedean derivative bound)
  - Files: `rh/academic_framework/GammaBounds.lean`, `rh/Cert/FactorsWitness.lean`
  - Objectives:
    - Prove a uniform bound on `‖H′(s)‖` for `H(s)=π^{-s/2}Γ(s/2)` on the closed strip `σ ∈ [σ0,1]`, `σ0>1/2`, via a Cauchy circle of radius `r = σ0/2`.
    - Produce a Prop/lemma equivalent to `BoundedFGammaPrimeOnStrip σ0` giving an explicit `C ≥ 0`.
    - Wire that constant into `UniformHDerivBound.of_FGammaPrime` so `factors_witness` uses `FEFactors_from_Hderiv`.
  - Inputs: see `gamma-bounds-gpt5.txt` for the intended argument outline; prefer mathlib facts (Cauchy estimate on circles, cpow modulus, basic Γ vertical‑strip bounds).
  - Acceptance:
    - No new axioms; compiles in this track. If a needed library lemma (e.g., a specific Cauchy derivative bound) is missing, add a one‑line entry to `BLOCKERS.md` and stop.

- Cert‑Kξ (Certificate Kξ + P+)
  - Deliverables:
    - Define `PPlus` (boundary wedge predicate) and `KxiBound` (Carleson box–energy interface), Prop‑level is acceptable.
    - Add the statement `PPlusFromCarleson` with precise hypotheses (no axioms; statement only).
    - Update any destructuring to the current `BoundedFGammaPrimeOnStrip` nested `Exists` if referenced here.
  - Acceptance:
    - Compiles; no axioms; only this file edited.

### Working Protocol (all agents)

- Edit only your track files. No new axioms. No deletions or mass renames.
- Build once and fix the first error in your track. If the next error is outside your track, STOP and report.
- If a needed lemma is deep or missing in mathlib, add a one‑line blocker in `BLOCKERS.md` and STOP.
- Keep edits small and atomic; commit as `fix(track-<name>): <short>`.
- Prefer short, finished proofs over mirroring the manuscript; cite mathlib lemmas where possible.

### Acceptance Checklist (per task)

- Builds cleanly; no new `admit`/`sorry` introduced by your edits.
- No axioms added; mathlib‑only imports.
- Public names and signatures match Objectives so downstream modules can import them.
- Any missing library items recorded succinctly in `BLOCKERS.md`.
