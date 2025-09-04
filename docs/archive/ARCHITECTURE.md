### Project Architecture (RS/Schur-first)

- **Goal**: Modernize the proof workspace to cleanly separate RS (Schur globalization), Euler product wrappers, and Diagonal Fredholm product machinery while avoiding new axioms.
- **Entry point**: `rh/Proof/Main.lean` (Lean scaffold; no sorries). This collects stable imports and documents the proof route.

### Tracks & Responsibilities
- **Agent RS (Schur globalization)**
  - File: `rh/RS/SchurGlobalization.lean`
  - Targets:
    - `Rect.isOpen_Ω` (openness of union of rectangles)
    - `SchurOnRectangles` (Poisson/Herglotz + Cayley ⇒ analytic Θ on Ω, |Θ| ≤ 1, and 1+J ≠ 0)
    - `NoInteriorZeros` (strict boundary margin ⇒ no interior zeros by maximum modulus)
    - `ZetaNoZerosOnRe1FromSchur` (if ζ = Θ/N, N analytic nonvanishing on closure, then ζ zero-free on Re=1)
  - Rule: If a deep missing lemma arises, add a one-line note to `BLOCKERS.md` and stop.

- **Agent DF (Weierstrass/product)**
  - Files: `rh/academic_framework/DiagonalFredholm/WeierstrassProduct.lean`, `ProductLemmas.lean`
  - Actions: Use current mathlib API (HasProd/Multipliable, `HasSum.cexp`, `Complex.norm_log_one_add_le` with z ↦ -z). Replace deprecated `tprod_*` and nonexistent `Complex.norm_log_one_sub_le`.

- **Agent Comp (Comprehensive)**
  - File: `rh/academic_framework/DiagonalFredholm/Comprehensive.lean`
  - Actions: Fix invalid field notation on predicates, add `[DecidableEq ι] [Countable ι]` when required, switch to modern product/sum lemmas.

- **Agent EPM (Euler product and ζ wrappers)**
  - File: `rh/academic_framework/EulerProductMathlib.lean`
  - Actions: Keep mathlib-backed facts: `riemannZeta_eulerProduct_tprod`, trivial zeros, `riemannZeta_ne_zero_of_one_lt_re`. For `Re=1`, delegate to `RS.ZetaNoZerosOnRe1FromSchur` or existing RS stub.
  - Actions: Keep mathlib-backed facts: `riemannZeta_eulerProduct_tprod`, trivial zeros, `riemannZeta_ne_zero_of_one_lt_re`. For `Re=1`, delegate to `RS.ZetaNoZerosOnRe1FromSchur` (implemented; no axioms).

### Global Rules
- No new axioms. No deletions or mass renames. Edit only your track files.
- On deep missing lemma: append to `BLOCKERS.md` with file:line, Lean goal, minimal context, proposed approach; then stop.
- Build cadence: `scripts/clean_build.sh` on macOS if hidden files interfere; otherwise `lake build`.
- After each local fix: rebuild; if next error is outside your track, stop and report.
- Commit style: `git add <files> && git commit -m "fix(track-XYZ): <short>"`.

### Notes
- Use `Mathlib/Topology/Algebra/InfiniteSum/Basic` and friends for products, `Mathlib/Analysis/SpecialFunctions/Complex/LogBounds` for log bounds, and avoid deprecated `tprod_*` globals.
