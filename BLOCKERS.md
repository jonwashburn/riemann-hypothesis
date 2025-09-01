# BLOCKERS

This file tracks mathematical blockers encountered during the build-fix loop.

Format:
- MATH-BLOCKER: <one-line description>
  - Location: <file:line>
  - Lean goal / statement: <copy of the goal>
  - Proposed approach: <short plan, links to mathlib refs if known>
  - Stub: <lemma name in rh/Blockers/Triage.lean>

---

- MATH-BLOCKER: Carleson box energy framework on half-plane (Whitney boxes)
  - Location: meta-proof/rh/Cert/KxiPPlus.lean (interface needed)
  - Lean goal / statement: Define and use a Carleson measure `μ = |∇U|^2 σ dt dσ` and prove `μ(Q(I)) ≤ C · |I|` for analytic `U = Re log ξ` on Whitney boxes.
  - Proposed approach: Seek or build an interface around Poisson extensions and Carleson embedding on the half-plane; if missing, isolate as axioms in a separate namespace and keep proofs external.
  - Stub: `Cert.CarlesonBoxEnergyWhitney`
  - Progress: Added `WhitneyInterval`, `CarlesonBox`, and `BoxEnergy` interfaces (no axioms) in `rh/Cert/KxiPPlus.lean`. Introduced `KxiBound` and `PPlusFromCarleson` statement forms.
  - Next: Add CR–Green pairing interface and link `BoxEnergy.bound` to `(K0+Kξ)|I|` to enable a pure-statement (P+) lemma.

- MATH-BLOCKER: VK zero-density/counting usable form
  - Location: meta-proof/rh/Cert/KxiPPlus.lean (Kξ bound interface)
  - Lean goal / statement: A lemma giving annular counts `ν_k ≲ 2^k L log ⟨T⟩ + log ⟨T⟩` sufficient to derive `Kξ` Carleson bound.
  - Proposed approach: Cite Titchmarsh/Ivić statements; provide constants abstractly, keeping formalization as assumptions until mathlib support exists.
  - Stub: `Cert.VKAnnularCount`
  - Progress: Added `VKAnnularCount` interface and a summary constructor `KxiFromVK` that states “VK + annular L2 ⇒ KξBound” as a Prop (no axioms).
  - Next: Model the annular L2 kernel inequality at the interface level and state the sum-over-annuli inequality as a Prop connecting to `KxiFromVK`.

- MATH-BLOCKER: Characterize zeros of ζ(s) with Re(s) ≤ 0 as trivial zeros
  - Location: rh/academic_framework/EulerProductMathlib.lean:125
  - Lean goal / statement:
    `∀ z : ℂ, z.re ≤ 0 → riemannZeta z = 0 → ∃ n : ℕ, 0 < n ∧ z = -2 * n`
  - Proposed approach: cite the functional equation and known classification of zeros; replace with a mathlib lemma if/when available. Until then, keep proof externalized.
  - Stub: `Blockers.zeta_zero_in_Re_le_zero_is_trivial`

- MATH-BLOCKER: Fill proof of `zeta_zero_in_Re_le_zero_is_trivial` (current stub)
  - Location: rh/Blockers/Triage.lean:12–16
  - Lean goal / statement:
    `∀ z : ℂ, z.re ≤ 0 → riemannZeta z = 0 → ∃ n : ℕ, 0 < n ∧ z = (-2 : ℂ) * (n : ℂ)`
  - Proposed approach:
    1) Use the functional equation `ξ(s) = ξ(1 - s)` with `ξ` entire, and symmetry of zero sets.
    2) Combine with known nontrivial-zero localization `0 < Re(s) < 1` to exclude Re(s) ≤ 0 except the gamma/polynomial trivial factors.
    3) Derive that any zero with Re ≤ 0 must come from the gamma/polynomial factor, hence at negative even integers.
    4) Alternatively, use Hadamard product factorization of ζ and the gamma factor’s poles/zeros alignment.
  - Dependencies needed in mathlib:
    - Functional equation in a usable form; zero-set symmetries.
    - Statement that nontrivial zeros lie in the critical strip.
  - Interim helpers added:
    - `zeta_trivial_zero` and `zeta_eq_zero_of_neg_even` wrappers using `riemannZeta_neg_two_mul_nat_add_one` to unblock downstream uses where only the forward direction is needed.

- RESOLVED: Non-vanishing of ζ on the boundary line Re(s) = 1
  - Location: `rh/RS/SchurGlobalization.lean`, `rh/academic_framework/EulerProductMathlib.lean`
  - Lean goal / statement:
    `∀ z : ℂ, z.re = 1 → riemannZeta z ≠ 0`
  - Resolution: Implemented `RS.ZetaNoZerosOnRe1FromSchur` by delegating to the mathlib lemma
    `riemannZeta_ne_zero_of_one_le_re`. Added public wrapper
    `RH.AcademicFramework.EPM.zeta_nonzero_re_eq_one` delegating to RS.
  - Stubs: none

- MATH-BLOCKER: Numeric enclosure for arithmetic tail constant `K0`
  - Location: rh/academic_framework/EulerProduct/K0Bound.lean
  - Lean goal / statement:
    Prove the explicit bound `K0 ≤ 0.03486808` where
    `K0 = (1/4) * ∑_{k≥2} (∑_p p^{-k}) / k^2`.
  - Proposed approach:
    Split `k ≤ 20` via interval-checked prime sums and bound the tail by
    `∑_{k≥21} (ζ(k)-1)/k^2` using a proven inequality (Dusart/Rosser–Schoenfeld)
    and an integral remainder. Encapsulate numerics in a separate file or use
    mathlib numerics/interval tactics if available.
  - Stub: none (definitions landed; numeric evaluation pending)

- MATH-BLOCKER: Carleson box computation for prime-power tail `U₀`
  - Location: rh/academic_framework/EulerProduct/K0Bound.lean (conceptual origin)
  - Lean goal / statement:
    Derive rigorously that the Carleson box ratio of `U₀(s) = Re ∑_{p}∑_{k≥2} p^{-ks}/k`
    over Whitney boxes equals `(1/4) * ∑_{p}
    ∑_{k≥2} p^{-k}/k^2`, i.e., the constant `K0` defined here.
  - Proposed approach:
    Formalize the half-plane Carleson geometry for harmonic functions and the
    identity `|∇ Re f|^2 = |f'|^2` for analytic `f`, then compute the Whitney
    box integral explicitly and pass sup over normalized boxes.
  - Stub: none (requires a small Carleson framework; keep externalized until available)
