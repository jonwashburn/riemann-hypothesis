RS: ZetaNoZerosOnRe1FromSchur requires a ζ→Θ/N analytic bridge (Θ Schur on Ω, N analytic nonvanishing on closure); missing in codebase/mathlib, so export is blocked.
RS-ASSIGN: Producing `assign : Re=1 → LocalPinchData` from ζ→Θ/N needs a local removable-extension lemma ensuring an analytic `g` with `g(ρ)=1` agreeing with `Θ` on punctured neighborhoods; not present in mathlib at this specificity.
RS: Explicit Θ,N via Cayley with F:=2J and J:=det₂/(outer·ξ), ζ = Θ/N off zeros, and the pinned limit at ξ-zeros require a formal det₂/outer/ξ interface; not available—provide statement-level interface only.
- MATH-BLOCKER: Boundary assignment via pinned removable set
  - Location: `rh/RS/SchurGlobalization.lean`
  - Lean goal / statement: For each z with z.re = 1, choose open U ⊆ Ω and Z := Z(ξ), pick ρ ∈ Z ∩ U, and construct analytic g on U with EqOn Θ g (U \ Z) and g(ρ)=1, using Tendsto Θ → 1 along Ω \ Z near ρ (pinned limit). Package as `LocalPinchDataZ`.
  - Proposed approach: Need a mathlib lemma: from Θ analytic on Ω \ Z and Schur on Ω, plus lim Θ = 1 along Ω \ Z at ρ, build a removable analytic extension g on a small disc U with g(ρ)=1 and EqOn off Z. This is a multi-point removable-singularity construction relying on Riemann's theorem and boundary pinning; encode or cite if exists; otherwise keep as blocker.
  - Current RS interface provided for handoff: `OffZerosBoundaryHypothesis (Θ N)` requiring
    `IsSchurOn Θ Ω` and `(∀ z, z.re = 1 → ∃ (U Z) (data : LocalPinchDataZOff Θ N U Z), z ∈ U \ Z)`, and
    the RS corollary `ZetaNoZerosOnRe1_from_offZerosAssignmentStatement` which concludes
    `∀ z, z.re = 1 → riemannZeta z ≠ 0`. A longer-reasoning agent should produce the local
    data (U, Z = Z(ξ), ρ, g, agreement, g(ρ)=1, ζ=Θ/N, N≠0 on U \ Z) for each boundary point.
 - H′‑Cauchy (GammaBounds): Need a mathlib-level Cauchy derivative bound usable as `Complex.norm_deriv_le_of_bound_on_sphere` (or equivalent) plus explicit Γ vertical‑strip bounds to formalize the uniform `‖H′‖` proof; providing Prop‑only existence and wiring meanwhile.
# BLOCKERS

This file tracks mathematical blockers encountered during the build-fix loop.

Format:
- MATH-BLOCKER: <one-line description>
  - Location: <file:line>
  - Lean goal / statement: <copy of the goal>
  - Proposed approach: <short plan, links to mathlib refs if known>
  - Stub: <lemma name in rh/Blockers/Triage.lean>

---

- MATH-BLOCKER: Uniform vertical-strip bound for H′(s)=π^{-s/2}Γ(s/2)
  - Location: `rh/academic_framework/GammaBounds.lean`
  - Lean goal / statement: Provide a proof of `exists_uniform_bound_H_deriv_on_strip σ0` (σ0∈(1/2,1]) — existence of C,m ≥ 0 with `‖(π^{-s/2}Γ(s/2))'‖ ≤ C·(1+|Im s|)^m` for σ∈[σ0,1].
  - Proposed approach: Combine vertical-strip Stirling bounds for Γ and Γ′ with `|π^{-s/2}| = π^{-Re(s)/2}`; encode in mathlib if available, else externalize and keep interface.
  - Stub: `RH.AcademicFramework.GammaBounds.exists_uniform_bound_H_deriv_on_strip`

- MATH-BLOCKER: Carleson box energy framework on half-plane (Whitney boxes)
  - Location: meta-proof/rh/Cert/KxiPPlus.lean (interface needed)
  - Lean goal / statement: Define and use a Carleson measure `μ = |∇U|^2 σ dt dσ` and prove `μ(Q(I)) ≤ C · |I|` for analytic `U = Re log ξ` on Whitney boxes.
  - Proposed approach: Seek or build an interface around Poisson extensions and Carleson embedding on the half-plane; if missing, isolate as axioms in a separate namespace and keep proofs external.
  - Stub: `Cert.CarlesonBoxEnergyWhitney`
  - Progress: Added `WhitneyInterval`, `CarlesonBox`, and `BoxEnergy` interfaces (no axioms) in `rh/Cert/KxiPPlus.lean`. Introduced `KxiBound` and `PPlusFromCarleson` statement forms.
  - Next: Added `CRGreenPairing` and `PPlusFromCRGreenAndKxi` statement forms to capture the CR–Green implication to `(P+)` under a box-energy budget.
  - Progress (cont.): Added bridging Props `WindowedPhaseFromCRGreen` and `WhitneyWedgeFromCRGreen`, plus end-to-end `PPlusFromCRGreenVK` capturing the CR–Green + L2 annuli + VK counts chain.
  - Progress (cont.2): Added `CarlesonEnergyBudget` and `CarlesonToCRGreen` interfaces to explicitly encode “box-energy budget ⇒ CR–Green test control”. Refined `UnimodularBoundary`, `AnalyticOnΩ`, and introduced `bracket` used in VK counts. All additions remain statement-level; no axioms introduced.
  - Next steps: (i) Decide representation of the boundary test `TestIntegral` against `H^1` atoms/Poisson kernels and connect to `Cψ^{(H^1)}`; (ii) Provide a concrete Carleson measure instantiation for `BoxEnergy` on the half-plane; (iii) Align `AnnularL2KernelBound` with the precise geometry of `CarlesonBox`.

- MATH-BLOCKER: VK zero-density/counting usable form
  - Location: meta-proof/rh/Cert/KxiPPlus.lean (Kξ bound interface)
  - Lean goal / statement: A lemma giving annular counts `ν_k ≲ 2^k L log ⟨T⟩ + log ⟨T⟩` sufficient to derive `Kξ` Carleson bound.
  - Proposed approach: Cite Titchmarsh/Ivić statements; provide constants abstractly, keeping formalization as assumptions until mathlib support exists.
  - Stub: `Cert.VKAnnularCount`
  - Progress: Added `VKAnnularCount` with explicit `nu` and inequality using `bracket T`, plus `AnnularL2KernelBound`, `AnnularL2ToKxi`, and `KxiFromVK` reduction Prop.
  - Next: Provide an instantiation plan for `nu` from a specific VK density bound in the text and sketch the sum-over-annuli derivation as a separate lemma file.

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

- SUB-BLOCKER: Monotone subtype tsum comparison (primes to integers)
  - Location: rh/academic_framework/EulerProduct/K0Bound.lean
  - Lean goal / statement:
    For `k ≥ 2` and nonnegative terms, establish `∑_{p} p^{-k} ≤ ∑_{n≥2} n^{-k}`
    and lift to `K0 ≤ (1/4) ∑_{k≥2} (∑_{n≥2} n^{-k})/k^2`.
  - Proposed approach:
    Implement a helper: for nonnegative `f : ℕ → ℝ_{ }`,
    `∑'_{p:Nat.Primes} f p ≤ ∑'_{n:ℕ} f n`. Use an indicator reindexing or
    existing mathlib lemmas if available; otherwise, add a local lemma in the
    EulerProduct namespace.
  - Stub: local helper lemma `tsum_subtype_le_total` (nonnegative)

- MATH-BLOCKER: RvM short-interval zero-count bound (VK/annular counts) for ξ
  - Location: `rh/Cert/KxiWhitney_RvM.lean`
  - Lean goal / statement: Formalize `rvM_short_interval_bound` (|{ρ : Im ρ ∈ [T−L,T+L]}| ≤ A0 + A1·L·log⟨T⟩ for Whitney L ≍ c/log⟨T⟩, large T) and derive `kxi_whitney_carleson_of_rvm : KxiBound α c` via annular Poisson L^2 summation.
  - Proposed approach: Needs mathlib-level zero-counting/density for ζ/ξ on short intervals (Riemann–von Mangoldt/Vinogradov–Korobov) and a half-plane Carleson box framework; add once available, then implement the neutralization + annular aggregation.

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
