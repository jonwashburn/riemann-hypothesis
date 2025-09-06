import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.NumberTheory.LSeries.RiemannZeta
import rh.academic_framework.CompletedXi
import rh.academic_framework.ZetaFunctionalEquation

/-!
Zero-symmetry for completed ξ from the functional equation (statement level).

This module exposes a convenience wrapper to derive zero symmetry from an
assumed functional equation `ξ(s) = ξ(1 - s)`.

Proof sketch: If ζ satisfies a functional equation of the form
`ζ(s) = χ(s) · ζ(1−s)` and the Archimedean factor `G` linking `ξ = G·ζ`
balances as `G(s)·χ(s) = G(1−s)`, then
`ξ(s) = G(s)·ζ(s) = G(s)·χ(s)·ζ(1−s) = G(1−s)·ζ(1−s) = ξ(1−s)`.
From this equality, zeros of `ξ` are symmetric under `s ↦ 1−s`.
-/

noncomputable section

open Complex

namespace RH.AcademicFramework.CompletedXi

/-- Polynomial–completed factorization for ξ. -/
@[simp] theorem xi_eq_poly_completed (s : ℂ) :
    riemannXi s = ((1 : ℂ) / 2) * s * (1 - s) * completedRiemannZeta s := by
  classical
  by_cases hs0 : s = 0
  · -- direct zero at s = 0 with a tiny calc (no simp recursion)
    have hLeft : riemannXi s = 0 := by
      calc
        riemannXi s = G s * riemannZeta s := rfl
        _ = (((1 : ℂ) / 2) * s * (1 - s) * (Real.pi : ℂ) ^ (-(s / 2)) * Gamma (s / 2)) * riemannZeta s := rfl
        _ = 0 := by
          have : s = 0 := hs0;
          have hfac : ((1 : ℂ) / 2) * s * (1 - s) = 0 := by
            have : s = 0 := hs0; simpa [this]
          simpa [hfac, mul_left_comm, mul_assoc]
    have hRight : ((1 : ℂ) / 2) * s * (1 - s) * completedRiemannZeta s = 0 := by
      have : s = 0 := hs0
      have hfac : ((1 : ℂ) / 2) * s * (1 - s) = 0 := by simpa [this]
      simpa [hfac, mul_left_comm, mul_assoc]
    exact hLeft.trans hRight.symm
  by_cases hs1 : s = 1
  · -- direct zero at s = 1 with a tiny calc (no simp recursion)
    have hLeft : riemannXi s = 0 := by
      calc
        riemannXi s = G s * riemannZeta s := rfl
        _ = (((1 : ℂ) / 2) * s * (1 - s) * (Real.pi : ℂ) ^ (-(s / 2)) * Gamma (s / 2)) * riemannZeta s := rfl
        _ = 0 := by
          have : (1 - s) = 0 := by simpa [hs1]
          have hfac : ((1 : ℂ) / 2) * s * (1 - s) = 0 := by simpa [this]
          simpa [hfac, mul_left_comm, mul_assoc]
    have hRight : ((1 : ℂ) / 2) * s * (1 - s) * completedRiemannZeta s = 0 := by
      have : (1 - s) = 0 := by simpa [hs1]
      have hfac : ((1 : ℂ) / 2) * s * (1 - s) = 0 := by simpa [this]
      simpa [hfac, mul_left_comm, mul_assoc]
    exact hLeft.trans hRight.symm
  -- For s ≠ 0, express completedRiemannZeta via Γℝ and ζ, then cancel
  have hζ : riemannZeta s = completedRiemannZeta s / s.Gammaℝ :=
    riemannZeta_def_of_ne_zero (s := s) (by simpa using hs0)
  -- identify Gammaℝ s with the explicit (Real.pi : ℂ)^(-s/2) * Gamma(s/2)
  have hΓ : s.Gammaℝ = (Real.pi : ℂ) ^ (-(s / 2)) * Gamma (s / 2) := rfl
  have hswap : ((Real.pi : ℂ) ^ (-(s / 2)) * Gamma (s / 2)) * riemannZeta s
              = riemannZeta s * s.Gammaℝ := by
    calc
      ((Real.pi : ℂ) ^ (-(s / 2)) * Gamma (s / 2)) * riemannZeta s
          = riemannZeta s * ((Real.pi : ℂ) ^ (-(s / 2)) * Gamma (s / 2)) := by
                rw [mul_comm]
      _   = riemannZeta s * s.Gammaℝ := by
                -- rewrite to Gammaℝ s using hΓ in the correct direction
                simpa [hΓ]
  have hRG : riemannZeta s * s.Gammaℝ = completedRiemannZeta s := by
    -- avoid simp recursion; rewrite directly from hζ
    have := congrArg (fun t => t * s.Gammaℝ) hζ
    -- riemannZeta s * Γℝ s = (completedZeta s / Γℝ s) * Γℝ s = completedZeta s
    -- rearrange the RHS by definally unfolding division
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  calc
    riemannXi s
        = ((1 : ℂ) / 2) * s * (1 - s) *
          ((Real.pi : ℂ) ^ (-(s / 2)) * Gamma (s / 2)) * riemannZeta s := by
            simp only [riemannXi, G]
    _   = ((1 : ℂ) / 2) * s * (1 - s) * (riemannZeta s * s.Gammaℝ) := by
            -- use the prepared swap equality without global simp
            exact congrArg (fun t => ((1 : ℂ) / 2) * s * (1 - s) * t) hswap
    _   = ((1 : ℂ) / 2) * s * (1 - s) * completedRiemannZeta s := by
            -- replace ζ * Γℝ with completedRiemannZeta
            exact congrArg
              (fun t => ((1 : ℂ) / 2) * s * (1 - s) * t)
              hRG

/-- Zero symmetry derived from a supplied functional equation. -/
theorem zero_symmetry_from_fe
    (riemannXi : ℂ → ℂ)
    (funcEq : ∀ s, riemannXi s = riemannXi (1 - s)) :
    ∀ ρ, riemannXi ρ = 0 → riemannXi (1 - ρ) = 0 := by
  intro ρ hρ
  have hfe : riemannXi (1 - ρ) = riemannXi ρ := by simpa [eq_comm] using (funcEq ρ)
  simpa [hfe]

/-- Functional equation for `ξ`, obtained directly from the completed ζ equation. -/
@[simp] theorem xi_functional_equation : ∀ s, riemannXi s = riemannXi (1 - s) := by
  intro s
  -- expand ξ on both sides using the polynomial–completed factorization
  have h1 : riemannXi s = ((1 : ℂ) / 2) * s * (1 - s) * completedRiemannZeta s :=
    xi_eq_poly_completed (s := s)
  have h2 : riemannXi (1 - s) = ((1 : ℂ) / 2) * (1 - s) * s * completedRiemannZeta (1 - s) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using xi_eq_poly_completed (s := 1 - s)
  calc
    riemannXi s
        = ((1 : ℂ) / 2) * s * (1 - s) * completedRiemannZeta s := h1
    _   = ((1 : ℂ) / 2) * s * (1 - s) * completedRiemannZeta (1 - s) := by
            -- completed ζ FE in our restated form
            simpa using (by simpa using RH.AcademicFramework.zeta_functional_equation s)
    _   = ((1 : ℂ) / 2) * (1 - s) * s * completedRiemannZeta (1 - s) := by
            simp [mul_comm, mul_left_comm, mul_assoc]
    _   = riemannXi (1 - s) := by
            simpa using h2.symm

/-- Zero symmetry for `ξ` as a consequence of its functional equation. -/
@[simp] theorem xi_zero_symmetry : ∀ ρ, riemannXi ρ = 0 → riemannXi (1 - ρ) = 0 := by
  refine zero_symmetry_from_fe riemannXi ?hfe
  intro s; exact xi_functional_equation s

/-- Functional equation for `ξ` from a ζ functional equation and the Γ/π balance. -/
@[simp] theorem xi_functional_equation_of_zeta_balance
    (χ : ℂ → ℂ)
    (zeta_fe : ∀ s, riemannZeta s = χ s * riemannZeta (1 - s))
    (archimedean_balance : ∀ s, G s * χ s = G (1 - s)) :
    ∀ s, riemannXi s = riemannXi (1 - s) := by
  intro s
  -- expand ξ and use the ζ functional equation and the G-balance
  have hz : riemannZeta s = χ s * riemannZeta (1 - s) := zeta_fe s
  have hG : G s * χ s = G (1 - s) := archimedean_balance s
  calc
    riemannXi s
        = G s * riemannZeta s := rfl
    _   = G s * (χ s * riemannZeta (1 - s)) := by simpa [hz]
    _   = (G s * χ s) * riemannZeta (1 - s) := by
            simp [mul_comm, mul_left_comm, mul_assoc]
    _   = G (1 - s) * riemannZeta (1 - s) := by simpa [hG]
    _   = riemannXi (1 - s) := rfl

/-- Zero symmetry for `ξ` exported from ζ functional equation and Γ/π balance. -/
@[simp] theorem zero_symmetry_from_zeta_fe
    (χ : ℂ → ℂ)
    (zeta_fe : ∀ s, riemannZeta s = χ s * riemannZeta (1 - s))
    (archimedean_balance : ∀ s, G s * χ s = G (1 - s)) :
    ∀ ρ, riemannXi ρ = 0 → riemannXi (1 - ρ) = 0 := by
  -- derive ξ FE then apply the generic zero-symmetry wrapper
  refine zero_symmetry_from_fe riemannXi ?feρ
  intro s; exact xi_functional_equation_of_zeta_balance χ zeta_fe archimedean_balance s

end RH.AcademicFramework.CompletedXi
