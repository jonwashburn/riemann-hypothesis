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
  -- Expand ξ and regroup to factor out the completed Λ(s)
  have hΛ : (Real.pi : ℂ) ^ (-(s / 2)) * Gamma (s / 2) * riemannZeta s =
      completedRiemannZeta s := rfl
  calc
    riemannXi s
        = (((1 : ℂ) / 2) * s * (1 - s) * (Real.pi : ℂ) ^ (-(s / 2)) * Gamma (s / 2)) * riemannZeta s := by
            simp [riemannXi, G, mul_comm, mul_left_comm, mul_assoc]
    _   = ((1 : ℂ) / 2) * s * (1 - s) * ((Real.pi : ℂ) ^ (-(s / 2)) * Gamma (s / 2) * riemannZeta s) := by
            simp [mul_comm, mul_left_comm, mul_assoc]
    _   = ((1 : ℂ) / 2) * s * (1 - s) * completedRiemannZeta s := by
            simpa [hΛ]

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
  have h2 : riemannXi (1 - s) = ((1 : ℂ) / 2) * (1 - s) * s * completedRiemannZeta (1 - s) :=
    by
      -- instantiate the lemma at (1 - s) and reorder factors
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        xi_eq_poly_completed (s := 1 - s)
  calc
    riemannXi s
        = ((1 : ℂ) / 2) * s * (1 - s) * completedRiemannZeta s := h1
    _   = ((1 : ℂ) / 2) * s * (1 - s) * completedRiemannZeta (1 - s) := by
            -- completed ζ FE
            simpa using
              congrArg (fun t => ((1 : ℂ) / 2) * s * (1 - s) * t)
                (RH.AcademicFramework.zeta_functional_equation s)
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
