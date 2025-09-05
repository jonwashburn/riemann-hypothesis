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

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma
import Mathlib.NumberTheory.LSeries.RiemannZeta
import ./CompletedXi

noncomputable section

open Complex

namespace RH.AcademicFramework.CompletedXi

/-- Zero symmetry derived from a supplied functional equation. -/
theorem zero_symmetry_from_fe
    (riemannXi : ℂ → ℂ)
    (funcEq : ∀ s, riemannXi s = riemannXi (1 - s)) :
    ∀ ρ, riemannXi ρ = 0 → riemannXi (1 - ρ) = 0 := by
  intro ρ hρ
  have hfe : riemannXi (1 - ρ) = riemannXi ρ := by simpa [eq_comm] using (funcEq ρ)
  simpa [hfe]

/-
Functional equation for `ξ` from a ζ functional equation and the Γ/π balance.

Suppose `ζ` satisfies `ζ(s) = χ(s) · ζ(1−s)` and the Archimedean factor `G`
balances as `G(s) · χ(s) = G(1−s)`. Then `ξ(s) = ξ(1−s)`.
-/
theorem xi_functional_equation_of_zeta_balance
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
theorem zero_symmetry_from_zeta_fe
    (χ : ℂ → ℂ)
    (zeta_fe : ∀ s, riemannZeta s = χ s * riemannZeta (1 - s))
    (archimedean_balance : ∀ s, G s * χ s = G (1 - s)) :
    ∀ ρ, riemannXi ρ = 0 → riemannXi (1 - ρ) = 0 := by
  -- derive ξ FE then apply the generic zero-symmetry wrapper
  refine zero_symmetry_from_fe riemannXi ?feρ
  intro s; exact xi_functional_equation_of_zeta_balance χ zeta_fe archimedean_balance s

end RH.AcademicFramework.CompletedXi
