/-!
Zero-symmetry for completed ξ from the functional equation (statement level).

This module exposes a convenience wrapper to derive zero symmetry from an
assumed functional equation `ξ(s) = ξ(1 - s)`.
-/

import Mathlib.Analysis.Complex.Basic
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

end RH.AcademicFramework.CompletedXi
