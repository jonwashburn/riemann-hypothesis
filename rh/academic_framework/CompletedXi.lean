import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.NumberTheory.LSeries.RiemannZeta
import rh.RS.SchurGlobalization

/-!
Completed Riemann ξ function: archimedean factor `G` and `riemannXi = G · ζ`.

This module defines the completed ξ used by the proof assembly. Deeper
properties (functional equation, nonvanishing facts, etc.) are provided by
callers or other modules.
-/

noncomputable section

open Complex

namespace RH.AcademicFramework.CompletedXi

/-- Archimedean factor for the completed Riemann ξ function. -/
def G (s : ℂ) : ℂ :=
  ((1 : ℂ) / 2) * s * (1 - s) * (Real.pi : ℂ) ^ (-(s / 2)) * Complex.Gamma (s / 2)

/-- Completed Riemann ξ function, defined by `ξ = G · ζ`. -/
def riemannXi (s : ℂ) : ℂ := G s * riemannZeta s

/-- Factorization of ξ (definition level). -/
@[simp] theorem xi_factorization (s : ℂ) : riemannXi s = G s * riemannZeta s := rfl

end RH.AcademicFramework.CompletedXi
