/-!
Completed Riemann ξ function: archimedean factor `G` and `riemannXi = G · ζ`.

This module defines the completed ξ used by the proof assembly. Deeper
properties (functional equation, nonvanishing facts, etc.) are provided by
callers or other modules.
-/

import Mathlib.Analysis.SpecialFunctions.Gamma
import Mathlib.NumberTheory.LSeries.RiemannZeta
import rh.RS.SchurGlobalization

noncomputable section

open Complex

namespace RH.AcademicFramework.CompletedXi

/-- Archimedean factor for the completed Riemann ξ function. -/
def G (s : ℂ) : ℂ :=
  ((1 : ℂ) / 2) * s * (1 - s) * (Complex.pi) ^ (-(s / 2)) * Complex.Gamma (s / 2)

/-- Completed Riemann ξ function, defined by `ξ = G · ζ`. -/
def riemannXi (s : ℂ) : ℂ := G s * riemannZeta s

/-- Factorization of ξ (definition level). -/
@[simp] theorem xi_factorization (s : ℂ) : riemannXi s = G s * riemannZeta s := rfl

/-- Nonvanishing of `G` on the open right half-plane `Ω` away from `s = 1`.
    Uses that `s ≠ 0` on `Ω`, `π ≠ 0`, complex powers at nonzero base are nonzero,
    and `Γ` has no zeros; the factor `(1 - s)` is nonzero when `s ≠ 1`. -/
lemma G_nonzero_on_Ω_away_from_one : ∀ s ∈ RH.RS.Ω, s ≠ (1 : ℂ) → G s ≠ 0 := by
  intro s hs hsne1
  -- s ≠ 0 since Re s > 1/2 ⇒ Re s > 0
  have hsne0 : s ≠ 0 := by
    have hsre_pos : (0 : ℝ) < s.re := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hs
    intro h
    have : s.re = 0 := by simpa [h, Complex.zero_re]
    exact (ne_of_gt hsre_pos) this
  -- π ≠ 0 and complex power is nonzero for nonzero base
  have hpi_ne : (Complex.pi : ℂ) ≠ 0 := by
    simpa using (by exact_mod_cast (Real.pi_ne_zero))
  have hcpow_ne : (Complex.pi : ℂ) ^ (-(s / 2)) ≠ 0 := by
    simpa using Complex.cpow_ne_zero (Complex.pi) (-(s / 2)) hpi_ne
  -- Γ has no zeros
  have hGamma : Complex.Gamma (s / 2) ≠ 0 := by simpa using Complex.Gamma_ne_zero (s / 2)
  -- Assemble product
  have h1 : ((1 : ℂ) / 2) ≠ 0 := by norm_num
  have h2 : s ≠ 0 := hsne0
  have h3 : (1 - s) ≠ 0 := by
    simpa using sub_ne_zero.mpr hsne1
  have : ((1 : ℂ) / 2) * s * (1 - s) ≠ 0 := mul_ne_zero (mul_ne_zero h1 h2) h3
  have : (((1 : ℂ) / 2) * s * (1 - s)) * ((Complex.pi : ℂ) ^ (-(s / 2))) ≠ 0 :=
    mul_ne_zero this hcpow_ne
  have : ((((1 : ℂ) / 2) * s * (1 - s)) * ((Complex.pi : ℂ) ^ (-(s / 2)))) *
      Complex.Gamma (s / 2) ≠ 0 := mul_ne_zero this hGamma
  simpa [G, mul_left_comm, mul_assoc] using this

end RH.AcademicFramework.CompletedXi
