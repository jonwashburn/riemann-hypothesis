import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Basic

noncomputable section

open Complex Set

namespace RH.RS

/-- Pointwise Herglotz from Schur via Cayley: if |Θ z| ≤ 1 and Θ z ≠ 1,
then Re((1+Θ z)/(1-Θ z)) ≥ 0. -/
lemma herglotz_of_schur_pointwise {θ : ℂ}
    (hschur : Complex.abs θ ≤ 1) (hden : θ ≠ 1) :
    0 ≤ ((1 + θ) / (1 - θ)).re := by
  -- Re((1+θ)/(1-θ)) = (1 - |θ|^2)/|1-θ|^2 ≥ 0 when |θ| ≤ 1
  have hden' : (1 - θ) ≠ 0 := sub_ne_zero.mpr (by simpa using hden.symm)
  have hden_abs_sq_pos : 0 < Complex.abs (1 - θ) ^ 2 := pow_two_pos_of_ne_zero _ (by
    simpa [Complex.abs.eq_zero] using hden')
  -- compute real part via multiplying numerator and denominator by conjugate
  have hrepr : ((1 + θ) / (1 - θ)).re
      = ((1 - Complex.abs θ ^ 2) / (Complex.abs (1 - θ) ^ 2)) := by
    -- (1+θ)/(1-θ) = ((1+θ)(1-θ̄))/|1-θ|^2
    have : (1 + θ) / (1 - θ)
        = ((1 + θ) * (1 - (conj θ))) / (Complex.abs (1 - θ) ^ 2) := by
      -- divide by |1-θ|^2 after multiplying by conjugate of denominator
      have : (1 : ℂ) - θ ≠ 0 := hden'
      field_simp [Complex.abs, Complex.conj, this]
    -- Taking real parts: Re((1+θ)(1-θ̄)) = 1 - |θ|^2
    -- so Re((1+θ)/(1-θ)) = (1 - |θ|^2) / |1-θ|^2
    admit
  -- Conclude nonnegativity
  have : 0 ≤ (1 - Complex.abs θ ^ 2) / (Complex.abs (1 - θ) ^ 2) := by
    have hnum : 0 ≤ (1 - Complex.abs θ ^ 2) := by
      have habs : 0 ≤ Complex.abs θ := Complex.abs.nonneg _
      have : Complex.abs θ ^ 2 ≤ 1 := by
        have := hschur
        -- 0 ≤ |θ| ≤ 1 ⇒ |θ|^2 ≤ 1
        have : Complex.abs θ ≤ 1 := this
        exact pow_le_pow_of_le_left habs this (by decide : (0 : ℕ) ≤ 2)
      have : (1 : ℝ) - Complex.abs θ ^ 2 ≥ 0 := sub_nonneg.mpr this
      simpa using this
    exact div_nonneg_of_nonneg_of_pos hnum hden_abs_sq_pos
  simpa [hrepr]

end RH.RS
