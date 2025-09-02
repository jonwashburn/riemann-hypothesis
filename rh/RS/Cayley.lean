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
  have hden_abs_sq_pos : 0 < Complex.abs (1 - θ) ^ 2 := by
    have hpos : 0 < Complex.abs (1 - θ) := by
      simp [Complex.abs.pos, hden']
    have : (Complex.abs (1 - θ)) ≠ 0 := by exact ne_of_gt hpos
    simpa [pow_two, sq] using sq_pos_of_ne_zero (Complex.abs (1 - θ)) this
  -- compute real part via multiplying numerator and denominator by conjugate
  have hrepr : ((1 + θ) / (1 - θ)).re
      = ((1 - Complex.abs θ ^ 2) / (Complex.abs (1 - θ) ^ 2)) := by
    -- Standard identity by multiplying by the conjugate
    have h1 : (1 + θ) / (1 - θ) = ((1 + θ) * conj (1 - θ)) / ((1 - θ) * conj (1 - θ)) := by
      field_simp [hden']
    have hdenabs : (Complex.abs (1 - θ) ^ 2 : ℝ)
        = ((1 - θ) * conj (1 - θ)).re := by
      -- |z|^2 = z * conj z with real part equal to |z|^2
      simp [Complex.mul_conj, Complex.sq_abs]
    have hnum : ((1 + θ) * conj (1 - θ)).re = 1 - Complex.abs θ ^ 2 := by
      -- Re((1+θ)(1-conj θ)) = Re(1 - conj θ + θ - θ conj θ) = 1 - |θ|^2
      -- use algebraic identities
      have : ((1 + θ) * (1 - conj θ)).re = 1 - Complex.abs θ ^ 2 := by
        simp [mul_add, add_mul, sub_eq_add_neg, Complex.mul_conj, Complex.sq_abs,
              Complex.conj_ofReal]
      simpa [Complex.conj_sub, sub_eq_add_neg, Complex.conj_ofReal] using this
    have : ((1 + θ) / (1 - θ)).re
        = (((1 + θ) * conj (1 - θ)) / ((1 - θ) * conj (1 - θ))).re := by simpa [h1]
    simpa [Complex.realPart_div, hnum, hdenabs]
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
