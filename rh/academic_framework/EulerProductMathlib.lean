import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import rh.RS.SchurGlobalization

namespace RH.AcademicFramework.EPM

/-!
Euler product and zeta wrappers (mathlib-backed).
-/

open Complex
open scoped BigOperators

/-- Euler product: for Re(s) > 1, ζ(s) equals the product over primes. -/
theorem euler_product_wrapper
    (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ := by
  simpa using LSeries.eulerProduct_riemannZeta hs

/-- Nonvanishing: for Re(s) > 1, ζ(s) ≠ 0. -/
theorem zeta_nonzero_re_gt_one
    {s : ℂ} (hs : 1 < s.re) : riemannZeta s ≠ 0 := by
  simpa using riemannZeta_ne_zero_of_one_lt_re hs

/-- Nonvanishing on the boundary line: for Re(s) = 1, ζ(s) ≠ 0.
Delegates to `RS.ZetaNoZerosOnRe1FromSchur` proved via the Schur–pinch route. -/
theorem zeta_nonzero_re_eq_one
    (z : ℂ) (hz : z.re = 1) : riemannZeta z ≠ 0 := by
  exact RH.RS.ZetaNoZerosOnRe1FromSchur z hz

end RH.AcademicFramework.EPM

namespace RH.AcademicFramework.EPM

open Complex Real

/-- Exact modulus of `π^{-s/2}` in terms of the real part of `s`.
This is a light wrapper around `Complex.abs_cpow_eq_rpow_re_of_pos` specialized to `π` and the exponent `-(s/2)`.
It is useful for vertical-strip bounds where only `s.re` matters. -/
lemma abs_pi_cpow_neg_half_eq (s : ℂ) :
    Complex.abs ((Real.pi : ℂ) ^ (-(s / 2))) = Real.pi ^ (-(s.re) / 2) := by
  -- Use the generic positive-base formula and simplify the real part
  simpa [Complex.neg_re, Complex.re_div, Complex.re_ofReal] using
    (Complex.abs_cpow_eq_rpow_re_of_pos Real.pi_pos (-(s / 2)))

/-- Uniform linear-growth bound for `‖s‖` on a closed vertical strip `a ≤ Re(s) ≤ b`.
It yields `‖s‖ ≤ (|a| + |b| + 1) · (1 + |Im(s)|)`.
This is convenient for controlling polynomial factors built from `s` on strips. -/
lemma norm_le_const_mul_one_add_abs_im_of_re_mem_Icc
    {a b : ℝ} {s : ℂ} (hs : a ≤ s.re ∧ s.re ≤ b) :
    ‖s‖ ≤ (|a| + |b| + 1) * (1 + |s.im|) := by
  -- Triangle inequality with real/imag parts
  have htri : ‖s‖ ≤ |s.re| + |s.im| := by
    -- `s = (s.re : ℂ) + I * s.im`
    have : s = (s.re : ℂ) + Complex.I * s.im := by
      ext <;> simp
    calc
      ‖s‖ = ‖(s.re : ℂ) + Complex.I * s.im‖ := by simpa [this]
      _ ≤ ‖(s.re : ℂ)‖ + ‖Complex.I * s.im‖ := by simpa using norm_add_le _ _
      _ = |s.re| + |s.im| := by simp
  -- Bound the real part on the strip by a strip-dependent constant
  have hmax_abs : |s.re| ≤ |a| + |b| := by
    -- First, `max a b ≤ max |a| |b| ≤ |a| + |b|`
    have h1 : max a b ≤ max (|a|) (|b|) :=
      max_le_max (le_abs_self _) (le_abs_self _)
    have h2 : max (|a|) (|b|) ≤ |a| + |b| := by
      refine (max_le_iff.mpr ?_)
      constructor
      · exact le_add_of_nonneg_right (abs_nonneg _)
      · exact le_add_of_nonneg_left (abs_nonneg _)
    -- Now split on the sign of `s.re`
    rcases le_total (s.re) 0 with hnonpos | hnonneg
    · -- `|s.re| = -s.re ≤ -a ≤ max(-a,-b) ≤ max |a| |b| ≤ |a|+|b|`
      have habs : |s.re| = -s.re := abs_of_nonpos hnonpos
      have h3 : -s.re ≤ max (-a) (-b) :=
        le_max_of_le_left (neg_le_neg hs.1)
      have h4 : max (-a) (-b) ≤ max (|a|) (|b|) :=
        max_le_max (by simpa using (neg_le_abs a)) (by simpa using (neg_le_abs b))
      exact
        (le_trans (by simpa [habs] using h3) (le_trans h4 h2))
    · -- `|s.re| = s.re ≤ max a b ≤ |a|+|b|`
      have habs : |s.re| = s.re := abs_of_nonneg hnonneg
      have h3 : s.re ≤ max a b := le_max_of_le_right hs.2
      exact (le_trans (by simpa [habs] using h3) (le_trans h1 h2))
  -- Assemble the bound and absorb the constants into `(·)*(1+|Im s|)`
  have hnonneg_im : 0 ≤ |s.im| := abs_nonneg _
  calc
    ‖s‖ ≤ |s.re| + |s.im| := htri
    _ ≤ (|a| + |b|) + |s.im| := add_le_add_right hmax_abs _
    _ ≤ (|a| + |b| + 1) * (1 + |s.im|) := by
      -- since `|s.im| ≥ 0`, we have `X + |s.im| ≤ (X+1)*(1+|s.im|)` for any `X ≥ 0`
      have hX : 0 ≤ |a| + |b| := by exact add_nonneg (abs_nonneg _) (abs_nonneg _)
      have : (|a| + |b|) + |s.im| ≤ (|a| + |b|) + 1 + ((|a| + |b|) + 1) * |s.im| := by
        nlinarith [hnonneg_im, hX]
      simpa [left_distrib, right_distrib, one_mul, add_comm, add_left_comm, add_assoc,
             mul_add, add_mul] using this

/-- Uniform linear-growth bound for `‖1 - s‖` on a closed vertical strip `a ≤ Re(s) ≤ b`.
It yields `‖1 - s‖ ≤ (|1 - a| + |1 - b| + 1) · (1 + |Im(s)|)`.
This is obtained by applying the previous lemma to the strip for `1 - s`, which is
`1 - b ≤ Re(1 - s) ≤ 1 - a`. -/
lemma norm_one_sub_le_const_mul_one_add_abs_im_of_re_mem_Icc
    {a b : ℝ} {s : ℂ} (hs : a ≤ s.re ∧ s.re ≤ b) :
    ‖(1 : ℂ) - s‖ ≤ (|1 - a| + |1 - b| + 1) * (1 + |s.im|) := by
  -- The real part of `1 - s` lies in `Icc (1 - b) (1 - a)`
  have hstrip : (1 - b) ≤ (1 - s.re) ∧ (1 - s.re) ≤ (1 - a) := by
    constructor
    · have : s.re ≤ b := hs.2; linarith
    · have : a ≤ s.re := hs.1; linarith
  -- Apply the previous lemma to `1 - s`
  have := norm_le_const_mul_one_add_abs_im_of_re_mem_Icc (a := 1 - b) (b := 1 - a)
              (s := (1 : ℂ) - s) hstrip
  -- Rewrite `im (1 - s) = - im s` and simplify
  simpa [sub_eq_add_neg, Complex.add_im, Complex.ofReal_im, Complex.neg_im, abs_neg,
        add_comm, add_left_comm, add_assoc, one_div] using this

/-- Product bound on the strip for the polynomial factor `s(1-s)`.
It yields `‖s * (1 - s)‖ ≤ C · (1 + |Im(s)|)^2` with an explicit strip-dependent constant `C`.
This suffices for controlling power factors built from `s` on vertical strips. -/
lemma norm_mul_one_sub_le_quadratic_in_im_of_re_mem_Icc
    {a b : ℝ} {s : ℂ} (hs : a ≤ s.re ∧ s.re ≤ b) :
    ‖s * ((1 : ℂ) - s)‖ ≤ ((|a| + |b| + 1) * (|1 - a| + |1 - b| + 1)) * (1 + |s.im|)^2 := by
  have hs1 := norm_le_const_mul_one_add_abs_im_of_re_mem_Icc (a := a) (b := b) (s := s) hs
  have hs2 := norm_one_sub_le_const_mul_one_add_abs_im_of_re_mem_Icc (a := a) (b := b) (s := s) hs
  have hmul : ‖s * ((1 : ℂ) - s)‖ ≤ ‖s‖ * ‖(1 : ℂ) - s‖ := by simpa using norm_mul_le _ _
  have hnonneg : 0 ≤ 1 + |s.im| := by nlinarith [abs_nonneg s.im]
  calc
    ‖s * ((1 : ℂ) - s)‖ ≤ ‖s‖ * ‖(1 : ℂ) - s‖ := hmul
    _ ≤ ((|a| + |b| + 1) * (1 + |s.im|)) * ((|1 - a| + |1 - b| + 1) * (1 + |s.im|)) :=
      mul_le_mul hs1 hs2 (by nlinarith [abs_nonneg s.im])
        (by
          have : 0 ≤ (|1 - a| + |1 - b| + 1) * (1 + |s.im|) := by
            nlinarith [abs_nonneg (1 - a), abs_nonneg (1 - b), hnonneg]
          exact this)
    _ = ((|a| + |b| + 1) * (|1 - a| + |1 - b| + 1)) * (1 + |s.im|)^2 := by
      ring

end RH.AcademicFramework.EPM
