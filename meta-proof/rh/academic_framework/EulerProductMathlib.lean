import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.LSeries.Nonvanishing
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
Delegates to `RS.ZetaNoZerosOnRe1FromSchur` (which currently uses the mathlib
closed-half-plane nonvanishing). -/
theorem zeta_nonzero_re_eq_one
    (z : ℂ) (hz : z.re = 1) : riemannZeta z ≠ 0 := by
  exact RH.RS.ZetaNoZerosOnRe1FromSchur z hz

end RH.AcademicFramework.EPM
