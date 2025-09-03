import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Liouville
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
  -- Use mathlib's `riemannZeta_eulerProduct_tprod` and flip the equality.
  simpa [eq_comm] using (riemannZeta_eulerProduct_tprod (s := s) hs)

/-- Nonvanishing: for Re(s) > 1, ζ(s) ≠ 0. -/
theorem zeta_nonzero_re_gt_one
    {s : ℂ} (hs : 1 < s.re) : riemannZeta s ≠ 0 := by
  simpa using riemannZeta_ne_zero_of_one_lt_re hs

-- Alias for RS delegate (kept for compatibility with callers) — to be enabled once RS exports.
-- theorem zeta_nonzero_re_eq_one
--     (z : ℂ) (hz : z.re = 1) : riemannZeta z ≠ 0 :=
--   RH.RS.ZetaNoZerosOnRe1FromSchur z hz

-- Note: boundary-line nonvanishing is delegated to the RS layer when needed.
-- We intentionally do not duplicate it here to keep this module mathlib-only.

/-- Trivial zeros: ζ vanishes at negative even integers. -/
theorem zeta_trivial_zero_neg_two_mul_nat_add_one (n : ℕ) :
    riemannZeta (-2 * (n + 1)) = 0 := by
  simpa using riemannZeta_neg_two_mul_nat_add_one n

end RH.AcademicFramework.EPM
