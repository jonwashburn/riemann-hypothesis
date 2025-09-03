import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! Modern DF‑WP helpers:

  - Use current mathlib: `HasSum.cexp`, `HasProd`/`Multipliable`.
  - Replace any use of non-existent `Complex.norm_log_one_sub_le` with
    `Complex.norm_log_one_add_le` specialized at `z ↦ -z`.
  - Keep the interface light; no axioms.
-/

namespace RH.AcademicFramework.DiagonalFredholm

noncomputable section

open Complex
open scoped BigOperators

/-- Log bound for `log(1 - z)` via the modern `log(1 + z)` inequality. -/
lemma norm_log_one_sub_le_of_lt_one {z : ℂ} (hz : ‖z‖ < (1 : ℝ)) :
    ‖Complex.log (1 - z)‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 + ‖z‖ := by
  -- Reduce to the `log(1 + w)` bound with `w = -z`.
  simpa [sub_eq_add_neg, norm_neg] using
    (Complex.norm_log_one_add_le (z := -z) (by simpa [norm_neg] using hz))

/-- A convenient half-radius variant of the previous bound. -/
lemma norm_log_one_sub_le_half {z : ℂ} (hz : ‖z‖ < (1 : ℝ) / 2) :
    ‖Complex.log (1 - z)‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 + ‖z‖ := by
  have h : (1 : ℝ) / 2 < 1 := by
    simpa using (one_half_lt_one : (1 : ℝ) / 2 < 1)
  exact norm_log_one_sub_le_of_lt_one (lt_trans hz h)

/-- Exponential turns sums into products (modern route).
If `a` is summable, then `∏ exp (a i) = exp (∑ a i)` and the product is
`Multipliable`. -/
lemma tprod_exp_of_summable {ι : Type*} [Countable ι]
    (a : ι → ℂ) (hsum : Summable a) :
    Multipliable (fun i => Complex.exp (a i)) ∧
      (∏' i, Complex.exp (a i)) = Complex.exp (∑' i, a i) := by
  -- `HasSum.cexp` yields a `HasProd` witness, from which both facts follow.
  have hsum' : HasSum a (∑' i, a i) := hsum.hasSum
  have hprod : HasProd (fun i => Complex.exp (a i)) (Complex.exp (∑' i, a i)) := by
    simpa [Function.comp] using hsum'.cexp
  exact ⟨hprod.multipliable, hprod.tprod_eq⟩

/-- Weierstrass-type bridge: from a summable log to a product identity.
If `f i ≠ 0` and `∑ log (f i)` converges, then `exp (∑ log (f i)) = ∏ f i`.
Derived from `HasSum.cexp` and `Complex.exp_log`. -/
lemma exp_tsum_eq_tprod {ι : Type*} [Countable ι]
    (f : ι → ℂ) (hne : ∀ i, f i ≠ 0)
    (hlog : Summable (fun i => Complex.log (f i))) :
    Complex.exp (∑' i, Complex.log (f i)) = ∏' i, f i := by
  have hprod : HasProd (fun i => Complex.exp (Complex.log (f i)))
      (Complex.exp (∑' i, Complex.log (f i))) := (hlog.hasSum).cexp
  calc
    Complex.exp (∑' i, Complex.log (f i))
        = ∏' i, Complex.exp (Complex.log (f i)) := by
          simpa using (hprod.tprod_eq.symm)
    _ = ∏' i, f i := by
      simp [Complex.exp_log (hne _)]

end

end RH.AcademicFramework.DiagonalFredholm
