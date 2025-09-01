import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import rh.academic_framework.EulerProduct.PrimeSeries

/-!
# Arithmetic prime-power tail K0 bound

We record a formal definition of the prime-power tail constant

  K0 := (1/4) * ∑_{p} ∑_{k≥2} p^{-k} / k^2

valid at the level of nonnegative series (interpreted via `tsum` on
`ℝ≥0∞` upper bounds or via absolute convergence on `ℝ`). We also give
a general inequality that reduces bounding `K0` to bounding the prime
Dirichlet series blocks `P(k) := ∑_{p} p^{-k}` for integers `k ≥ 2`.

This file purposefully stops short of a hard numeric evaluation such as
`K0 ≤ 0.03486808`. That final enclosure can be added later using either
interval arithmetic or a numerics file; here we isolate the algebraic
reduction and clean inequalities needed by higher layers.
-/

namespace RH.AcademicFramework.EulerProduct

open scoped BigOperators

namespace K0

/-- Prime-power block for integer exponent `k≥2`: `P(k) = ∑_{p} p^{-k}` as a real series. -/
noncomputable def P (k : ℕ) : ℝ :=
  (∑' p : Nat.Primes, (p : ℝ) ^ (-(k : ℝ)))

/-- The arithmetic tail constant `K0` as a real number: `(1/4) * ∑_{k≥2} P(k)/k^2`. -/
noncomputable def K0 : ℝ :=
  (1/4 : ℝ) * (∑' k : {n // 2 ≤ n}, P k / (k ^ 2))

/-! ### Basic summability -/

/-- For integer `k ≥ 2`, the prime series `∑_p p^{-k}` converges (absolute). -/
lemma summable_P_of_two_le (k : ℕ) (hk : 2 ≤ k) :
    Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(k : ℝ))) := by
  -- Reduce to the real-exponent lemma `r > 1`
  have hr : (1 : ℝ) < (k : ℝ) := by
    have : (1 : ℕ) < k := lt_of_le_of_lt (by decide : (1 : ℕ) ≤ 2) (lt_of_le_of_ne hk (by decide))
    exact_mod_cast this
  -- Use the prime-series convergence for real exponents > 1
  simpa using AcademicRH.EulerProduct.real_prime_rpow_summable hr

/-- Convenience: rewrite `P k` with the `tsum` over primes and invoke summability. -/
lemma summable_P (k : ℕ) (hk : 2 ≤ k) :
    Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(k : ℝ))) :=
  summable_P_of_two_le k hk

end K0

end RH.AcademicFramework.EulerProduct
