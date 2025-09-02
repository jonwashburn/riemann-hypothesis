import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace RH.AcademicFramework.DiagonalFredholm

/-!
Replace deprecated `tprod` lemmas with modern `HasProd`/`Multipliable` bridges.
-/

open scoped BigOperators

/-- Bridge: if `Multipliable f`, then we can reason with `HasProd`. -/
theorem hasProd_of_multipliable {ι : Type*} [Countable ι]
    {f : ι → ℂ} (hf : Multipliable f) : HasProd f (∏' i, f i) := by
  simpa using hf.hasProd

/-- Bridge: finite modification preserves multiplicability. -/
/-- Bridge: finite modification preserves multiplicability. -/
theorem multipliable_of_fintype_support {ι : Type*} [Countable ι]
    {f g : ι → ℂ} (hf : Multipliable f)
    (hfin : {i | g i ≠ f i}.Finite) : Multipliable g := by
  -- Use `Multipliable.congr` after restricting to finite difference set
  classical
  -- Define h that equals f except on a finite set where it equals g
  let h : ι → ℂ := fun i => if g i = f i then f i else g i
  have h_eq_g : h = g := by
    funext i; by_cases hg : g i = f i <;> simp [h, hg]
  -- h differs from f only on a finite set
  have hdiff : (mulSupport fun i => h i * (f i)⁻¹).Finite := by
    -- {i | h i ≠ f i} ⊆ {i | g i ≠ f i}
    refine (hfin.subset ?subset)
    intro i hi
    by_contra hg; push_neg at hg
    -- h i = f i by definition, contradicting hi
    have : h i = f i := by simp [h, hg]
    simpa [mulSupport, this] using hi
  -- f is multipliable, finite change preserves it
  have hm : Multipliable h := by
    -- use the basic lemma from mathlib on finite mulSupport
    -- rewrite h as f * (h * f⁻¹)
    have : h = fun i => f i * (h i * (f i)⁻¹) := by
      funext i; by_cases hg : g i = f i <;> simp [h, hg]
    -- multipliable_of_finite_mulSupport applies to the factor (h * f⁻¹)
    have hfinsupp : (mulSupport fun i => h i * (f i)⁻¹).Finite := hdiff
    -- f is multipliable and the correction has finite mulSupport ⇒ product is multipliable
    -- use `Multipliable.mul` after stating both parts are multipliable
    have h_corr : Multipliable (fun i => h i * (f i)⁻¹) :=
      multipliable_of_finite_mulSupport hfinsupp
    simpa [this, mul_comm, mul_left_comm, mul_assoc] using hf.mul h_corr
  simpa [h_eq_g] using hm

end RH.AcademicFramework.DiagonalFredholm
