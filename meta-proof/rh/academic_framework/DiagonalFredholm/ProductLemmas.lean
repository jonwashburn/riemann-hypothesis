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
theorem multipliable_of_fintype_support {ι : Type*} [Countable ι]
    {f g : ι → ℂ} (hf : Multipliable f)
    (hfin : {i | g i ≠ f i}.Finite) : Multipliable g := by
  exact hf.multipliable_of_finite_mul_support (by simpa using hfin)

end RH.AcademicFramework.DiagonalFredholm
