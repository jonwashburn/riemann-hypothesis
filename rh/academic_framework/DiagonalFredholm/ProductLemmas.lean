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

-- (Second bridge lemma intentionally omitted for stability across mathlib API drift.)

end RH.AcademicFramework.DiagonalFredholm
