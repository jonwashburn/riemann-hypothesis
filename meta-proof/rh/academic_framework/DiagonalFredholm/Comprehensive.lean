import rh.academic_framework.DiagonalFredholm.Operator
import rh.academic_framework.DiagonalFredholm.ProductLemmas
import rh.academic_framework.DiagonalFredholm.Determinant
import rh.academic_framework.EulerProduct.K0Bound

namespace RH.AcademicFramework.DiagonalFredholm

/-!
Comprehensive module that re-exports operator, product lemmas, and determinant pieces.

We also surface names used by downstream tracks:
- `diagDet2`, `renormE`
- `Det2IdentityReGtOne`, `Det2IdentityExtended`
-/

export RH.AcademicFramework.DiagonalFredholm (comprehensive_scaffold)
export RH.AcademicFramework.DiagonalFredholm in
  diagDet2 renormE det2_continuous det2_analytic det2_identity_Re_gt_one det2_identity_extended

theorem comprehensive_scaffold : True := by
  exact trivial

end RH.AcademicFramework.DiagonalFredholm
