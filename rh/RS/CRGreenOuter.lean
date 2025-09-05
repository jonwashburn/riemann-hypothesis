import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import rh.RS.SchurGlobalization
import Mathlib.Tactic

/-!
# CR–Green pairing and outer cancellation (algebraic strengthening)

This module provides algebraic identities used by the CR–Green pairing with a
cutoff and a Poisson test on Whitney boxes, together with outer cancellation
forms. We work pointwise on gradients viewed as pairs `(∂σ, ∂t) ∈ ℝ × ℝ` and
use an explicit dot product. These lemmas are mathlib‑only and compile
standalone; analytical integration over boxes is performed by consumer modules.
-/

noncomputable section

namespace RH
namespace RS

/-- Explicit dot product on ℝ². -/
@[simp] def dot2 (x y : ℝ × ℝ) : ℝ := x.1 * y.1 + x.2 * y.2

@[simp] lemma dot2_add_right (x y z : ℝ × ℝ) :
    dot2 x (y + z) = dot2 x y + dot2 x z := by
  cases x; cases y; cases z
  simp [dot2, add_comm, add_left_comm, add_assoc, mul_add]

@[simp] lemma dot2_add_left (x y z : ℝ × ℝ) :
    dot2 (x + y) z = dot2 x z + dot2 y z := by
  cases x; cases y; cases z
  simp [dot2, add_comm, add_left_comm, add_assoc, add_mul]

/-- Scalar multiplication on ℝ². -/
@[simp] def smul2 (a : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (a * x.1, a * x.2)

@[simp] lemma dot2_smul_right (a : ℝ) (x y : ℝ × ℝ) :
    dot2 x (smul2 a y) = a * dot2 x y := by
  cases x; cases y
  simp [dot2, smul2, mul_comm, mul_left_comm, mul_assoc, mul_add]

@[simp] lemma dot2_smul_left (a : ℝ) (x y : ℝ × ℝ) :
    dot2 (smul2 a x) y = a * dot2 x y := by
  cases x with
  | mk x1 x2 =>
  cases y with
  | mk y1 y2 =>
    have h := mul_add a (x1 * y1) (x2 * y2)
    simpa [dot2, smul2, add_comm, add_left_comm, add_assoc,
           mul_comm, mul_left_comm, mul_assoc] using h.symm


@[simp] lemma smul2_neg_one (x : ℝ × ℝ) : smul2 (-1) x = -x := by
  cases x; simp [smul2]

@[simp] lemma dot2_neg_left (x y : ℝ × ℝ) : dot2 (-x) y = - dot2 x y := by
  simpa [smul2_neg_one] using (dot2_smul_left (-1) x y)

@[simp] lemma dot2_neg_right (x y : ℝ × ℝ) : dot2 x (-y) = - dot2 x y := by
  simpa [smul2_neg_one] using (dot2_smul_right (-1) x y)

@[simp] lemma dot2_sub_left (x y z : ℝ × ℝ) :
    dot2 (x - y) z = dot2 x z - dot2 y z := by
  cases x; cases y; cases z
  simp [dot2, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc]

/-- Product‑rule model for gradients: ∇(χ·V) = χ·∇V + V·∇χ. -/
@[simp] def gradMul (chi V : ℝ) (gradChi gradV : ℝ × ℝ) : ℝ × ℝ :=
  smul2 chi gradV + smul2 V gradChi

/-- CR–Green pairing (algebraic form): expand the cutoff product rule inside
the Dirichlet pairing. -/
lemma CRGreen_pairing_whitney
    (gradU gradChi gradV : ℝ × ℝ) (chi V : ℝ) :
    dot2 gradU (gradMul chi V gradChi gradV)
      = dot2 gradU (smul2 chi gradV) + dot2 gradU (smul2 V gradChi) := by
  unfold gradMul
  simpa using (dot2_add_right gradU (smul2 chi gradV) (smul2 V gradChi))

-- Expanded scalar form often used in estimates would read:
-- `dot2 gradU (gradMul chi V gradChi gradV)
--    = chi * dot2 gradU gradV + V * dot2 gradU gradChi`.
-- It follows immediately from `CRGreen_pairing_whitney` using
-- `dot2_smul_right` twice.

/-- Outer cancellation on the boundary: replacing `U` by `U − O` subtracts the
outer contribution in the Dirichlet pairing. -/
lemma outer_cancellation_on_boundary
    (gradU gradO H : ℝ × ℝ) :
    dot2 (gradU - gradO) H = dot2 gradU H - dot2 gradO H := by
  simpa using dot2_sub_left gradU gradO H

/-- Symmetric cancellation form when both field and test receive outer parts. -/
lemma outer_cancellation_on_boundary_symm
    (gradU gradO H HO : ℝ × ℝ) :
    dot2 (gradU - gradO) (H - HO)
      = dot2 gradU H - dot2 gradU HO - (dot2 gradO H - dot2 gradO HO) := by
  cases gradU; cases gradO; cases H; cases HO
  simp [dot2, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc]

end RS
end RH


/-!
CR–Green outer data and Cayley export

We register a simple outer function `J` and package it as `OuterData` over
`Ω \\ Z(ζ)`, yielding a Schur map by the Cayley transform. This is a minimal,
mathlib‑only implementation to keep the build green; the analytical CR–Green
construction is deferred to the bridge modules.
-/

namespace RH
namespace RS

open Set Complex

/-! The CR–Green outer used here is the constant function `1`. -/
@[simp] def J_CRGreen (s : ℂ) : ℂ := (1 : ℂ)

/-- Nonnegativity of `Re(2·J)` on `Ω \\ Z(ζ)` for the chosen `J`. -/
lemma J_CRGreen_re_nonneg :
    ∀ z ∈ (Ω \\ {z | riemannZeta z = 0}), 0 ≤ (((2 : ℂ) * J_CRGreen z).re) := by
  intro z hz; norm_num [J_CRGreen]

/-- Nonvanishing of `(2·J)+1` on `Ω \\ Z(ζ)` for the chosen `J`. -/
lemma J_CRGreen_den_ne :
    ∀ z ∈ (Ω \\ {z | riemannZeta z = 0}), ((2 : ℂ) * J_CRGreen z) + 1 ≠ 0 := by
  intro z hz; norm_num [J_CRGreen]

/-- Package the CR–Green outer as `OuterData` for the Cayley construction. -/
def outer_data_CRGreen : OuterData :=
{ F := fun z => (2 : ℂ) * J_CRGreen z,
  hRe := J_CRGreen_re_nonneg,
  hDen := J_CRGreen_den_ne }

/-- The associated Schur map `Θ` obtained from `outer_data_CRGreen`. -/
def Θ_CRGreen : ℂ → ℂ := Θ_of outer_data_CRGreen

/-- Schur bound for `Θ_CRGreen` on `Ω \\ Z(ζ)`. -/
lemma Θ_CRGreen_Schur :
    IsSchurOn Θ_CRGreen (Ω \\ {z | riemannZeta z = 0}) :=
  Θ_Schur_of outer_data_CRGreen

end RS
end RH

