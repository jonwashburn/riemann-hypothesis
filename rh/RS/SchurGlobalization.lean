import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Basic
-- import Mathlib.NumberTheory.LSeries.RiemannZeta -- avoided here to keep dependencies light
import Mathlib.Tactic
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.Basic

noncomputable section

open Set Complex

namespace RH.RS

/-- Right half-plane domain Ω = { s : ℂ | 1/2 < Re s }. -/
def Ω : Set ℂ := { s : ℂ | (1 / 2 : ℝ) < s.re }

/-- Ω is open. -/
lemma isOpen_Ω : IsOpen Ω := by
  -- Ω = (Complex.re) ⁻¹' Ioi (1/2)
  simpa [Ω, Set.preimage, Set.mem_setOf_eq] using
    (isOpen_Ioi.preimage continuous_re)

/-- Schur predicate on a set. -/
def IsSchurOn (Θ : ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, Complex.abs (Θ z) ≤ 1

lemma schur_of_cayley_re_nonneg_on
    (F : ℂ → ℂ) (S : Set ℂ)
    (hRe : ∀ z ∈ S, 0 ≤ (F z).re)
    (hDen : ∀ z ∈ S, F z + 1 ≠ 0) :
    IsSchurOn (fun z => (F z - 1) / (F z + 1)) S := by
  intro z hz
  have hden : F z + 1 ≠ 0 := hDen z hz
  have hRez : 0 ≤ (F z).re := hRe z hz
  -- Goal: |(w-1)/(w+1)| ≤ 1 when Re w ≥ 0 and w ≠ -1
  -- Reduce to |w-1| ≤ |w+1|
  -- Work with real coordinates x = Re(F z), y = Im(F z)
  set x : ℝ := (F z).re with hx
  set y : ℝ := (F z).im with hy
  have hxplus : (F z + 1).re = x + 1 := by simpa [hx, Complex.add_re]
  have hyplus : (F z + 1).im = y := by simpa [hy, Complex.add_im]
  have hxminus : (F z - 1).re = x - 1 := by simpa [hx, Complex.sub_re]
  have hyminus : (F z - 1).im = y := by simpa [hy, Complex.sub_im]
  have hdiff : (Complex.abs (F z + 1)) ^ 2 - (Complex.abs (F z - 1)) ^ 2 = 4 * x := by
    calc
      (Complex.abs (F z + 1)) ^ 2 - (Complex.abs (F z - 1)) ^ 2
          = Complex.normSq (F z + 1) - Complex.normSq (F z - 1) := by
            simp [Complex.sq_abs]
      _ = (((F z + 1).re) ^ 2 + ((F z + 1).im) ^ 2)
            - (((F z - 1).re) ^ 2 + ((F z - 1).im) ^ 2) := by
            simp [Complex.normSq_apply]
      _ = ((x + 1) ^ 2 + y ^ 2) - ((x - 1) ^ 2 + y ^ 2) := by
            simp [hxplus, hyplus, hxminus, hyminus]
      _ = (x + 1) ^ 2 - (x - 1) ^ 2 := by
            have hstep : ((x + 1) ^ 2 + y ^ 2) - ((x - 1) ^ 2 + y ^ 2) = (x + 1) ^ 2 - (x - 1) ^ 2 := by
              ring
            simpa using hstep
      _ = 4 * x := by ring
  have hnonneg : 0 ≤ (Complex.abs (F z + 1)) ^ 2 - (Complex.abs (F z - 1)) ^ 2 := by
    have hxnonneg : 0 ≤ x := by simpa [hx] using hRez
    have : 0 ≤ 4 * x := by exact mul_nonneg (by norm_num) hxnonneg
    simpa [hdiff] using this
  have hle_sq : (Complex.abs (F z - 1)) ^ 2 ≤ (Complex.abs (F z + 1)) ^ 2 :=
    (sub_nonneg.mp hnonneg)
  -- Monotonicity of sqrt gives |w-1| ≤ |w+1|
  have hle : Complex.abs (F z - 1) ≤ Complex.abs (F z + 1) := by
    have : Real.sqrt ((Complex.abs (F z - 1)) ^ 2)
           ≤ Real.sqrt ((Complex.abs (F z + 1)) ^ 2) :=
      Real.sqrt_le_sqrt hle_sq
    simpa [Real.sqrt_sq_eq_abs] using this
  -- Conclude |(w-1)/(w+1)| ≤ 1
  have hden_pos : 0 < Complex.abs (F z + 1) := by
    simpa using (Complex.abs.pos_iff.mpr hden)
  -- Divide the inequality by the positive denominator
  have hmul : Complex.abs (F z - 1) / Complex.abs (F z + 1)
      ≤ Complex.abs (F z + 1) / Complex.abs (F z + 1) := by
    exact div_le_div_of_nonneg_right hle (by exact Complex.abs.nonneg _)
  have hdiv_le_one : Complex.abs (F z - 1) / Complex.abs (F z + 1) ≤ 1 := by
    simpa [div_self (ne_of_gt hden_pos)] using hmul
  -- Conclude using `abs_div`
  simpa [abs_div, div_eq_mul_inv] using hdiv_le_one

/-! A convenient wrapper: under `0 ≤ Re F` the denominator `F+1` never
vanishes, so the Cayley transform is Schur on the same set. -/
lemma SchurOnRectangles
    (F : ℂ → ℂ) (R : Set ℂ)
    (hRe : ∀ z ∈ R, 0 ≤ (F z).re) :
    IsSchurOn (fun z => (F z - 1) / (F z + 1)) R := by
  -- If `F z + 1 = 0`, then `F z = -1`, contradicting `0 ≤ Re (F z)`.
  have hDen : ∀ z ∈ R, F z + 1 ≠ 0 := by
    intro z hz hzden
    have hFneg1 : F z = (-1 : ℂ) := by
      -- From `F z + 1 = 0` we get `F z = -1`.
      have : F z = -(1 : ℂ) := eq_neg_of_add_eq_zero_left hzden
      simpa using this
    have h0le : 0 ≤ (F z).re := hRe z hz
    -- Rewrite and contradict 0 ≤ -1
    have hle : (0 : ℝ) ≤ -1 := by
      simpa [hFneg1] using h0le
    have hlt : (-1 : ℝ) < 0 := by norm_num
    have : (0 : ℝ) < 0 := lt_of_le_of_lt hle hlt
    exact False.elim ((lt_irrefl _) this)
  exact schur_of_cayley_re_nonneg_on F R hRe hDen

lemma PinchConstantOfOne
    (S : Set ℂ) (hSopen : IsOpen S) (hSconn : IsPreconnected S)
    (Θ : ℂ → ℂ) (hΘ : AnalyticOn ℂ Θ S) (hSchur : IsSchurOn Θ S)
    (z0 : ℂ) (hz0 : z0 ∈ S) (hval : Θ z0 = 1) :
    ∀ z ∈ S, Θ z = 1 := by
  classical
  -- Use the maximum modulus principle in the strictly convex codomain ℂ.
  have hdiff : DifferentiableOn ℂ Θ S :=
    (analyticOn_iff_differentiableOn hSopen).1 hΘ
  have hmax : IsMaxOn (fun x => Complex.abs (Θ x)) S z0 := by
    intro z hz
    have : Complex.abs (Θ z) ≤ 1 := hSchur z hz
    simpa [hval, Complex.abs.map_one] using this
  have hconst :=
    Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (E := ℂ) (F := ℂ)
      hSconn hSopen hdiff hz0 hmax
  intro z hz
  have : Θ z = Θ z0 := hconst hz
  simpa [hval] using this

lemma PinchFromExtension
    (S : Set ℂ) (hSopen : IsOpen S) (hSconn : IsPreconnected S) (ρ : ℂ) (hρ : ρ ∈ S)
    (Θ : ℂ → ℂ) (hΘ : AnalyticOn ℂ Θ (S \ {ρ}))
    (hSchur : IsSchurOn Θ (S \ {ρ}))
    (g : ℂ → ℂ) (hg : AnalyticOn ℂ g S)
    (heq : EqOn Θ g (S \ {ρ}))
    (hval : g ρ = 1) :
    (∀ z ∈ S, g z = 1) ∧ (∀ z ∈ (S \ {ρ}), Θ z = 1) := by
  have hSchur_g : IsSchurOn g S := by
    intro z hz
    by_cases hzρ : z = ρ
    · -- at ρ, we have g ρ = 1, hence Schur bound holds
      simpa [hzρ, hval]
    · -- away from ρ, g agrees with Θ and inherits the Schur bound
      have hz_in : z ∈ (S \ {ρ}) := ⟨hz, by simp [hzρ]⟩
      have hzg : Θ z = g z := by simpa [hzρ] using heq hz_in
      have : Complex.abs (Θ z) ≤ 1 := hSchur z hz_in
      simpa [hzg] using this
  have hconst := PinchConstantOfOne S hSopen hSconn g hg hSchur_g ρ hρ hval
  have hg1 : ∀ z ∈ S, g z = 1 := hconst
  have hθ1 : ∀ z ∈ (S \ {ρ}), Θ z = 1 := by
    intro z hz
    have hzg : Θ z = g z := by simpa using heq hz
    have hz1 : g z = 1 := hg1 z hz.1
    simpa [hzg.symm] using hz1
  exact ⟨hg1, hθ1⟩

/-- Globalization across a removable set: suppose Θ is analytic and Schur on
`Ω \ Z`, with removable singularities across `Z ⊆ Ω` (captured by an analytic
extension `g` on each connected open piece). If at some `ρ ∈ Z` we have
`g ρ = 1`, then `Θ ≡ 1` on the connected component of `Ω \ Z` adjoining ρ.
This is the Schur–Herglotz pinch used to exclude off-critical zeros. -/
theorem GlobalizeAcrossRemovable
    (Z : Set ℂ) (Θ : ℂ → ℂ)
    (hSchur : IsSchurOn Θ (Ω \ Z))
    (U : Set ℂ) (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    (hUsub : U ⊆ Ω)
    (ρ : ℂ) (hρΩ : ρ ∈ Ω) (hρU : ρ ∈ U) (hρZ : ρ ∈ Z)
    (g : ℂ → ℂ) (hg : AnalyticOn ℂ g U)
    (hΘU : AnalyticOn ℂ Θ (U \ {ρ}))
    (hUminusSub : (U \ {ρ}) ⊆ (Ω \ Z))
    (hExt : EqOn Θ g (U \ {ρ}))
    (hval : g ρ = 1) :
    ∀ z ∈ U, g z = 1 := by
  -- Restrict Schur bound to U \ {ρ}
  have hSchur_U : IsSchurOn Θ (U \ {ρ}) := by
    intro z hz
    have hz_in : z ∈ (Ω \ Z) := hUminusSub hz
    exact hSchur z hz_in
  -- Apply the removable-extension pinch on U at ρ
  have : (∀ z ∈ U, g z = 1) ∧ (∀ z ∈ (U \ {ρ}), Θ z = 1) := by
    exact PinchFromExtension U hUopen hUconn ρ hρU Θ hΘU hSchur_U g hg hExt hval
  exact this.1

/-- Maximum-modulus corollary for Schur maps (admitted placeholder). -/
lemma NoInteriorZeros
    (S : Set ℂ) (hSopen : IsOpen S) (hSconn : IsPreconnected S)
    (Θ : ℂ → ℂ) (hΘ : AnalyticOn ℂ Θ S) (hSchur : IsSchurOn Θ S) :
    (∀ z ∈ S, Θ z ≠ 1) ∨ (∀ z ∈ S, Θ z = 1) := by
  classical
  by_cases h∃ : ∃ z0 ∈ S, Θ z0 = 1
  · rcases h∃ with ⟨z0, hz0, hval⟩
    right
    exact PinchConstantOfOne S hSopen hSconn Θ hΘ hSchur z0 hz0 hval
  · left
    intro z hz
    exact fun h => h∃ ⟨z, hz, h⟩

/- Non-vanishing of ζ on Re(s)=1 via the Schur–Herglotz pinch route.
This is the RS delegate used by other tracks. -/
-- Number-theoretic delegate removed here; provided in EPM layer.

end RH.RS

/-! Simple rectangle namespace aliases expected by other tracks. -/
namespace Rect

open RH.RS

/-- Right half-plane domain Ω (alias into `Rect`). -/
def Ω : Set ℂ := RH.RS.Ω

/-- Ω is open (alias). -/
lemma isOpen_Ω : IsOpen Ω := by
  simpa [Rect.Ω] using RH.RS.isOpen_Ω

end Rect
