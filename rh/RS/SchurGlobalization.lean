import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Topology.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import rh.RS.OffZerosBridge
-- import Mathlib.NumberTheory.LSeries.RiemannZeta -- avoided here to keep dependencies light
import Mathlib.Tactic
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.Basic

noncomputable section

open Set Complex Filter

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

/-- Monotonicity of the Schur predicate under set inclusion. -/
lemma IsSchurOn.mono {Θ : ℂ → ℂ} {S T : Set ℂ}
    (h : IsSchurOn Θ S) (hTS : T ⊆ S) : IsSchurOn Θ T := by
  intro z hz; exact h z (hTS hz)

/-- Non-circular, off-zeros ζ→Schur bridge on Ω.

`hζeq_off` only asserts the ζ = Θ / N identity off the zero set of ζ (so division is legal),
and `hN_nonzero_off` only requires nonvanishing of `N` off the zeros of ζ. This avoids
encoding the target theorem (nonvanishing of ζ on Ω) in the interface. -/
structure ZetaSchurDecompositionOffZeros where
  Θ : ℂ → ℂ
  N : ℂ → ℂ
  hΘSchur : IsSchurOn Θ Ω
  hNanalytic : AnalyticOn ℂ N Ω
  hζeq_off : ∀ z ∈ (Ω \ {z | riemannZeta z = 0}), riemannZeta z = Θ z / N z
  hN_nonzero_off : ∀ z ∈ (Ω \ {z | riemannZeta z = 0}), N z ≠ 0

/-- Helper constructor for the off-zeros bridge. -/
def ZetaSchurDecompositionOffZeros.ofEqOffZeros
    {Θ N : ℂ → ℂ}
    (hΘSchur : IsSchurOn Θ Ω)
    (hNanalytic : AnalyticOn ℂ N Ω)
    (hζeq_off : ∀ z ∈ (Ω \ {z | riemannZeta z = 0}), riemannZeta z = Θ z / N z)
    (hN_nonzero_off : ∀ z ∈ (Ω \ {z | riemannZeta z = 0}), N z ≠ 0)
    : ZetaSchurDecompositionOffZeros :=
  { Θ := Θ, N := N, hΘSchur := hΘSchur, hNanalytic := hNanalytic
    , hζeq_off := hζeq_off, hN_nonzero_off := hN_nonzero_off }



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
  have hxplus : (F z + 1).re = x + 1 := by simpa [hx] using (by simp : (F z + 1).re = (F z).re + 1)
  have hyplus : (F z + 1).im = y := by simpa [hy] using (by simp : (F z + 1).im = (F z).im)
  have hxminus : (F z - 1).re = x - 1 := by simpa [hx] using (by simp : (F z - 1).re = (F z).re - 1)
  have hyminus : (F z - 1).im = y := by simpa [hy] using (by simp : (F z - 1).im = (F z).im)
  have hdiff : (Complex.abs (F z + 1)) ^ 2 - (Complex.abs (F z - 1)) ^ 2 = 4 * x := by
    have h1s : (Complex.abs (F z + 1)) ^ 2 = (x + 1) * (x + 1) + y * y := by
      simpa [Complex.normSq_apply, hxplus, hyplus, pow_two] using (Complex.sq_abs (F z + 1))
    have h2s : (Complex.abs (F z - 1)) ^ 2 = (x - 1) * (x - 1) + y * y := by
      simpa [Complex.normSq_apply, hxminus, hyminus, pow_two] using (Complex.sq_abs (F z - 1))
    have : ((x + 1) * (x + 1) + y * y) - ((x - 1) * (x - 1) + y * y) = 4 * x := by
      ring
    simpa [h1s, h2s]
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

/-! A small convenience: the Cayley transform. -/

/-- Cayley transform sending the right half-plane to the unit disc. -/
def cayley (F : ℂ → ℂ) : ℂ → ℂ := fun z => (F z - 1) / (F z + 1)

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

/-- No off‑critical zeros from a Schur bound off the zero set together with
local removable extensions that pin to `1` and are not identically `1`.

If `Θ` is Schur on `Ω \ Z(ζ)` and, for every putative zero `ρ ∈ Ω`, there is an
open, preconnected `U ⊆ Ω` with `(U ∩ Z(ζ)) = {ρ}` and an analytic extension
`g` of `Θ` across `ρ` with `g ρ = 1` that is not identically `1` on `U`, then
`ζ` has no zeros in `Ω`.
-/
theorem no_offcritical_zeros_from_schur
    (Θ : ℂ → ℂ)
    (hSchur : IsSchurOn Θ (Ω \ {z | riemannZeta z = 0}))
    (assign : ∀ ρ, ρ ∈ Ω → riemannZeta ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
          EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
    : ∀ ρ ∈ Ω, riemannZeta ρ ≠ 0 := by
  intro ρ hρΩ hζρ
  rcases assign ρ hρΩ hζρ with
    ⟨U, hUopen, hUconn, hUsub, hρU, hUZeq, g, hg, hΘU, hExt, hval, z, hzU, hgzne⟩
  -- Apply globalization across Z(ζ) to get g ≡ 1 on U
  have hρZ : ρ ∈ ({z | riemannZeta z = 0} : Set ℂ) := by
    simpa [Set.mem_setOf_eq] using hζρ
  have hUminusSub : (U \ {ρ}) ⊆ (Ω \ ({z | riemannZeta z = 0})) := by
    intro x hx
    have hxU : x ∈ U := hx.1
    have hxNe : x ≠ ρ := by
      intro h; exact hx.2 (by simpa [h])
    have hxNotZ : x ∉ ({z | riemannZeta z = 0} : Set ℂ) := by
      intro hxZ
      have hxInCap : x ∈ (U ∩ {z | riemannZeta z = 0}) := ⟨hxU, hxZ⟩
      have hxSingleton : x ∈ ({ρ} : Set ℂ) := by
        -- from x ∈ U ∩ Z and U ∩ Z = {ρ}
        simpa [hUZeq] using hxInCap
      have : x = ρ := by
        simpa using hxSingleton
      exact hxNe this
    exact ⟨hUsub hxU, hxNotZ⟩
  have hAllOne : ∀ w ∈ U, g w = 1 :=
    GlobalizeAcrossRemovable ({z | riemannZeta z = 0}) Θ hSchur
      U hUopen hUconn hUsub ρ hρΩ hρU hρZ g hg hΘU hUminusSub hExt hval
  -- Contradiction: g must be identically 1 on U
  have : g z = 1 := hAllOne z hzU
  exact (hgzne this)

/-- Maximum-modulus corollary for Schur maps. -/
lemma NoInteriorZeros
    (S : Set ℂ) (hSopen : IsOpen S) (hSconn : IsPreconnected S)
    (Θ : ℂ → ℂ) (hΘ : AnalyticOn ℂ Θ S) (hSchur : IsSchurOn Θ S) :
    (∀ z ∈ S, Θ z ≠ 1) ∨ (∀ z ∈ S, Θ z = 1) := by
  classical
  by_cases hExists : ∃ z0 ∈ S, Θ z0 = 1
  · rcases hExists with ⟨z0, hz0, hval⟩
    right
    exact PinchConstantOfOne S hSopen hSconn Θ hΘ hSchur z0 hz0 hval
  · left
    intro z hz
    exact fun h => hExists ⟨z, hz, h⟩

/-- Prototype interface for the ζ→Θ/N bridge and RS export shape (statement-only).
We do not construct Θ or N here. This provides the target interface used by
the EPM delegate once the bridge is available. -/
structure ZetaSchurDecomposition where
  Θ : ℂ → ℂ
  N : ℂ → ℂ
  hΘSchur : IsSchurOn Θ Ω
  hNanalytic : AnalyticOn ℂ N Ω
  hNnonzero : ∀ z ∈ Ω, N z ≠ 0
  hζeq : ∀ z ∈ Ω, riemannZeta z = Θ z / N z

/-- Statement-only alias for the boundary-line nonvanishing target. -/
def ZetaNoZerosOnRe1FromSchur_Statement (z : ℂ) (hz : z.re = 1)
    (w : ZetaSchurDecomposition) : Prop :=
  riemannZeta z ≠ 0

/-- Local pinch-to-nonvanishing: given a ζ→Θ/N decomposition `w` on `Ω`,
an open, preconnected `U ⊆ Ω`, a point `ρ ∈ U`, and an analytic extension
`g` on `U` that agrees with `Θ` on `U \ {ρ}` and takes the value `1` at `ρ`,
then ζ has no zeros at any `z ∈ U \ {ρ}`. This packages the removable-pinching
argument in a form usable by the eventual bridge. -/
theorem zeta_nonzero_from_local_pinch
    (w : ZetaSchurDecomposition)
    (U : Set ℂ) (hUopen : IsOpen U) (hUconn : IsPreconnected U) (hUsub : U ⊆ Ω)
    (ρ : ℂ) (hρU : ρ ∈ U)
    (z : ℂ) (hzUdiff : z ∈ (U \ {ρ}))
    (hΘU : AnalyticOn ℂ w.Θ (U \ {ρ}))
    (g : ℂ → ℂ) (hg : AnalyticOn ℂ g U)
    (hExt : EqOn w.Θ g (U \ {ρ})) (hval : g ρ = 1) :
    riemannZeta z ≠ 0 := by
  -- Restrict Schur bound to `Ω \ {ρ}`
  have hSchur_restrict : IsSchurOn w.Θ (Ω \ {ρ}) := by
    intro ζ hζ
    exact w.hΘSchur ζ hζ.1
  -- `z ∈ Ω` since `z ∈ U` and `U ⊆ Ω`
  have hzΩ : z ∈ Ω := hUsub hzUdiff.1
  -- Globalize across the removable point to get `g ≡ 1` on `U`
  have hg_one : ∀ ζ ∈ U, g ζ = 1 := by
    have hUminusSub : (U \ {ρ}) ⊆ (Ω \ {ρ}) := by
      intro ζ hζ
      exact ⟨hUsub hζ.1, hζ.2⟩
    have hρΩ : ρ ∈ Ω := hUsub hρU
    have hρZ : ρ ∈ ({ρ} : Set ℂ) := by simp
    exact GlobalizeAcrossRemovable ({ρ} : Set ℂ) w.Θ hSchur_restrict
      U hUopen hUconn hUsub ρ hρΩ hρU hρZ g hg hΘU hUminusSub hExt hval
  -- On `U \ {ρ}`, `Θ = g = 1`
  have hΘ_eq_g : w.Θ z = g z := by
    have hz_in : z ∈ (U \ {ρ}) := hzUdiff
    exact (hExt hz_in)
  have hgz1 : g z = 1 := hg_one z hzUdiff.1
  have hΘz1 : w.Θ z = 1 := by simpa [hΘ_eq_g] using hgz1
  -- Convert decomposition to `ζ z = 1 / N z`
  have hζ_div : riemannZeta z = 1 / w.N z := by
    simpa [hΘz1] using (w.hζeq z hzΩ)
  -- Use `N z ≠ 0` to conclude nonvanishing of ζ
  have hNnz : w.N z ≠ 0 := w.hNnonzero z hzΩ
  intro hz0
  -- Multiply `0 = 1 / N z` by `N z` (nonzero) to get a contradiction
  have : (0 : ℂ) = 1 / w.N z := by simpa [hζ_div] using hz0.symm
  have : (0 : ℂ) * w.N z = (1 / w.N z) * w.N z := congrArg (fun t => t * w.N z) this
  have hcontr : (0 : ℂ) = 1 := by
    simpa [zero_mul, one_div, hNnz] using this
  exact (zero_ne_one : (0 : ℂ) ≠ 1) hcontr

/-- Local bridge data at a point `ρ` inside an open set `U ⊆ Ω` sufficient to
drive the Schur–pinch nonvanishing argument. -/
structure LocalPinchData (w : ZetaSchurDecomposition) (U : Set ℂ) (ρ : ℂ) where
  hUopen : IsOpen U
  hUconn : IsPreconnected U
  hUsub : U ⊆ Ω
  hρU : ρ ∈ U
  hΘU : AnalyticOn ℂ w.Θ (U \ {ρ})
  g : ℂ → ℂ
  hg : AnalyticOn ℂ g U
  hExt : EqOn w.Θ g (U \ {ρ})
  hval : g ρ = 1

/-- Generalized local pinch data across a removable set `Z ⊆ Ω`.
This variant allows `U` to contain possibly many removable points, packaged as `Z`.
One marked point `ρ ∈ Z ∩ U` carries the normalization `g ρ = 1`. -/
structure LocalPinchDataZ (w : ZetaSchurDecomposition) (U Z : Set ℂ) where
  hUopen : IsOpen U
  hUconn : IsPreconnected U
  hUsub : U ⊆ Ω
  hZsub : Z ⊆ Ω
  hΘU : AnalyticOn ℂ w.Θ (U \ Z)
  g : ℂ → ℂ
  hg : AnalyticOn ℂ g U
  hExt : EqOn w.Θ g (U \ Z)
  ρ : ℂ
  hρU : ρ ∈ U
  hρZ : ρ ∈ Z
  hval : g ρ = 1
  hZcapU_singleton : (U ∩ Z) = {ρ}

/-- Off-zeros local data variant: carry Θ, N and the off-zeros identities locally on `U \ Z`.
Used to derive ζ(z) ≠ 0 at `z ∈ U \ Z` without requiring a global strong decomposition. -/
structure LocalPinchDataZOff (Θ N : ℂ → ℂ) (U Z : Set ℂ) where
  hUopen : IsOpen U
  hUconn : IsPreconnected U
  hUsub : U ⊆ Ω
  hZsub : Z ⊆ Ω
  hΘU : AnalyticOn ℂ Θ (U \ Z)
  g : ℂ → ℂ
  hg : AnalyticOn ℂ g U
  hExt : EqOn Θ g (U \ Z)
  ρ : ℂ
  hρU : ρ ∈ U
  hρZ : ρ ∈ Z
  hval : g ρ = 1
  hZcapU_singleton : (U ∩ Z) = {ρ}
  hζeq_off : ∀ z ∈ (U \ Z), riemannZeta z = Θ z / N z
  hNnonzero_off : ∀ z ∈ (U \ Z), N z ≠ 0

/-- Boundary-line globalization: if for every `z` with `Re z = 1` there is
local pinch data assigning an open `U ⊆ Ω`, a point `ρ ∈ U`, and an analytic
extension `g` across `ρ` with value `1` at `ρ` that agrees with `Θ` on
`U \\ {ρ}`, then `ζ z ≠ 0` on the entire boundary line `Re = 1`.

This uses `zeta_nonzero_from_local_pinch` pointwise with the supplied local
data; the existence of such data is the (future) ζ→Θ/N bridge responsibility. -/
theorem zeta_nonzero_on_Re1_from_local_bridges
    (w : ZetaSchurDecomposition)
    (assign : ∀ z, z.re = 1 → ∃ (U : Set ℂ) (ρ : ℂ) (data : LocalPinchData w U ρ), z ∈ (U \ {ρ})) :
    ∀ z, z.re = 1 → riemannZeta z ≠ 0 := by
  intro z hz
  rcases assign z hz with ⟨U, ρ, data, hzUdiff⟩
  rcases data with ⟨hUopen, hUconn, hUsub, hρU, hΘU, g, hg, hExt, hval⟩
  exact zeta_nonzero_from_local_pinch w U hUopen hUconn hUsub ρ hρU z hzUdiff hΘU g hg hExt hval

/-- Local nonvanishing from off-zeros data. Requires a global Schur bound for Θ on Ω
and the local off-zeros identities on `U \ Z`. -/
theorem zeta_nonzero_from_local_pinch_Z_off
    (Θ N : ℂ → ℂ)
    (hΘSchur : IsSchurOn Θ Ω)
    {U Z : Set ℂ} (data : LocalPinchDataZOff Θ N U Z)
    {z : ℂ} (hzUdiff : z ∈ (U \ Z)) :
    riemannZeta z ≠ 0 := by
  -- Pinch to get g ≡ 1 on U using |g| ≤ 1 on U \ {ρ}
  have hg_one : ∀ ζ ∈ U, data.g ζ = 1 := by
    have hle : ∀ ζ ∈ (U \ {data.ρ}), Complex.abs (data.g ζ) ≤ 1 := by
      intro ζ hζ
      rcases hζ with ⟨hζU, hζne⟩
      have hζnotZ : ζ ∉ Z := by
        intro hzZ
        have : ζ ∈ (U ∩ Z) := ⟨hζU, hzZ⟩
        have : ζ ∈ ({data.ρ} : Set ℂ) := by simpa [data.hZcapU_singleton] using this
        have : ζ = data.ρ := by simpa using this
        exact hζne this
      have hζUZ : ζ ∈ (U \ Z) := ⟨hζU, hζnotZ⟩
      have hΩ : ζ ∈ Ω := data.hUsub hζU
      have hΘle : Complex.abs (Θ ζ) ≤ 1 := hΘSchur ζ hΩ
      have hΘeqg : Θ ζ = data.g ζ := by simpa using data.hExt hζUZ
      simpa [hΘeqg] using hΘle
    -- Build Schur bound for g on U and pinch
    have hSchurU : IsSchurOn data.g U := by
      intro ξ hξU
      by_cases hξρ : ξ = data.ρ
      · simpa [hξρ, data.hval]
      · have hξ' : ξ ∈ (U \ {data.ρ}) := ⟨hξU, by simp [hξρ]⟩
        exact hle ξ hξ'
    exact PinchConstantOfOne U data.hUopen data.hUconn data.g data.hg hSchurU data.ρ data.hρU data.hval
  -- Hence Θ = 1 on U \ Z
  have hΘz1 : Θ z = 1 := by
    have hzU : z ∈ U := hzUdiff.1
    have hz1 : data.g z = 1 := hg_one z hzU
    have hΘ_eq_g : Θ z = data.g z := data.hExt hzUdiff
    simpa [hΘ_eq_g] using hz1
  -- Use local off-zeros identity at z
  have hζ_div : riemannZeta z = 1 / N z := by simpa [hΘz1] using (data.hζeq_off z hzUdiff)
  have hNnz : N z ≠ 0 := data.hNnonzero_off z hzUdiff
  intro hz0
  have : (0 : ℂ) = 1 / N z := by simpa [hζ_div] using hz0.symm
  have : (0 : ℂ) * N z = (1 / N z) * N z := congrArg (fun t => t * N z) this
  have hcontr : (0 : ℂ) = 1 := by simpa [zero_mul, one_div, hNnz] using this
  exact (zero_ne_one : (0 : ℂ) ≠ 1) hcontr

/-- Boundary-line nonvanishing from off-zeros local assignments. -/
theorem zeta_nonzero_on_Re1_from_local_bridges_Z_off
    (Θ N : ℂ → ℂ)
    (hΘSchur : IsSchurOn Θ Ω)
    (assign : ∀ z, z.re = 1 → ∃ (U Z : Set ℂ)
      (data : LocalPinchDataZOff Θ N U Z), z ∈ (U \ Z)) :
    ∀ z, z.re = 1 → riemannZeta z ≠ 0 := by
      intro z hz
      rcases assign z hz with ⟨U, Z, data, hzUdiff⟩
      exact zeta_nonzero_from_local_pinch_Z_off Θ N hΘSchur data hzUdiff

/-- RS export wrapper: boundary nonvanishing from an off-zeros boundary assignment. -/
structure OffZerosBoundaryAssignment where
  Θ : ℂ → ℂ
  N : ℂ → ℂ
  hΘSchur : IsSchurOn Θ Ω
  assign : ∀ z, z.re = 1 → ∃ (U Z : Set ℂ) (data : LocalPinchDataZOff Θ N U Z), z ∈ (U \ Z)

theorem ZetaNoZerosOnRe1_from_offZerosAssignment
    (A : OffZerosBoundaryAssignment) :
    ∀ z, z.re = 1 → riemannZeta z ≠ 0 :=
  zeta_nonzero_on_Re1_from_local_bridges_Z_off A.Θ A.N A.hΘSchur A.assign

-- (explicit off-zeros convenience theorem removed; use `ZetaNoZerosOnRe1_from_offZerosDecomp`
-- together with `OffZerosBoundaryAssignment.ofPinnedRemovable_noZetaZeros` instead.)

/-- Adapter (GLOBALIZE): from an off-zeros boundary assignment provided by the
bridge agent, we immediately obtain both the global Schur bound on `Θ` over `Ω`
and nonvanishing of `ζ` on the boundary line `Re = 1` by calling
`ZetaNoZerosOnRe1_from_offZerosAssignment`.

This is the short end-to-end hook requested: Agent A supplies
`OffZerosBoundaryAssignment`; this lemma exposes `(IsSchurOn A.Θ Ω)` (already
contained in the assignment) and boundary nonvanishing for `ζ` without adding
any further axioms. -/
theorem Globalize_from_OffZerosBoundaryAssignment
    (A : OffZerosBoundaryAssignment) :
    IsSchurOn A.Θ Ω ∧ (∀ z, z.re = 1 → riemannZeta z ≠ 0) := by
  exact ⟨A.hΘSchur, ZetaNoZerosOnRe1_from_offZerosAssignment A⟩

/-- Pure statement-level hypothesis for off-zeros boundary assignment: Θ is Schur
on Ω and for each boundary point z there exist U, Z and local off-zeros data with
z ∈ U \ Z (exactly the shape needed by `LocalPinchDataZOff`). -/
def OffZerosBoundaryHypothesis (Θ N : ℂ → ℂ) : Prop :=
  IsSchurOn Θ Ω ∧ (∀ z, z.re = 1 → ∃ (U Z : Set ℂ)
    (data : LocalPinchDataZOff Θ N U Z), z ∈ (U \ Z))

/-- From the off-zeros boundary hypothesis, conclude ζ ≠ 0 on Re = 1. -/
theorem ZetaNoZerosOnRe1_from_offZerosAssignmentStatement
    {Θ N : ℂ → ℂ}
    (h : OffZerosBoundaryHypothesis Θ N) :
    ∀ z, z.re = 1 → riemannZeta z ≠ 0 := by
  rcases h with ⟨hΘSchur, assign⟩
  exact zeta_nonzero_on_Re1_from_local_bridges_Z_off Θ N hΘSchur assign

/-- Adapter: build an `OffZerosBoundaryAssignment` from a concrete off-zeros
decomposition together with a boundary assignment that produces local
`LocalPinchDataZOff` for each boundary point. This keeps the packaging
inside RS uniform without re-proving the assignment itself here. -/
def OffZerosBoundaryAssignment.ofDecomp
    {zf ξf : ℂ → ℂ}
    (w : RH.RS.OffZeros.ZetaSchurDecompositionOffZeros zf ξf)
    (hΘSchur : IsSchurOn w.Θ Ω)
    (assign : ∀ z, z.re = 1 →
      ∃ (U Z : Set ℂ) (data : LocalPinchDataZOff w.Θ w.N U Z), z ∈ (U \ Z))
    : OffZerosBoundaryAssignment :=
{ Θ := w.Θ,
  N := w.N,
  hΘSchur := hΘSchur,
  assign := assign }

/-- Local nonvanishing using generalized removable set data. -/
theorem zeta_nonzero_from_local_pinch_Z
    (w : ZetaSchurDecomposition)
    (U Z : Set ℂ)
    (hUopen : IsOpen U) (hUconn : IsPreconnected U) (hUsub : U ⊆ Ω)
    (hZsub : Z ⊆ Ω)
    (ρ : ℂ) (hρU : ρ ∈ U) (hρZ : ρ ∈ Z)
    (hZcapU_singleton : (U ∩ Z) = {ρ})
    (z : ℂ) (hzUdiff : z ∈ (U \ Z))
    (hΘU : AnalyticOn ℂ w.Θ (U \ Z))
    (g : ℂ → ℂ) (hg : AnalyticOn ℂ g U)
    (hExt : EqOn w.Θ g (U \ Z)) (hval : g ρ = 1) :
    riemannZeta z ≠ 0 := by
  -- Pinch to get g ≡ 1 on U using |g| ≤ 1 on U \ {ρ}
  have hg_one : ∀ ζ ∈ U, g ζ = 1 := by
    have hle : ∀ ζ ∈ (U \ {ρ}), Complex.abs (g ζ) ≤ 1 := by
      intro ζ hζ
      rcases hζ with ⟨hζU, hζne⟩
      -- If ζ ∈ Z then ζ ∈ U ∩ Z = {ρ}, contradicting ζ ≠ ρ
      have hζUZ : ζ ∈ (U \ Z) := by
        constructor
        · exact hζU
        · intro hzZ; exact hζne (by
            have : ζ ∈ (U ∩ Z) := ⟨hζU, hzZ⟩
            have : ζ ∈ ({ρ} : Set ℂ) := by simpa [hZcapU_singleton] using this
            simpa using this)
      have hΩ : ζ ∈ Ω := hUsub hζU
      have hΘle : Complex.abs (w.Θ ζ) ≤ 1 := w.hΘSchur ζ hΩ
      have hΘeqg : w.Θ ζ = g ζ := by simpa using hExt hζUZ
      simpa [hΘeqg] using hΘle
    -- Build Schur bound for g on U and pinch
    have hSchurU : IsSchurOn g U := by
      intro ξ hξU
      by_cases hξρ : ξ = ρ
      · simpa [hξρ, hval]
      · have hξ' : ξ ∈ (U \ {ρ}) := ⟨hξU, by simp [hξρ]⟩
        exact hle ξ hξ'
    exact PinchConstantOfOne U hUopen hUconn g hg hSchurU ρ hρU hval
  -- Hence Θ = 1 on U \ Z
  have hΘz1 : w.Θ z = 1 := by
    have hzU : z ∈ U := hzUdiff.1
    have hz1 : g z = 1 := hg_one z hzU
    have hΘ_eq_g : w.Θ z = g z := hExt hzUdiff
    simpa [hΘ_eq_g] using hz1
  -- Convert decomposition to ζ z = 1 / N z and conclude
  have hzΩ : z ∈ Ω := hUsub hzUdiff.1
  have hζ_div : riemannZeta z = 1 / w.N z := by simpa [hΘz1] using (w.hζeq z hzΩ)
  have hNnz : w.N z ≠ 0 := w.hNnonzero z hzΩ
  intro hz0
  have : (0 : ℂ) = 1 / w.N z := by simpa [hζ_div] using hz0.symm
  have : (0 : ℂ) * w.N z = (1 / w.N z) * w.N z := congrArg (fun t => t * w.N z) this
  have hcontr : (0 : ℂ) = 1 := by simpa [zero_mul, one_div, hNnz] using this
  exact (zero_ne_one : (0 : ℂ) ≠ 1) hcontr

/-! Off-zeros assignment ⇒ boundary nonvanishing (Z-variant).

We now thread the generalized removable-set local pinch through the boundary:
given, for every `z` with `Re z = 1`, a choice of open `U ⊆ Ω`, a removable
set `Z ⊆ Ω`, and local extension data as in `LocalPinchDataZ` with
`z ∈ U \ Z`, we conclude `ζ z ≠ 0`. -/

/-- Boundary-line globalization using `LocalPinchDataZ` at each boundary point. -/
theorem zeta_nonzero_on_Re1_from_local_bridges_Z
    (w : ZetaSchurDecomposition)
    (assignZ : ∀ z, z.re = 1 → ∃ (U Z : Set ℂ) (data : LocalPinchDataZ w U Z), z ∈ (U \ Z)) :
    ∀ z, z.re = 1 → riemannZeta z ≠ 0 := by
  intro z hz
  rcases assignZ z hz with ⟨U, Z, data, hzUdiff⟩
  rcases data with ⟨hUopen, hUconn, hUsub, hZsub, hΘU, g, hg, hExt, ρ, hρU, hρZ, hval, hZcapU_singleton⟩
  exact zeta_nonzero_from_local_pinch_Z w U Z hUopen hUconn hUsub hZsub ρ hρU hρZ hZcapU_singleton z hzUdiff hΘU g hg hExt hval

/-- Local-assignment packaging (Z-variant): for each boundary point, provide
an open set `U ⊆ Ω`, a removable set `Z ⊆ Ω`, and local extension data. -/
structure BoundaryLocalPinchAssignmentZ (w : ZetaSchurDecomposition) where
  choose : ∀ z, z.re = 1 → ∃ (U Z : Set ℂ) (data : LocalPinchDataZ w U Z), z ∈ (U \ Z)

/-- Boundary nonvanishing from a Z-assignment (convenience wrapper). -/
theorem ZetaNoZerosOnRe1FromSchur_from_localAssignmentZ
    {w : ZetaSchurDecomposition}
    (A : BoundaryLocalPinchAssignmentZ w) :
    ∀ z, z.re = 1 → riemannZeta z ≠ 0 :=
  zeta_nonzero_on_Re1_from_local_bridges_Z w A.choose

/-- Statement-level wrapper from a Z-assignment. -/
theorem ZetaNoZerosOnRe1FromSchur_Statement_from_localAssignmentZ
    {w : ZetaSchurDecomposition}
    (A : BoundaryLocalPinchAssignmentZ w) (z : ℂ) (hz : z.re = 1) :
    ZetaNoZerosOnRe1FromSchur_Statement z hz w :=
  ZetaNoZerosOnRe1FromSchur_from_localAssignmentZ A z hz

/-- A boundary bridge (Z-variant) packages a ζ→Θ/N decomposition along with
local pinch data over removable sets for every boundary point `Re = 1`. -/
structure ZetaSchurBoundaryBridgeZ where
  w : ZetaSchurDecomposition
  assignZ : ∀ z, z.re = 1 → ∃ (U Z : Set ℂ) (data : LocalPinchDataZ w U Z), z ∈ (U \ Z)

/-- Global nonvanishing from a Z-bridge. -/
theorem ZetaNoZerosOnRe1FromSchur_from_bridgeZ
    (B : ZetaSchurBoundaryBridgeZ) :
    ∀ z, z.re = 1 → riemannZeta z ≠ 0 :=
  zeta_nonzero_on_Re1_from_local_bridges_Z B.w B.assignZ

/-- A boundary bridge packages a ζ→Θ/N decomposition along with local pinch data
for every boundary point `Re = 1`. When provided, it implies global nonvanishing
on the boundary via the local pinch lemma. -/
structure ZetaSchurBoundaryBridge where
  w : ZetaSchurDecomposition
  assign : ∀ z, z.re = 1 → ∃ (U : Set ℂ) (ρ : ℂ) (data : LocalPinchData w U ρ), z ∈ (U \ {ρ})

/-- Global nonvanishing from a boundary bridge. -/
theorem ZetaNoZerosOnRe1FromSchur_from_bridge
    (B : ZetaSchurBoundaryBridge) :
    ∀ z, z.re = 1 → riemannZeta z ≠ 0 :=
  zeta_nonzero_on_Re1_from_local_bridges B.w B.assign

/-- RS export: global nonvanishing on `Re = 1` from a provided boundary bridge. -/
theorem ZetaNoZerosOnRe1FromSchur
    (B : ZetaSchurBoundaryBridge) :
    ∀ z, z.re = 1 → riemannZeta z ≠ 0 :=
  ZetaNoZerosOnRe1FromSchur_from_bridge B

/-- Pointwise RS export shape from a boundary bridge, matching the existing
statement-level API surface. -/
theorem ZetaNoZerosOnRe1FromSchur_Statement_from_bridge
    (B : ZetaSchurBoundaryBridge) (z : ℂ) (hz : z.re = 1) :
    ZetaNoZerosOnRe1FromSchur_Statement z hz B.w :=
  (ZetaNoZerosOnRe1FromSchur_from_bridge B z hz)

/-- Prop-level bridge statement: existence of a ζ→Θ/N decomposition together with
local pinch data for each boundary point. This avoids constructing a concrete
bridge object while enabling global nonvanishing conclusions. -/
def ZetaSchurBridgeStatement : Prop :=
  ∃ (w : ZetaSchurDecomposition),
    ∀ z, z.re = 1 → ∃ (U : Set ℂ) (ρ : ℂ) (data : LocalPinchData w U ρ), z ∈ (U \ {ρ})

/-- Global boundary nonvanishing from the Prop-level bridge statement. -/
theorem ZetaNoZerosOnRe1FromSchur_from_bridgeStatement
    (h : ZetaSchurBridgeStatement) :
    ∀ z, z.re = 1 → riemannZeta z ≠ 0 := by
  rcases h with ⟨w, assign⟩
  exact zeta_nonzero_on_Re1_from_local_bridges w assign

/-- Local-assignment packaging: for each boundary point, provide the open set,
pinch point, and removable extension data. This is exactly the data required
to build a `ZetaSchurBoundaryBridge`. -/
structure BoundaryLocalPinchAssignment (w : ZetaSchurDecomposition) where
  choose : ∀ z, z.re = 1 → ∃ (U : Set ℂ) (ρ : ℂ) (data : LocalPinchData w U ρ), z ∈ (U \ {ρ})

/-- Build a boundary bridge from a local assignment. -/
def bridge_of_localAssignment
    {w : ZetaSchurDecomposition}
    (A : BoundaryLocalPinchAssignment w) : ZetaSchurBoundaryBridge :=
  { w := w, assign := A.choose }

/-- Nonvanishing on the boundary from a local assignment (convenience wrapper). -/
theorem ZetaNoZerosOnRe1FromSchur_from_localAssignment
    {w : ZetaSchurDecomposition}
    (A : BoundaryLocalPinchAssignment w) :
    ∀ z, z.re = 1 → riemannZeta z ≠ 0 :=
  ZetaNoZerosOnRe1FromSchur_from_bridge (bridge_of_localAssignment A)

/-- Statement-level wrapper from a local assignment. -/
theorem ZetaNoZerosOnRe1FromSchur_Statement_from_localAssignment
    {w : ZetaSchurDecomposition}
    (A : BoundaryLocalPinchAssignment w) (z : ℂ) (hz : z.re = 1) :
    ZetaNoZerosOnRe1FromSchur_Statement z hz w :=
  ZetaNoZerosOnRe1FromSchur_from_localAssignment A z hz

-- Removable-singularity pinch: if `g` is analytic on open connected `U`, satisfies
-- `‖g z‖ ≤ 1` on `U \ {ρ}`, and `g ρ = 1`, then `g ≡ 1` on `U`.
lemma schur_pinches_to_one
    {U : Set ℂ} (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    {ρ : ℂ} {g : ℂ → ℂ}
    (hg : AnalyticOn ℂ g U)
    (hle : ∀ z ∈ (U \ {ρ}), Complex.abs (g z) ≤ 1)
    (hρU : ρ ∈ U) (hval : g ρ = 1) : ∀ z ∈ U, g z = 1 := by
  -- Build a Schur bound for g on U from the off-point bound and the pinned value.
  have hSchurU : IsSchurOn g U := by
    intro z hz
    by_cases hzρ : z = ρ
    · simpa [hzρ, hval]
    · have hz' : z ∈ (U \ {ρ}) := ⟨hz, by simp [hzρ]⟩
      exact hle z hz'
  exact PinchConstantOfOne U hUopen hUconn g hg hSchurU ρ hρU hval

-- Wrapper specialized to a single removable point `{ρ}` using the global Schur bound on Ω.
lemma GlobalizeAcrossRemovable_atPoint
    (Θ g : ℂ → ℂ) {U : Set ℂ} {ρ : ℂ}
    (hUopen : IsOpen U) (hUconn : IsPreconnected U) (hUsub : U ⊆ Ω)
    (hρU : ρ ∈ U)
    (hΘSchur : IsSchurOn Θ Ω)
    (hΘU : AnalyticOn ℂ Θ (U \ {ρ}))
    (hg : AnalyticOn ℂ g U)
    (hExt : EqOn Θ g (U \ {ρ}))
    (hval : g ρ = 1) : ∀ z ∈ U, g z = 1 := by
  -- Transfer Schur bound from Θ to g on U \ {ρ} via equality, then pinch.
  have hle : ∀ z ∈ (U \ {ρ}), Complex.abs (g z) ≤ 1 := by
    intro z hz
    have hzΩ : z ∈ Ω := hUsub hz.1
    have : Θ z = g z := by simpa using hExt hz
    simpa [this] using hΘSchur z hzΩ
  exact schur_pinches_to_one (U := U) (ρ := ρ) (g := g)
    hUopen hUconn hg hle hρU hval

/-- Builder: package pinned-removable local data at each boundary point into a
`LocalPinchDataZOff` assignment, under the additional assumption that the chosen
open set `U` contains no zeros of ζ. This makes the off-zeros identities hold
on `U \ Z` by restriction from the global off-zeros decomposition.

Inputs:
- `w`: an off-zeros ζ→Θ/N decomposition with Schur bound and pinned limits.
- `choose`: for each boundary point `z` with `Re z = 1`, pick
  `U ⊆ Ω`, a distinguished `ρ ∈ U` with `(U ∩ Z(ξ)) = {ρ}`, a removable
  extension `g` of `Θ` across `ρ` with `g ρ = 1`, and the side-condition that
  `ζ` has no zeros in `U` (so the off-zeros equalities apply throughout `U`). -/
def OffZerosBoundaryAssignment.ofPinnedRemovable_noZetaZeros
    {ξf : ℂ → ℂ}
    (w : RH.RS.OffZeros.ZetaSchurDecompositionOffZeros riemannZeta ξf)
    (choose : ∀ z, z.re = 1 →
      ∃ (U : Set ℂ) (ρ : ℂ),
        IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
        (U ∩ (RH.RS.OffZeros.Z ξf)) = {ρ} ∧
        (∀ x ∈ U, riemannZeta x ≠ 0) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ EqOn w.Θ g (U \ (RH.RS.OffZeros.Z ξf)) ∧ g ρ = 1 ∧
        z ∈ (U \ (RH.RS.OffZeros.Z ξf)))
    : OffZerosBoundaryAssignment :=
{ Θ := w.Θ,
  N := w.N,
  hΘSchur := w.hΘSchur,
  assign := by
    intro z hz
    classical
    rcases choose z hz with
      ⟨U, ρ, hUopen, hUconn, hUsub, hρU, hZcap, hNoZeta, g, hgan, hExt, hval, hzUdiff⟩
    -- Define the local removable set Z := U ∩ Z(ξ)
    let Z : Set ℂ := U ∩ (RH.RS.OffZeros.Z ξf)
    have hZsub : Z ⊆ Ω := by
      intro x hx; exact hUsub hx.1
    -- z lies in U \ Z since it lies in U and avoids Z(ξ)
    have hz_not_Z : z ∉ Z := by
      intro hzZ
      have hz_inZxi : z ∈ (RH.RS.OffZeros.Z ξf) := hzZ.2
      have hz_not_inZxi : z ∉ (RH.RS.OffZeros.Z ξf) := by simpa using hzUdiff.2
      exact hz_not_inZxi hz_inZxi
    have hz_mem : z ∈ (U \ Z) := ⟨hzUdiff.1, hz_not_Z⟩
    -- Build LocalPinchDataZOff structure
    refine ⟨U, Z, ?data, hz_mem⟩
    refine ⟨hUopen, hUconn, hUsub, hZsub, ?hΘU, g, hgan, ?hExt, ρ, hρU, ?hρZ, hval, ?hZcapU,
            ?hζeq_off, ?hNnz_off⟩
    · -- Θ analytic on U \ Z by equality with analytic g on U
      -- Restrict equality to U \ Z from U \ Z(ξ)
      have hExt' : EqOn w.Θ g (U \ (RH.RS.OffZeros.Z ξf)) := hExt
      have hsub : (U \ Z) ⊆ (U \ (RH.RS.OffZeros.Z ξf)) := by
        intro x hx
        have hnotin : x ∉ RH.RS.OffZeros.Z ξf := by
          intro hxZxi; exact hx.2 ⟨hx.1, hxZxi⟩
        exact And.intro hx.1 hnotin
      have hExt'' : EqOn w.Θ g (U \ Z) := fun x hx => hExt' (hsub hx)
      exact (hgan.mono (by intro x hx; exact hx.1)).congr hExt''
    · -- Θ = g on U \ Z (since Z ⊆ Z(ξ) locally)
      intro x hx
      have hx' : x ∈ (U \ (RH.RS.OffZeros.Z ξf)) := by
        refine And.intro hx.1 ?hnotin
        intro hxZxi; exact hx.2 ⟨hx.1, hxZxi⟩
      exact hExt hx'
    · -- ρ ∈ Z = U ∩ Z(ξ)
      have : ρ ∈ (U ∩ (RH.RS.OffZeros.Z ξf)) := by
        have : ρ ∈ ({ρ} : Set ℂ) := by simp
        simpa [hZcap] using this
      exact this
    · -- (U ∩ Z) = {ρ}
      -- Here Z = U ∩ Z(ξ), so U ∩ Z = U ∩ (U ∩ Z(ξ)) = U ∩ Z(ξ) = {ρ}
      have : (U ∩ Z) = (U ∩ (RH.RS.OffZeros.Z ξf)) := by
        ext x; constructor <;> intro hx
        · exact ⟨hx.1, hx.2.2⟩
        · exact ⟨hx.1, And.intro hx.1 hx.2⟩
      simpa [this, hZcap]
    · -- ζ = Θ / N on U \ Z (since U has no ζ-zeros)
      intro x hx
      have hxU : x ∈ U := hx.1
      have hxΩ : x ∈ Ω := hUsub hxU
      have hxNotInZeta : x ∉ (RH.RS.OffZeros.Z riemannZeta) := by
        intro hxZ
        have hx0 : riemannZeta x = 0 := by simpa [RH.RS.OffZeros.Z, Set.mem_setOf_eq] using hxZ
        exact (hNoZeta x hxU) hx0
      have hxOffZeta : x ∈ (Ω \ (RH.RS.OffZeros.Z riemannZeta)) := ⟨hxΩ, hxNotInZeta⟩
      -- Use w's off-zeros identity at x
      simpa using (w.hζeq_off (by exact hxOffZeta))
    · -- N ≠ 0 on U \ Z (since U has no ζ-zeros)
      intro x hx
      have hxU : x ∈ U := hx.1
      have hxΩ : x ∈ Ω := hUsub hxU
      have hxNotInZeta : x ∉ (RH.RS.OffZeros.Z riemannZeta) := by
        intro hxZ
        have hx0 : riemannZeta x = 0 := by simpa [RH.RS.OffZeros.Z, Set.mem_setOf_eq] using hxZ
        exact (hNoZeta x hxU) hx0
      have hxOffZeta : x ∈ (Ω \ (RH.RS.OffZeros.Z riemannZeta)) := ⟨hxΩ, hxNotInZeta⟩
      exact w.hN_ne_off (by exact hxOffZeta) }
