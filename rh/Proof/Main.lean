import rh.academic_framework.Certificate
import rh.RS.SchurGlobalization
import rh.academic_framework.EulerProductMathlib
import rh.academic_framework.CompletedXi
import rh.academic_framework.Theta
import rh.RS.OffZerosBridge
import rh.RS.SchurGlobalization
import rh.RS.CRGreenOuter
-- CompletedXi import deferred until formalization lands
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

namespace RH.Proof

/-- Entry point availability placeholder for the final assembly theorem (interface). -/
def main_outline_available : Prop := True

/-/ Proof-layer alias for certificate readiness. -/
def PipelineReady : Prop := RH.AcademicFramework.Certificate.Ready

/-- Bridge: certificate readiness implies proof-layer readiness. -/
theorem pipeline_ready_of_certificate_ready
    (h : RH.AcademicFramework.Certificate.Ready) : PipelineReady := h

/-- Unconditional pipeline readiness, delegated to the certificate layer. -/
theorem pipeline_ready_unconditional : PipelineReady := by
  exact pipeline_ready_of_certificate_ready
    (RH.AcademicFramework.Certificate.Ready_unconditional)

end RH.Proof

-- Specialized wrappers are placed after `theorem RH` below

namespace RH.Proof.Assembly

/-- Boundary nonvanishing from the RS off-zeros boundary hypothesis (statement-level). -/
theorem boundary_nonvanishing_from_offzeros
    {Θ N : ℂ → ℂ}
    (h : RH.RS.OffZerosBoundaryHypothesis Θ N) :
    ∀ z, z.re = 1 → riemannZeta z ≠ 0 :=
  RH.RS.ZetaNoZerosOnRe1_from_offZerosAssignmentStatement h

/-- EPM-facing pointwise wrapper for the same statement. -/
theorem boundary_nonvanishing_from_offzeros_pointwise
    {Θ N : ℂ → ℂ}
    (h : RH.RS.OffZerosBoundaryHypothesis Θ N)
    (z : ℂ) (hz : z.re = 1) :
    riemannZeta z ≠ 0 :=
  RH.AcademicFramework.EPM.zeta_nonzero_re_eq_one_from_offZerosAssignmentStatement h z hz

end RH.Proof.Assembly

namespace RH.Proof.Assembly

/-- Pack the RS data needed to drive RH for a supplied `riemannXi`. -/
structure XiOffZerosBridge where
  riemannXi : ℂ → ℂ
  G : ℂ → ℂ
  symXi : ∀ ρ, riemannXi ρ = 0 → riemannXi (1 - ρ) = 0
  hXiEq : ∀ s, riemannXi s = G s * riemannZeta s
  hGnz : ∀ ρ ∈ RH.RS.Ω, G ρ ≠ 0
  Θ : ℂ → ℂ
  hSchur : RH.RS.IsSchurOn Θ (RH.RS.Ω \ {z | riemannZeta z = 0})
  assign : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
      (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) ∧
      ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
        Set.EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1

end RH.Proof.Assembly

namespace RH.Proof

open Complex

/-- RH symmetry wrapper (statement-level, generic function Ξ):
If `Ξ` has no zeros in the open right half‑plane `Ω = {Re > 1/2}` and its zeros
are symmetric under `s ↦ 1 - s`, then every zero of `Ξ` lies on the critical
line `Re = 1/2`.

This is the abstract symmetry pinching step; consumers can instantiate `Ξ` with
a completed zeta–type function that satisfies the functional equation. -/
theorem RH_core
    {Ξ : ℂ → ℂ}
    (noRightZeros : ∀ ρ ∈ RH.RS.Ω, Ξ ρ ≠ 0)
    (sym : ∀ ρ, Ξ ρ = 0 → Ξ (1 - ρ) = 0) :
    ∀ ρ, Ξ ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  intro ρ h0
  -- Trichotomy on Re ρ
  rcases lt_trichotomy ρ.re (1 / 2 : ℝ) with hlt | heq | hgt
  · -- Re ρ < 1/2 ⇒ Re (1 - ρ) > 1/2, so 1-ρ lies in Ω and carries a zero by symmetry
    have hgt' : (1 / 2 : ℝ) < 1 - ρ.re := by linarith
    -- membership in Ω for σ := 1 - ρ
    have hΩσ : (1 - ρ) ∈ RH.RS.Ω := by
      -- Ω = {s | 1/2 < Re s}
      have : (1 / 2 : ℝ) < (1 - ρ).re := by
        -- Re(1 - ρ) = 1 - Re ρ
        simpa [Complex.sub_re, Complex.one_re] using hgt'
      simpa [RH.RS.Ω, Set.mem_setOf_eq] using this
    -- symmetry transports the zero to 1-ρ
    have h0σ : Ξ (1 - ρ) = 0 := sym ρ h0
    -- contradict no-zero in Ω
    exfalso
    exact (noRightZeros (1 - ρ) hΩσ) h0σ
  · -- Re ρ = 1/2
    simpa using heq
  · -- Re ρ > 1/2 contradicts noRightZeros on Ω
    have hΩ : ρ ∈ RH.RS.Ω := by simpa [RH.RS.Ω, Set.mem_setOf_eq] using hgt
    exact False.elim ((noRightZeros ρ hΩ) h0)

end RH.Proof

-- Specialized RH wrappers (defined after the core RH theorem)
namespace RH.Proof

/-- RH specialized to an arbitrary function `Ξ` under the standard two hypotheses. -/
theorem RH_for
    (Ξ : ℂ → ℂ)
    (noRightZeros : ∀ ρ ∈ RH.RS.Ω, Ξ ρ ≠ 0)
    (sym : ∀ ρ, Ξ ρ = 0 → Ξ (1 - ρ) = 0) :
    ∀ ρ, Ξ ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  simpa using (RH_core (Ξ := Ξ) noRightZeros sym)

/-- RH specialized to a provided symbol `riemannXi` (completed zeta),
    assuming no zeros on Ω and symmetry of zeros. -/
theorem RH_riemannXi
    (riemannXi : ℂ → ℂ)
    (noRightZeros : ∀ ρ ∈ RH.RS.Ω, riemannXi ρ ≠ 0)
    (sym : ∀ ρ, riemannXi ρ = 0 → riemannXi (1 - ρ) = 0) :
    ∀ ρ, riemannXi ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  simpa using (RH_core (Ξ := riemannXi) noRightZeros sym)

end RH.Proof

namespace RH.Proof.Assembly

/-- Factorization transfer: if `Ξ = G · Z` on a set `Ω` and both `G` and `Z`
    are nonvanishing on `Ω`, then `Ξ` is nonvanishing on `Ω`. -/
theorem nonvanishing_of_factor
    (Ω : Set ℂ) (Ξ Z G : ℂ → ℂ)
    (hEq : ∀ s, Ξ s = G s * Z s)
    (hG : ∀ ρ ∈ Ω, G ρ ≠ 0)
    (hZ : ∀ ρ ∈ Ω, Z ρ ≠ 0) :
    ∀ ρ ∈ Ω, Ξ ρ ≠ 0 := by
  intro ρ hΩ
  have hGρ := hG ρ hΩ
  have hZρ := hZ ρ hΩ
  simpa [hEq ρ] using mul_ne_zero hGρ hZρ

/-- Route assembly: assuming
    1) symmetry of zeros for a provided `riemannXi`,
    2) a factorization `riemannXi = G · ζ` with `G` zero‑free on `Ω`, and
    3) an RS Schur–pinch off‑zeros assignment excluding ζ‑zeros in `Ω`,
    we obtain RH for `riemannXi`. -/
theorem RH_riemannXi_from_RS_offZeros
    (riemannXi : ℂ → ℂ)
    (symXi : ∀ ρ, riemannXi ρ = 0 → riemannXi (1 - ρ) = 0)
    (G : ℂ → ℂ)
    (hXiEq : ∀ s, riemannXi s = G s * riemannZeta s)
    (hGnz : ∀ ρ ∈ RH.RS.Ω, G ρ ≠ 0)
    (Θ : ℂ → ℂ)
    (hSchur : RH.RS.IsSchurOn Θ (RH.RS.Ω \ {z | riemannZeta z = 0}))
    (assign : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
          Set.EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
    : ∀ ρ, riemannXi ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  -- ζ has no zeros on Ω by the RS off‑zeros Schur–pinch route
  have hζnz : ∀ ρ ∈ RH.RS.Ω, riemannZeta ρ ≠ 0 :=
    RH.RS.no_offcritical_zeros_from_schur Θ hSchur assign
  -- Transfer to Ξ via the factorization Ξ = G·ζ with G nonzero on Ω
  have hΞnz : ∀ ρ ∈ RH.RS.Ω, riemannXi ρ ≠ 0 :=
    nonvanishing_of_factor (Ω := RH.RS.Ω)
      (Ξ := riemannXi) (Z := riemannZeta) (G := G) hXiEq hGnz hζnz
  -- Conclude RH for Ξ by symmetry wrapper
  exact RH_riemannXi riemannXi hΞnz symXi

end RH.Proof.Assembly

namespace RH.Proof.Assembly

/-- Route assembly (one-safe variant): allow `G ≠ 0` on `Ω \ {1}` and a separate
    nonvanishing fact `riemannXi 1 ≠ 0`. -/
theorem RH_riemannXi_from_RS_offZeros_oneSafe
    (riemannXi : ℂ → ℂ)
    (symXi : ∀ ρ, riemannXi ρ = 0 → riemannXi (1 - ρ) = 0)
    (G : ℂ → ℂ)
    (hXiEq : ∀ s, riemannXi s = G s * riemannZeta s)
    (hGnzAway : ∀ ρ ∈ RH.RS.Ω, ρ ≠ (1 : ℂ) → G ρ ≠ 0)
    (hXiOne : riemannXi 1 ≠ 0)
    (Θ : ℂ → ℂ)
    (hSchur : RH.RS.IsSchurOn Θ (RH.RS.Ω \ {z | riemannZeta z = 0}))
    (assign : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
          Set.EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
    : ∀ ρ, riemannXi ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  -- ζ has no zeros on Ω
  have hζnz : ∀ ρ ∈ RH.RS.Ω, riemannZeta ρ ≠ 0 :=
    RH.RS.no_offcritical_zeros_from_schur Θ hSchur assign
  -- Build Ξ nonvanishing on Ω pointwise using the one-safe guard at 1
  have hΞnz : ∀ ρ ∈ RH.RS.Ω, riemannXi ρ ≠ 0 := by
    intro ρ hΩ
    by_cases h1 : ρ = (1 : ℂ)
    · simpa [h1] using hXiOne
    · have hG : G ρ ≠ 0 := hGnzAway ρ hΩ h1
      have hZ : riemannZeta ρ ≠ 0 := hζnz ρ hΩ
      simpa [hXiEq ρ] using mul_ne_zero hG hZ
  -- Conclude RH for Ξ by symmetry wrapper
  exact RH_riemannXi riemannXi hΞnz symXi

end RH.Proof.Assembly

namespace RH.Proof.Assembly

/-- Route assembly (one-safe, local equality variant): allow
    1) zero-symmetry for a provided `riemannXi`,
    2) factorization `riemannXi = G · ζ` only on `Ω \ {1}`,
    3) nonvanishing of `G` on `Ω \ {1}` plus a separate center value `riemannXi 1 ≠ 0`, and
    4) RS Schur–pinch off‑zeros assignment excluding ζ‑zeros in `Ω`.

    Concludes RH for the provided `riemannXi`. -/
theorem RH_riemannXi_from_RS_offZeros_oneSafe_localEq
    (riemannXi : ℂ → ℂ)
    (symXi : ∀ ρ, riemannXi ρ = 0 → riemannXi (1 - ρ) = 0)
    (G : ℂ → ℂ)
    (hXiEqAway : ∀ ρ ∈ RH.RS.Ω, ρ ≠ (1 : ℂ) → riemannXi ρ = G ρ * riemannZeta ρ)
    (hGnzAway : ∀ ρ ∈ RH.RS.Ω, ρ ≠ (1 : ℂ) → G ρ ≠ 0)
    (hXiOne : riemannXi 1 ≠ 0)
    (Θ : ℂ → ℂ)
    (hSchur : RH.RS.IsSchurOn Θ (RH.RS.Ω \ {z | riemannZeta z = 0}))
    (assign : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
          Set.EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
    : ∀ ρ, riemannXi ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  -- ζ has no zeros on Ω
  have hζnz : ∀ ρ ∈ RH.RS.Ω, riemannZeta ρ ≠ 0 :=
    RH.RS.no_offcritical_zeros_from_schur Θ hSchur assign
  -- Build Ξ nonvanishing on Ω pointwise using the one-safe guard at 1
  have hΞnz : ∀ ρ ∈ RH.RS.Ω, riemannXi ρ ≠ 0 := by
    intro ρ hΩ
    by_cases h1 : ρ = (1 : ℂ)
    · simpa [h1] using hXiOne
    · have hG : G ρ ≠ 0 := hGnzAway ρ hΩ h1
      have hZ : riemannZeta ρ ≠ 0 := hζnz ρ hΩ
      have hEq : riemannXi ρ = G ρ * riemannZeta ρ := hXiEqAway ρ hΩ h1
      simpa [hEq] using mul_ne_zero hG hZ
  -- Conclude RH for Ξ by symmetry wrapper
  exact RH_riemannXi riemannXi hΞnz symXi

end RH.Proof.Assembly

namespace RH.Proof.Final

open RH.AcademicFramework.CompletedXi

/-- RH for `riemannXi` from supplied FE, Schur map Θ, assignment, and nonvanishing of G on Ω. -/
theorem RH_xi_from_supplied_RS
    (fe : ∀ s, riemannXi s = riemannXi (1 - s))
    (Θ : ℂ → ℂ)
    (hSchur : RH.RS.IsSchurOn Θ (RH.RS.Ω \ {z | riemannZeta z = 0}))
    (assign : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
          Set.EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
    (hGnz : ∀ ρ ∈ RH.RS.Ω, G ρ ≠ 0)
    : ∀ ρ, riemannXi ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  -- Derive zero-symmetry from the supplied functional equation locally
  have symXi : ∀ ρ, riemannXi ρ = 0 → riemannXi (1 - ρ) = 0 := by
    intro ρ hρ; have := fe ρ; simpa [this] using hρ
  exact RH.Proof.Assembly.RH_riemannXi_from_RS_offZeros
    riemannXi symXi G (by intro z; exact xi_factorization z) hGnz Θ hSchur assign

end RH.Proof.Final

namespace RH.Proof.Final

open RH.AcademicFramework.CompletedXi

/-- Hxi from the CR-outer full route: plug `fe := xi_functional_equation`. -/
theorem Hxi_from_CR_outer
    (choose : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      RH.RS.OffZeros.LocalData (riemannZeta := riemannZeta)
        (Θ := RH.RS.Θ_of RH.RS.CRGreenOuterData) (ρ := ρ))
    (hGnz : ∀ ρ ∈ RH.RS.Ω, G ρ ≠ 0)
    : ∀ ρ, riemannXi ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  -- inline call to the already-defined outer/local wrapper to avoid forward ref
  exact RH.Proof.Final.RH_xi_from_outer_and_local (fe := xi_functional_equation)
    (choose := choose) (hGnz := hGnz)

/-- Hxi from the CR-outer one-safe route: plug `fe := xi_functional_equation`. -/
theorem Hxi_from_CR_outer_oneSafe
    (choose : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      RH.RS.OffZeros.LocalData (riemannZeta := riemannZeta)
        (Θ := RH.RS.Θ_of RH.RS.CRGreenOuterData) (ρ := ρ))
    (hGnzAway : ∀ ρ ∈ RH.RS.Ω, ρ ≠ (1 : ℂ) → G ρ ≠ 0)
    (hXiOne : riemannXi 1 ≠ 0)
    : ∀ ρ, riemannXi ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  -- inline call to avoid forward ref; use the one-safe outer/local wrapper
  exact RH.Proof.Final.RH_xi_from_outer_and_local_oneSafe (fe := xi_functional_equation)
    (O := RH.RS.CRGreenOuterData) (choose := choose) (hGnzAway := hGnzAway) (hXiOne := hXiOne)

/-- Convert Hxi to mathlib's `RiemannZeta.RiemannHypothesis`. -/
theorem RH_mathlib_from_xi
    (Hxi : ∀ ρ, riemannXi ρ = 0 → ρ.re = (1 / 2 : ℝ))
    : RiemannHypothesis := by
  intro s hζ _hneTriv hne1
  -- `Ξ(s) = G(s)·ζ(s)` vanishes at every ζ-zero
  have hXi0 : riemannXi s = 0 := by simpa [xi_factorization s, hζ]
  -- Apply Hxi
  exact Hxi s hXi0

/-- Compose the CR-outer full route with `RH_mathlib_from_xi`. -/
theorem RH_mathlib_from_CR_outer
    (choose : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      RH.RS.OffZeros.LocalData (riemannZeta := riemannZeta)
        (Θ := RH.RS.Θ_of RH.RS.CRGreenOuterData) (ρ := ρ))
    (hGnz : ∀ ρ ∈ RH.RS.Ω, G ρ ≠ 0)
    : RiemannHypothesis :=
  RH_mathlib_from_xi (Hxi_from_CR_outer choose hGnz)

/-- Compose the CR-outer one-safe route with `RH_mathlib_from_xi`. -/
theorem RH_mathlib_from_CR_outer_oneSafe_final
    (choose : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      RH.RS.OffZeros.LocalData (riemannZeta := riemannZeta)
        (Θ := RH.RS.Θ_of RH.RS.CRGreenOuterData) (ρ := ρ))
    (hGnzAway : ∀ ρ ∈ RH.RS.Ω, ρ ≠ (1 : ℂ) → G ρ ≠ 0)
    (hXiOne : riemannXi 1 ≠ 0)
    : RiemannHypothesis :=
  RH_mathlib_from_xi (Hxi_from_CR_outer_oneSafe choose hGnzAway hXiOne)

end RH.Proof.Final

namespace RH.Proof.Final

open RH.AcademicFramework.CompletedXi

/-- RH for `riemannXi` from: functional equation `fe`, outer data `O` producing a Schur map
Θ via the Cayley transform, a local chooser `choose` yielding removable-set data at each
putative ζ-zero inside Ω, and nonvanishing of `G` on Ω. -/
theorem RH_xi_from_outer_and_local
    (fe : ∀ s, riemannXi s = riemannXi (1 - s))
    (O : RH.RS.OuterData)
    (choose : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      RH.RS.OffZeros.LocalData (riemannZeta := riemannZeta) (Θ := RH.RS.Θ_of O) (ρ := ρ))
    (hGnz : ∀ ρ ∈ RH.RS.Ω, G ρ ≠ 0)
    : ∀ ρ, riemannXi ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  -- Build Θ and Schur bound from outer data
  let Θ : ℂ → ℂ := RH.RS.Θ_of O
  have hSchur : RH.RS.IsSchurOn Θ (RH.RS.Ω \ {z | riemannZeta z = 0}) :=
    RH.RS.Θ_Schur_of O
  -- Build assign via the local chooser
  let assign := RH.RS.OffZeros.assign_fromLocal (Θ := Θ) (choose := choose)
  -- Invoke the supplied RS assembly
  exact RH_xi_from_supplied_RS fe Θ hSchur assign hGnz

end RH.Proof.Final

namespace RH.Proof.Final

open RH.AcademicFramework.CompletedXi
-- open of `zero_symmetry_from_fe` is not needed here; we derive symmetry locally

/-- RH for `riemannXi` using the one-safe assembly variant. -/
theorem RH_xi_from_outer_and_local_oneSafe
    (fe : ∀ s, riemannXi s = riemannXi (1 - s))
    (O : RH.RS.OuterData)
    (choose : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      RH.RS.OffZeros.LocalData (riemannZeta := riemannZeta) (Θ := RH.RS.Θ_of O) (ρ := ρ))
    (hGnzAway : ∀ ρ ∈ RH.RS.Ω, ρ ≠ (1 : ℂ) → G ρ ≠ 0)
    (hXiOne : riemannXi 1 ≠ 0)
    : ∀ ρ, riemannXi ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  let Θ : ℂ → ℂ := RH.RS.Θ_of O
  have hSchur : RH.RS.IsSchurOn Θ (RH.RS.Ω \ {z | riemannZeta z = 0}) := RH.RS.Θ_Schur_of O
  let assign := RH.RS.OffZeros.assign_fromLocal (Θ := Θ) (choose := choose)
  -- Local zero-symmetry from FE
  have symXi : ∀ ρ, riemannXi ρ = 0 → riemannXi (1 - ρ) = 0 := by
    intro ρ hρ; have := fe ρ; simpa [this] using hρ
  exact RH.Proof.Assembly.RH_riemannXi_from_RS_offZeros_oneSafe
    riemannXi symXi G (by intro z; exact xi_factorization z) hGnzAway hXiOne Θ hSchur assign

/-- CR-outer one-safe route: instantiate the outer data with CRGreenOuterData. -/
theorem RiemannHypothesis_from_CR_outer_oneSafe
    (fe : ∀ s, riemannXi s = riemannXi (1 - s))
    (choose : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      RH.RS.OffZeros.LocalData (riemannZeta := riemannZeta) (Θ := RH.RS.Θ_of RH.RS.CRGreenOuterData) (ρ := ρ))
    (hGnzAway : ∀ ρ ∈ RH.RS.Ω, ρ ≠ (1 : ℂ) → G ρ ≠ 0)
    (hXiOne : riemannXi 1 ≠ 0)
    : ∀ ρ, riemannXi ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  exact RH_xi_from_outer_and_local_oneSafe fe RH.RS.CRGreenOuterData choose hGnzAway hXiOne

/-- CR-outer full route (if global nonvanishing for G on Ω is available). -/
theorem RiemannHypothesis_from_CR_outer
    (fe : ∀ s, riemannXi s = riemannXi (1 - s))
    (choose : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      RH.RS.OffZeros.LocalData (riemannZeta := riemannZeta) (Θ := RH.RS.Θ_of RH.RS.CRGreenOuterData) (ρ := ρ))
    (hGnz : ∀ ρ ∈ RH.RS.Ω, G ρ ≠ 0)
    : ∀ ρ, riemannXi ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  exact RH_xi_from_outer_and_local fe RH.RS.CRGreenOuterData choose hGnz

end RH.Proof.Final
