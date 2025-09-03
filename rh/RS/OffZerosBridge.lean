/-
  RS: explicit Θ,N for the off-zeros ζ–Schur bridge, pinned limit, and boundary assignment.

  Non-circular interface: N is analytic on Ω \ Z(ξ); ζ = Θ/N only on Ω \ Z(ζ).
  This matches the manuscript's active route and avoids baking in ζ nonvanishing on Ω.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Topology.Algebra.UniformGroup

noncomputable section
open Complex Filter Set
open scoped Topology

namespace RH
namespace RS
namespace OffZeros

variable (riemannZeta riemannXi : ℂ → ℂ)

/-- Right half-plane Ω := { s : ℂ | 1/2 < Re s }. -/
def Ω : Set ℂ := {s : ℂ | (1/2 : ℝ) < s.re}

/-- Zero set of a function. -/
def Z (f : ℂ → ℂ) : Set ℂ := {s | f s = 0}

/-- Schur-on-a-set predicate. -/
def IsSchurOn (Θ : ℂ → ℂ) (S : Set ℂ) : Prop := ∀ ⦃s⦄, s ∈ S → Complex.abs (Θ s) ≤ 1

/-- Cayley map. -/
private def cayley (F : ℂ → ℂ) : ℂ → ℂ := fun s => (F s - 1) / (F s + 1)

/-- Off-zeros ζ–Schur bridge. -/
structure ZetaSchurDecompositionOffZeros where
  Θ : ℂ → ℂ
  N : ℂ → ℂ
  hΘSchur : IsSchurOn Θ (Ω)
  hNanalytic_offXi : AnalyticOn ℂ N (Ω \ Z riemannXi)
  hζeq_off : ∀ {s}, s ∈ (Ω \ Z riemannZeta) → riemannZeta s = Θ s / N s
  hN_ne_off : ∀ {s}, s ∈ (Ω \ Z riemannZeta) → N s ≠ 0
  hΘ_lim1_at_ξzero : ∀ {ρ}, ρ ∈ Ω → riemannXi ρ = 0 → Tendsto Θ (nhdsWithin ρ (Ω \ Z riemannXi)) (nhds 1)

/-- Constructor: explicit Θ,N from J with ξ = G·ζ on Ω.
We require analyticity of det2, O, G, ξ on Ω; a pointwise identity for J off Z(ξ);
and Schur bound for Θ := cayley (2·J). We also assume Θ is analytic off Z(ξ)
(available in-project via denominator nonvanishing).
Additionally, we assume the explicit nonvanishing of `Θ s * G s / riemannXi s` on `Ω \ Z ζ`,
which holds in your project from the determinant/outer noncancellation and the algebraic identities. -/
def ZetaSchurDecompositionOffZeros.ofEqOffZeros
  (det2 O G J : ℂ → ℂ)
  (hdet2A : AnalyticOn ℂ det2 (Ω))
  (hOA : AnalyticOn ℂ O (Ω))
  (hGA : AnalyticOn ℂ G (Ω))
  (hXiA : AnalyticOn ℂ riemannXi (Ω))
  (hO_ne : ∀ ⦃s⦄, s ∈ (Ω) → O s ≠ 0)
  (hdet2_ne : ∀ ⦃s⦄, s ∈ (Ω) → det2 s ≠ 0)
  (hG_ne_offζ : ∀ ⦃s⦄, s ∈ (Ω \ Z riemannZeta) → G s ≠ 0)
  (hJ_def_offXi : ∀ ⦃s⦄, s ∈ (Ω \ Z riemannXi) → J s = det2 s / (O s * riemannXi s))
  (hXi_eq_Gζ : ∀ ⦃s⦄, s ∈ (Ω) → riemannXi s = G s * riemannZeta s)
  (hΘSchur : IsSchurOn (cayley (fun s => (2 : ℂ) * J s)) (Ω))
  (hΘA_offXi : AnalyticOn ℂ (cayley (fun s => (2 : ℂ) * J s)) (Ω \ Z riemannXi))
  (hΘ_lim1_at_ξzero : ∀ ⦃ρ⦄, ρ ∈ Ω → riemannXi ρ = 0 →
      Tendsto (cayley (fun s => (2 : ℂ) * J s)) (nhdsWithin ρ (Ω \ Z riemannXi)) (nhds (1 : ℂ)))
  (hN_ne_off_assm : ∀ ⦃s⦄, s ∈ (Ω \ Z riemannZeta) →
      ((cayley (fun s => (2 : ℂ) * J s)) s * G s / riemannXi s) ≠ 0)
  : ZetaSchurDecompositionOffZeros riemannZeta riemannXi := by
  -- Definitions
  let F : ℂ → ℂ := fun s => (2 : ℂ) * J s
  let Θ : ℂ → ℂ := cayley F
  let N : ℂ → ℂ := fun s => Θ s * G s / riemannXi s
  -- Analyticity of N on Ω \ Z(ξ)
  have hNanalytic_offXi : AnalyticOn ℂ N (Ω \ Z riemannXi) := by
    have hΘA : AnalyticOn ℂ Θ (Ω \ Z riemannXi) := by simpa [Θ, F] using hΘA_offXi
    have hGA' : AnalyticOn ℂ G (Ω \ Z riemannXi) := hGA.mono (by intro s hs; exact hs.1)
    have hXiA' : AnalyticOn ℂ riemannXi (Ω \ Z riemannXi) := hXiA.mono (by intro s hs; exact hs.1)
    refine (hΘA.mul hGA').div hXiA' ?den
    intro s hs; simpa [Z] using hs.2
  -- ζ = Θ / N on Ω \ Z(ζ)
  have hζeq_off' : ∀ ⦃s⦄, s ∈ (Ω \ Z riemannZeta) → riemannZeta s = Θ s / N s := by
    intro s hs
    rcases hs with ⟨hsΩ, hsζ⟩
    have hζne : riemannZeta s ≠ 0 := by simpa [Z] using hsζ
    have hGne : G s ≠ 0 := hG_ne_offζ ⟨hsΩ, hsζ⟩
    have hξ : riemannXi s = G s * riemannZeta s := hXi_eq_Gζ hsΩ
    have hξne : riemannXi s ≠ 0 := by simpa [hξ] using mul_ne_zero hGne hζne
    -- Nonvanishing of N from the explicit assumption
    have hNne : N s ≠ 0 := by
      have := hN_ne_off_assm ⟨hsΩ, hsζ⟩
      simpa [N, Θ, F] using this
    -- Prove equality by multiplying both sides by N s and using associativity
    have hmul : riemannZeta s * N s = Θ s := by
      have hNdef : N s = Θ s * G s / riemannXi s := rfl
      calc
        riemannZeta s * N s
            = riemannZeta s * (Θ s * G s / riemannXi s) := by simp [hNdef]
        _   = riemannZeta s * (Θ s * G s) * (riemannXi s)⁻¹ := by
              simp [div_eq_mul_inv, mul_assoc]
        _   = Θ s * (riemannZeta s * G s) * (riemannXi s)⁻¹ := by
              simp [mul_comm, mul_left_comm, mul_assoc]
        _   = Θ s * (G s * riemannZeta s) * (riemannXi s)⁻¹ := by
              simp [mul_comm]
        _   = Θ s * riemannXi s * (riemannXi s)⁻¹ := by
              simpa [hξ, mul_comm, mul_left_comm, mul_assoc]
        _   = Θ s := by
              simp [hξne]
    -- Convert back to a division equality using multiplicative inverses
    have hcalc : riemannZeta s = Θ s / N s := by
      have hNne' : N s ≠ 0 := hNne
      calc
        riemannZeta s
            = riemannZeta s * 1 := by simp
        _   = riemannZeta s * (N s * (N s)⁻¹) := by
              simp [hNne']
        _   = (riemannZeta s * N s) * (N s)⁻¹ := by
              simp [mul_assoc]
        _   = Θ s * (N s)⁻¹ := by
              simpa [hmul]
        _   = Θ s / N s := by
              simp [div_eq_mul_inv]
    -- Conclude ζ = Θ/N by symmetry
    simpa [hcalc]
  -- N ≠ 0 on Ω \ Z(ζ)
  have hN_ne_off' : ∀ ⦃s⦄, s ∈ (Ω \ Z riemannZeta) → N s ≠ 0 := by
    intro s hs
    -- from the explicit nonvanishing assumption
    have := hN_ne_off_assm hs
    simpa [N, Θ, F] using this
  -- Assemble
  refine {
      Θ := Θ,
      N := N,
      hΘSchur := by simpa [Θ, F] using hΘSchur,
      hNanalytic_offXi := hNanalytic_offXi,
      hζeq_off := by intro s hs; simpa [Θ, F] using (hζeq_off' hs),
      hN_ne_off := by intro s hs; simpa [Θ, F] using (hN_ne_off' hs),
      hΘ_lim1_at_ξzero := by intro ρ hΩρ hξρ; simpa [Θ, F] using hΘ_lim1_at_ξzero hΩρ hξρ }

/-- Thin constructor: build `ZetaSchurDecompositionOffZeros` directly from off-zeros data. -/
def ZetaSchurDecompositionOffZeros.ofData
  {Θ N : ℂ → ℂ}
  (hΘSchur : IsSchurOn Θ (Ω))
  (hNanalytic_offXi : AnalyticOn ℂ N (Ω \ Z riemannXi))
  (hζeq_off : ∀ ⦃s⦄, s ∈ (Ω \ Z riemannZeta) → riemannZeta s = Θ s / N s)
  (hN_ne_off : ∀ ⦃s⦄, s ∈ (Ω \ Z riemannZeta) → N s ≠ 0)
  (hΘ_lim1_at_ξzero : ∀ ⦃ρ⦄, ρ ∈ Ω → riemannXi ρ = 0 → Tendsto Θ (nhdsWithin ρ (Ω \ Z riemannXi)) (nhds 1))
  : ZetaSchurDecompositionOffZeros riemannZeta riemannXi :=
{ Θ := Θ,
  N := N,
  hΘSchur := hΘSchur,
  hNanalytic_offXi := hNanalytic_offXi,
  hζeq_off := by intro s hs; exact hζeq_off hs,
  hN_ne_off := by intro s hs; exact hN_ne_off hs,
  hΘ_lim1_at_ξzero := by intro ρ hΩρ hξρ; exact hΘ_lim1_at_ξzero hΩρ hξρ }

end OffZeros
end RS
end RH
