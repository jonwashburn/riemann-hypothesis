/-!
ARCHIVE (not built): RS local assignment scaffolding (sketch).
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Basic
import rh.RS.SchurGlobalization

noncomputable section

open Complex Set

namespace ArchiveXi

variable (Θ : ℂ → ℂ)

/-- Sketch: data at a boundary point for removable-set pinch. -/
structure LocalData where
  U : Set ℂ
  ρ : ℂ
  hUopen : IsOpen U
  hUconn : IsPreconnected U
  hUsub : U ⊆ { s : ℂ | (1/2 : ℝ) < s.re }
  hρU : ρ ∈ U
  g : ℂ → ℂ
  hg : AnalyticOn ℂ g U
  hΘU : AnalyticOn ℂ Θ (U \ {ρ})
  hExt : Set.EqOn Θ g (U \ {ρ})
  hval : g ρ = 1
  hWitness : ∃ z, z ∈ U ∧ g z ≠ 1

/-- Sketch: build `assign` from a choice function that returns `LocalData` per ρ. -/
def assignOfChoice
    (choose : ∀ ρ, ∃ data : LocalData Θ, data.ρ = ρ) :
    ∀ ρ, ρ ∈ { s : ℂ | (1/2 : ℝ) < s.re } → Prop := by
  intro ρ hρ; exact True

/-- RS-shaped off-zeros assignment (archive sketch): produces the exact statement
    required by `RH.RS.no_offcritical_zeros_from_schur`.
    To be implemented by the ζ→Θ/N bridge; here we record the target type. -/
def assign_RS_shape :
    ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
          Set.EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1 := by
  intro ρ hΩ hζ
  admit

end ArchiveXi
