/-!
ARCHIVE (not built): RS local assignment scaffolding (sketch).
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Basic

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

end ArchiveXi


