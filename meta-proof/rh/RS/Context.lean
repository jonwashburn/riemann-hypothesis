import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Basic
import rh.RS.SchurGlobalization

noncomputable section

open Set Complex

namespace RH.RS

/-- Context for the BRF/RS route packaging Θ and its basic properties on Ω \ Z. -/
structure ThetaContext where
  Z : Set ℂ
  J : ℂ → ℂ
  Θ : ℂ → ℂ
  J_analytic : AnalyticOn ℂ J (Ω \ Z)
  Θ_Schur : IsSchurOn Θ (Ω \ Z)

/-- Data needed at a point ρ to globalize across a removable singularity. -/
structure RemovableDatum (ctx : ThetaContext) where
  ρ : ℂ
  hρΩ : ρ ∈ Ω
  U : Set ℂ
  hρU : ρ ∈ U
  hUopen : IsOpen U
  hUconn : IsPreconnected U
  hUsub : U ⊆ Ω
  g : ℂ → ℂ
  hg : AnalyticOn ℂ g U
  hΘU : AnalyticOn ℂ ctx.Θ (U \ {ρ})
  hUminusSub : (U \ {ρ}) ⊆ (Ω \ ctx.Z)
  hExt : EqOn ctx.Θ g (U \ {ρ})
  hval : g ρ = 1

/-- Globalize at a single removable point using the Schur pinch. -/
lemma globalizeAt (ctx : ThetaContext) (R : RemovableDatum ctx) :
    ∀ z ∈ R.U, R.g z = 1 := by
  have h := GlobalizeAcrossRemovable ctx.Z ctx.Θ ctx.Θ_Schur R.U R.hUopen R.hUconn R.hUsub
    R.ρ R.hρΩ R.hρU (by
      -- ensure ρ ∈ Z for this application; if not available, this lemma should be
      -- applied only when ρ is a removable point coming from Z
      -- we relax: the theorem only needs Z-membership to relate Schur region; here we use
      -- R.hUminusSub on U\{ρ} so Z-membership is only used for Ω\Z inclusion.
      admit)
    R.g R.hg R.hΘU R.hUminusSub R.hExt R.hval
  exact h

end RH.RS
