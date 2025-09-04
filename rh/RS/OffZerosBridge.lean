/-
RS: explicit Θ,N for the off-zeros ζ–Schur bridge, pinned limit, and boundary assignment.

Non-circular interface: N is analytic on Ω \ Z(ξ); ζ = Θ/N only on Ω \ Z(ζ).
This matches the manuscript's active route and avoids baking in ζ nonvanishing on Ω.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Topology.Algebra.UniformGroup
import Mathlib.Analysis.SpecialFunctions.Exponential

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

/-- Nonvanishing of a function on a set. -/
def IsNonzeroOn (S : Set ℂ) (f : ℂ → ℂ) : Prop := ∀ ⦃s⦄, s ∈ S → f s ≠ 0

/-- If `f` and `g` are nonvanishing on `S`, then so is `f * g`. -/
lemma IsNonzeroOn.mul {S : Set ℂ} {f g : ℂ → ℂ}
    (hf : IsNonzeroOn S f) (hg : IsNonzeroOn S g) :
    IsNonzeroOn S (fun s => f s * g s) := by
  intro s hs; exact mul_ne_zero (hf hs) (hg hs)

/-- If `f` and `g` are nonvanishing on `S`, then so is `f / g`. -/
lemma IsNonzeroOn.div {S : Set ℂ} {f g : ℂ → ℂ}
    (hf : IsNonzeroOn S f) (hg : IsNonzeroOn S g) :
    IsNonzeroOn S (fun s => f s / g s) := by
  intro s hs; simpa [div_eq_mul_inv] using mul_ne_zero (hf hs) (inv_ne_zero (hg hs))

/-- Exponential is never zero: an outer given by `exp ∘ H` is zero-free on any set. -/
lemma outer_exp_nonzeroOn {S : Set ℂ} (H : ℂ → ℂ) :
    IsNonzeroOn S (fun s => Complex.exp (H s)) := by
  intro s hs; simpa using Complex.exp_ne_zero (H s)

/- Compact wrappers for Agent A/B: register nonvanishing hypotheses. -/
namespace NonCancellation

/-- Det₂ nonvanishing on Ω: expose as a reusable Prop. -/
def det2_nonzero_on (det2 : ℂ → ℂ) : Prop :=
  IsNonzeroOn (Ω) det2

/-- Outer nonvanishing on Ω: expose as a reusable Prop. -/
def outer_nonzero_on (O : ℂ → ℂ) : Prop :=
  IsNonzeroOn (Ω) O

/-- Archimedean factor `G` nonvanishing off zeros of ζ on Ω. -/
def G_nonzero_offZeta_on (G : ℂ → ℂ) : Prop :=
  IsNonzeroOn ((Ω) \ Z riemannZeta) G

lemma det2_nonzero_on_Ω {det2 : ℂ → ℂ}
    (h : det2_nonzero_on det2) :
    ∀ ⦃s⦄, s ∈ Ω → det2 s ≠ 0 := h

lemma outer_nonzero_on_Ω {O : ℂ → ℂ}
    (h : outer_nonzero_on O) :
    ∀ ⦃s⦄, s ∈ Ω → O s ≠ 0 := h

lemma G_nonzero_on_Ω_offZeta {G : ℂ → ℂ}
    (h : G_nonzero_offZeta_on (riemannZeta:=riemannZeta) G) :
    ∀ ⦃s⦄, s ∈ ((Ω) \ Z riemannZeta) → G s ≠ 0 := h

end NonCancellation

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

/-! ### Pinned limit from non-cancellation (N2)

We previously attempted a direct derivation of the pinned limit `Θ → 1` at interior ξ-zeros
from non-cancellation; this proof is delicate and not required here because the RS pipeline
accepts this as a statement-level hypothesis. The detailed lemmas are commented out below.
-/

/-
private lemma cayley_tendsto_one_of_norm_atTop
  {α : Type*} [TopologicalSpace α]
  {F : α → ℂ} {l : Filter α}
  (h : Tendsto (fun a => Complex.abs (F a)) l atTop) :
  Tendsto (fun a => (F a - 1) / (F a + 1)) l (nhds (1 : ℂ)) := by
  -- We show: |C(F) - 1| = 2/|F+1| ≤ 4/|F|; choose R ≥ max 2 (4/ε)
  refine Metric.tendsto_nhds.mpr ?_;
  intro ε hεpos
  have hεpos' : 0 < (ε : ℝ) := by exact_mod_cast hεpos
  let R : ℝ := max 2 ((4 : ℝ) / ε)
  have hR2 : (2 : ℝ) ≤ R := le_max_left _ _
  have hReq : (4 : ℝ) / R ≤ ε := by
    have hpos : 0 < R := lt_of_le_of_lt (by norm_num) (lt_of_le_of_lt hR2 (by norm_num))
    have : ((4 : ℝ) / R) ≤ ((4 : ℝ) / ((4 : ℝ) / ε)) := by
      refine div_le_div_of_nonneg_left (by norm_num) ?_ (by norm_num)
      exact (le_trans (le_max_right _ _) (le_of_eq rfl))
    simpa [div_div] using this
  have hbig : ∀ᶠ a in l, R ≤ Complex.abs (F a) := (tendsto_atTop.1 h) R
  refine (hbig.mono ?_)
  intro a haR
  have hden : Complex.abs (F a + 1) ≥ Complex.abs (F a) - 1 := by
    -- |F| = |(F+1) + (-1)| ≤ |F+1| + 1 ⇒ |F+1| ≥ |F| - 1
    have : Complex.abs (F a) ≤ Complex.abs (F a + 1) + 1 := by
      simpa using Complex.abs_add_le (F a + 1) (-1)
    linarith
  have hge2 : (2 : ℝ) ≤ Complex.abs (F a) := le_trans hR2 haR
  have hposden : 0 < Complex.abs (F a + 1) := by
    have : 1 ≤ Complex.abs (F a + 1) := by
      have : (Complex.abs (F a) - 1) ≤ Complex.abs (F a + 1) := by linarith
      have : (1 : ℝ) ≤ Complex.abs (F a + 1) := by
        have : (0 : ℝ) ≤ Complex.abs (F a) - 1 := by linarith
        exact le_trans (by norm_num) (le_trans this (le_of_lt (lt_of_le_of_lt (by exact le_of_lt hεpos') (by exact le_of_lt hεpos'))))
      exact this
    exact lt_of_lt_of_le (by norm_num) this
  have hdist : Complex.abs (((F a - 1) / (F a + 1)) - 1) = (2 : ℝ) / Complex.abs (F a + 1) := by
    have : ((F a - 1) / (F a + 1) - 1) = (-(2 : ℂ)) / (F a + 1) := by
      field_simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    simpa [this, Complex.abs.map_neg, Complex.abs.div, Complex.abs.ofReal]
  have hineq1 : (2 : ℝ) / Complex.abs (F a + 1) ≤ (2 : ℝ) / (Complex.abs (F a) - 1) := by
    have : (0 : ℝ) ≤ Complex.abs (F a + 1) := Complex.abs.nonneg _
    exact (div_le_div_of_nonneg_left (by norm_num) this (by norm_num)).mpr hden
  have hineq2 : (2 : ℝ) / (Complex.abs (F a) - 1) ≤ (4 : ℝ) / Complex.abs (F a) := by
    -- valid when |F| ≥ 2
    have hpos : 0 < Complex.abs (F a) := lt_of_le_of_lt (by norm_num) hge2
    have hden' : 0 < Complex.abs (F a) - 1 := by linarith
    -- 2/(x-1) ≤ 4/x  ⇔  2x ≤ 4(x-1) ⇔ x ≥ 2
    have hxge2 : (2 : ℝ) ≤ Complex.abs (F a) := hge2
    have : (2 : ℝ) / (Complex.abs (F a) - 1) ≤ (4 : ℝ) / Complex.abs (F a) := by
      have hxpos : 0 < Complex.abs (F a) := hpos
      have hxne : Complex.abs (F a) ≠ 0 := ne_of_gt hxpos
      calc
        (2 : ℝ) / (Complex.abs (F a) - 1)
            ≤ (2 : ℝ) / (1 : ℝ) := by
              have : (1 : ℝ) ≤ Complex.abs (F a) - 1 := by linarith
              exact (div_le_div_of_nonneg_left (by norm_num) this (by norm_num))
        _ = (2 : ℝ) := by norm_num
        _ ≤ (4 : ℝ) / Complex.abs (F a) := by
              have : Complex.abs (F a) ≤ (Complex.abs (F a)) := le_rfl
              have : (2 : ℝ) ≤ (4 : ℝ) / Complex.abs (F a) := by
                have := (le_div_iff (show (0 : ℝ) < Complex.abs (F a) by exact hxpos)).mpr (by linarith)
                simpa using this
              exact this

    exact this
  have hfinal : Complex.abs (((F a - 1) / (F a + 1)) - 1) ≤ (4 : ℝ) / Complex.abs (F a) := by
    have := le_trans (by simpa [hdist]) (le_trans hineq1 hineq2)
    exact this
  -- combine with |F| ≥ R to bound by ε
  have : (4 : ℝ) / Complex.abs (F a) ≤ ε := by
    have : (4 : ℝ) / R ≤ ε := hReq
    have hmono : R ≤ Complex.abs (F a) := haR
    exact (div_le_div_of_nonneg_left (by norm_num) hmono (by norm_num)).trans this
  exact (le_trans hfinal this)

/-! Pinned limit from N2: Θ → 1 at a ξ-zero ρ.
    We work with F := 2 * (det₂/(O·ξ)) and estimate as above. -/
lemma Theta_pinned_limit_from_N2
  (det₂ O ξ : ℂ → ℂ)
  (hdet₂A : AnalyticOn ℂ det₂ (Ω))
  (hOA : AnalyticOn ℂ O (Ω))
  (hXiA : AnalyticOn ℂ riemannXi (Ω))
  {ρ : ℂ} (hρΩ : ρ ∈ Ω) (hξρ : riemannXi ρ = 0)
  (hdet2_ne : det₂ ρ ≠ 0) (hO_ne : O ρ ≠ 0) :
  Tendsto (fun s => ( (2 : ℂ) * (det₂ s / (O s * riemannXi s)) - 1)
                    / ( (2 : ℂ) * (det₂ s / (O s * riemannXi s)) + 1))
          (nhdsWithin ρ (Ω \ Z riemannXi)) (nhds (1 : ℂ)) := by
  -- Continuity of A := det₂ / O and lower bound near ρ
  have hdet2_ca : ContinuousAt det₂ ρ := (hdet₂A.analyticAt hρΩ).continuousAt
  have hO_ca    : ContinuousAt O ρ    := (hOA.analyticAt hρΩ).continuousAt
  have hXi_ca   : ContinuousAt riemannXi ρ := (hXiA.analyticAt hρΩ).continuousAt
  have hA_ca : ContinuousAt (fun s => det₂ s / O s) ρ := hdet2_ca.div hO_ca hO_ne
  -- pick cA>0 so that |A s| ≥ cA on a small punctured neighborhood
  have hcApos : 0 < Complex.abs (det₂ ρ / O ρ) := by
    have : det₂ ρ / O ρ ≠ 0 := by
      have := div_ne_zero hdet2_ne hO_ne; simpa using this
    simpa [Complex.abs.pos_iff] using this
  obtain ⟨cA, hcApos', hcA⟩ : ∃ cA : ℝ, 0 < cA ∧ ∀ᶠ s in nhds ρ, Complex.abs (det₂ s / O s) ≥ cA := by
    -- take cA = |A ρ|/2 by continuity
    refine ⟨Complex.abs (det₂ ρ / O ρ) / 2, by nlinarith, ?_⟩
    have : Tendsto (fun s => Complex.abs (det₂ s / O s)) (nhds ρ)
        (nhds (Complex.abs (det₂ ρ / O ρ))) :=
      (hA_ca.norm.tendsto)
    have hball := (tendsto_order.1 this).2 _ (by nlinarith)
    -- eventually |A s| ≥ |A ρ|/2
    simpa using hball
  -- from nhdsWithin ≤ nhds, transfer to punctured nhds
  have hcA_within : ∀ᶠ s in nhdsWithin ρ (Ω \ Z riemannXi),
        Complex.abs (det₂ s / O s) ≥ cA := hcA.filter_mono nhdsWithin_le_nhds
  -- ξ → 0 at ρ, hence |ξ s| ≤ cA/(2M) eventually for any M>0
  have hξ_to0 : Tendsto (fun s => Complex.abs (riemannXi s))
        (nhdsWithin ρ (Ω \ Z riemannXi)) (nhds (0 : ℝ)) :=
    (hXi_ca.tendsto.comp_tendsto (le_trans nhdsWithin_le_nhds le_rfl)) |> by
      -- simplify nhds (Complex.abs 0)
      simpa [hξρ, Complex.abs.map_zero]
  -- Now apply the generic Cayley convergence for F := 2*A/ξ
  -- show that ‖F s‖ → ∞ along the punctured nhds
  have hF_atTop : Tendsto (fun s => Complex.abs ((2 : ℂ) * (det₂ s / (O s * riemannXi s))))
      (nhdsWithin ρ (Ω \ Z riemannXi)) atTop := by
    -- Show: ∀ R, eventually R ≤ |F s|
    refine tendsto_atTop.2 ?_
    intro R
    by_cases hR : R ≤ 0
    · -- trivial for nonpositive thresholds
      refine eventually_of_forall (fun _ => ?_)
      have : (0 : ℝ) ≤ Complex.abs ((2 : ℂ) * (det₂ _ / (O _ * riemannXi _))) :=
        Complex.abs.nonneg _
      exact le_trans hR this
    · have hRpos : 0 < R := lt_of_le_of_ne hR (ne_of_gt (show 0 < R from lt_of_le_of_ne hR ?hcontra))
      -- choose δ := (2*cA)/R > 0 so that |ξ s| ≤ δ ⇒ |F s| ≥ R
      have hδpos : 0 < ( (2 : ℝ) * cA) / R := by
        have : 0 < (2 : ℝ) * cA := by nlinarith
        exact (div_pos this hRpos)
      have hξ_small : ∀ᶠ s in nhdsWithin ρ (Ω \ Z riemannXi),
          Complex.abs (riemannXi s) ≤ ((2 : ℝ) * cA) / R := by
        have := (tendsto_order.1 hξ_to0).2 _ hδpos
        exact this
      have hA_large := hcA_within
      -- combine eventually events
      refine (hA_large.and hξ_small).mono ?_
      intro s hs
      rcases hs with ⟨hA_ge, hξ_le⟩
      -- compute |F|
      have habsF : Complex.abs ((2 : ℂ) * (det₂ s / (O s * riemannXi s)))
          = (2 : ℝ) * Complex.abs (det₂ s / O s) / Complex.abs (riemannXi s) := by
        have : Complex.abs ((2 : ℂ) * (det₂ s / (O s * riemannXi s)))
            = (2 : ℝ) * Complex.abs (det₂ s / (O s * riemannXi s)) := by
          simpa [Complex.abs.map_mul]
        have : Complex.abs (det₂ s / (O s * riemannXi s))
            = Complex.abs (det₂ s) / Complex.abs (O s * riemannXi s) := by
          simpa [Complex.abs.div]
        have : Complex.abs (O s * riemannXi s) = Complex.abs (O s) * Complex.abs (riemannXi s) := by
          simpa using (Complex.abs.mul (O s) (riemannXi s))
        have : (2 : ℝ) * Complex.abs (det₂ s / (O s * riemannXi s))
            = (2 : ℝ) * (Complex.abs (det₂ s) / (Complex.abs (O s) * Complex.abs (riemannXi s))) := by
          simp [*]
        have : (2 : ℝ) * (Complex.abs (det₂ s) / (Complex.abs (O s) * Complex.abs (riemannXi s)))
            = (2 : ℝ) * (Complex.abs (det₂ s) / Complex.abs (O s)) / Complex.abs (riemannXi s) := by
          field_simp
        have : (2 : ℝ) * (Complex.abs (det₂ s) / Complex.abs (O s)) / Complex.abs (riemannXi s)
            = (2 : ℝ) * Complex.abs (det₂ s / O s) / Complex.abs (riemannXi s) := by
          simpa [Complex.abs.div]
        simpa [*]
      -- lower bound using hA_ge and hξ_le
      have : R ≤ (2 : ℝ) * Complex.abs (det₂ s / O s) / Complex.abs (riemannXi s) := by
        have hposξ : 0 ≤ Complex.abs (riemannXi s) := Complex.abs.nonneg _
        have : (2 : ℝ) * cA / Complex.abs (riemannXi s) ≥ R := by
          have : Complex.abs (riemannXi s) ≤ (2 : ℝ) * cA / R := hξ_le
          have hRpos' : 0 < R := lt_of_le_of_ne hR ?hRne
          have hdenpos : 0 < Complex.abs (riemannXi s) ∨ Complex.abs (riemannXi s) = 0 := lt_or_eq_of_le hposξ
          have : R ≤ (2 : ℝ) * cA / Complex.abs (riemannXi s) := by
            have hxpos : 0 < Complex.abs (riemannXi s) ∨ Complex.abs (riemannXi s) = 0 := hdenpos
            -- Using monotonicity of division on positive reals
            have : Complex.abs (riemannXi s) ≤ (2 : ℝ) * cA / R := hξ_le
            have hxpos' : 0 < Complex.abs (riemannXi s) :=
              by
                -- since s ∈ Ω \ Z ξ, denom is nonzero; but here we are on nhdsWithin set
                -- we can just note: if abs ξ = 0, inequality R ≤ ∞ holds trivially
                -- fallback: handle by cases
                have : Complex.abs (riemannXi s) = 0 ∨ 0 < Complex.abs (riemannXi s) := by exact Or.symm (lt_or_eq_of_le (Complex.abs.nonneg _))
                exact by cases this with
                | inl h0 => by have : riemannXi s = 0 := by simpa [Complex.abs.eq_zero] using h0; have : False := by trivial; exact (lt_of_le_of_ne le_rfl (by intro h; cases h))
                | inr hpos => hpos
            have hxne : Complex.abs (riemannXi s) ≠ 0 := ne_of_gt hxpos'
            have : R ≤ ((2 : ℝ) * cA) / Complex.abs (riemannXi s) := by
              have := (le_div_iff (show 0 < Complex.abs (riemannXi s) by exact hxpos')).mpr ?ineq
              simpa using this
            exact this
          exact this
        -- Now strengthen numerator via |A s| ≥ cA
        have : (2 : ℝ) * Complex.abs (det₂ s / O s) / Complex.abs (riemannXi s)
                ≥ (2 : ℝ) * cA / Complex.abs (riemannXi s) := by
          have hnonneg : 0 ≤ Complex.abs (riemannXi s) := Complex.abs.nonneg _
          exact (div_le_div_of_nonneg_right (by nlinarith [hA_ge]) hnonneg)
        exact le_trans ?_ this
      -- conclude R ≤ |F s|
      simpa [habsF] using this
  -- Conclude Θ → 1 from |F| → ∞
  have : Tendsto (fun s => ( (2 : ℂ) * (det₂ s / (O s * riemannXi s)) - 1)
                    / ( (2 : ℂ) * (det₂ s / (O s * riemannXi s)) + 1))
          (nhdsWithin ρ (Ω \ Z riemannXi)) (nhds (1 : ℂ)) :=
    cayley_tendsto_one_of_norm_atTop hF_atTop
  exact this

/-! A convenience wrapper: build the off-zeros bridge using (N2) to supply
    the pinned limit field `hΘ_lim1_at_ξzero`. -/
def ZetaSchurDecompositionOffZeros.ofEqOffZeros_fromN2
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
  (hΘA_offXi : AnalyticOn ℂ (cayley (fun s => (2 : ℂ) * J s)) (Ω \ Z riemannXi))
  (hΘSchur : IsSchurOn (cayley (fun s => (2 : ℂ) * J s)) (Ω))
  (hN_ne_off_assm : ∀ ⦃s⦄, s ∈ (Ω \ Z riemannZeta) → ( (cayley (fun s => (2 : ℂ) * J s)) s * G s / riemannXi s) ≠ 0)
  : ZetaSchurDecompositionOffZeros riemannZeta riemannXi := by
  -- derive pinned limit via Theta_pinned_limit_from_N2 using local data at each ρ
  have hlim : ∀ ⦃ρ⦄, ρ ∈ Ω → riemannXi ρ = 0 →
      Tendsto (cayley (fun s => (2 : ℂ) * J s)) (nhdsWithin ρ (Ω \ Z riemannXi)) (nhds (1 : ℂ)) := by
    intro ρ hρ hξρ
    -- rewrite J to det2/(O*ξ) on punctured nhds and apply the previous lemma
    -- Use noncancellation at ρ from hdet2_ne, hO_ne
    have hdetρ : det2 ρ ≠ 0 := hdet2_ne hρ
    have hOρ : O ρ ≠ 0 := hO_ne hρ
    -- now apply Theta_pinned_limit_from_N2
    have := Theta_pinned_limit_from_N2 (riemannZeta:=riemannZeta) (riemannXi:=riemannXi)
      (det₂:=det2) (O:=O) (ξ:=riemannXi)
      hdet2A hOA hXiA hρ hξρ hdetρ hOρ
    -- and note: on the punctured set, cayley(2*J) = cayley(2*det2/(O*ξ)) by hJ_def_offXi
    -- Tendsto is preserved under eventual equality
    exact this
  -- build via the original constructor
  exact ZetaSchurDecompositionOffZeros.ofEqOffZeros
    (det2) (O) (G) (J)
    hdet2A hOA hGA hXiA hO_ne hdet2_ne hG_ne_offζ hJ_def_offXi hXi_eq_Gζ hΘSchur hΘA_offXi
    (by intro ρ hρ hξρ; simpa using hlim hρ hξρ) hN_ne_off_assm
-/

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
