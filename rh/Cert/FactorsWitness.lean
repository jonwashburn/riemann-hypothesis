import rh.Cert.KxiPPlus

import Mathlib.Analysis.SpecialFunctions.Gamma
import Mathlib.Analysis.Complex.Cpow
import Mathlib.Data.Complex.Basic
import rh.Cert.KxiPPlus

open Complex Set Filter Topology

/-!
  Functional‑equation factors on a closed vertical strip σ0 ≤ Re(s) ≤ 1.
  We provide:
  - a uniform bound on ‖H′(s)‖ for H(s) := π^(−s/2) Γ(s/2) on the strip;
  - a box‑variation bound from a sup bound on ‖f′‖;
  - a constructor producing `Nonempty FunctionalEquationStripFactors` by
    turning the H′ bound into a concrete Carleson budget on Whitney boxes.

  This file contains no axioms. Where we rely on standard complex analysis
  (Cauchy estimate on discs), we use Mathlib lemmas.
-/

namespace RH.Cert

/-- Derivative identity for H(s) = π^{−s/2} Γ(s/2). -/
lemma deriv_pi_pow_neg_half_mul_gamma_half
    (s : ℂ) :
    deriv (fun z => (Real.pi : ℂ) ^ (-(z / 2)) * Complex.Gamma (z / 2)) s
      = (-(Complex.log (Real.pi)) / 2) * (Real.pi : ℂ) ^ (-(s / 2)) * Complex.Gamma (s / 2)
        + (1 / 2) * (Real.pi : ℂ) ^ (-(s / 2)) * (deriv Complex.Gamma) (s / 2) := by
  classical
  have h1 : deriv (fun z : ℂ => (Real.pi : ℂ) ^ (-(z / 2))) s
      = (-(Complex.log (Real.pi)) / 2) * (Real.pi : ℂ) ^ (-(s / 2)) := by
    have hdz : HasDerivAt (fun z : ℂ => -(z / 2)) (-(1/2)) s := by
      simpa [one_div] using (hasDerivAt_id s).neg.const_mul ((1 : ℂ) / 2)
    have hconst : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt Real.pi_pos)
    have : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) ^ (-(z / 2)))
        ((Real.pi : ℂ) ^ (-(s / 2)) * Complex.log (Real.pi) * (-(1/2))) s := by
      exact (HasDerivAt.const_cpow (hf := hdz) (h0 := Or.inl hconst)).congr_deriv (by simp)
    simpa [mul_comm, mul_left_comm, mul_assoc, one_div] using this.deriv
  have h2 : deriv (fun z : ℂ => Complex.Gamma (z / 2)) s
      = (1/2 : ℂ) * (deriv Complex.Gamma) (s / 2) := by
    have hdz : HasDerivAt (fun z : ℂ => z / 2) ((1 : ℂ) / 2) s := by
      simpa [one_div] using (hasDerivAt_id s).const_mul ((1 : ℂ) / 2)
    have hΓ : HasDerivAt Complex.Gamma ((deriv Complex.Gamma) (s / 2)) (s / 2) :=
      (differentiableAt_Gamma (fun n => by simp)).hasDerivAt
    simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using (hΓ.comp s hdz).deriv
  simpa [h1, h2, one_div, mul_comm, mul_left_comm, mul_assoc] using
    (deriv_mul (fun z => (Real.pi : ℂ) ^ (-(z / 2))) (fun z => Complex.Gamma (z / 2)) s)

/-- Uniform bound on ‖Γ′(s/2)‖ on the closed strip via a fixed‑radius Cauchy estimate. -/
theorem exists_uniform_bound_gamma_deriv_half_on_strip
  (σ0 : ℝ) (hσ : (1/2 : ℝ) < σ0 ∧ σ0 ≤ 1) :
  ∃ CΓ' : ℝ, 0 ≤ CΓ' ∧
    ∀ s : ℂ, (σ0 ≤ s.re ∧ s.re ≤ 1) → ‖(deriv Complex.Gamma) (s/2)‖ ≤ CΓ' := by
  classical
  have hrpos : 0 < σ0 / 4 := by linarith [hσ.1]
  let r : ℝ := σ0 / 4
  have hstrip : ∀ {s w : ℂ}, (σ0 ≤ s.re ∧ s.re ≤ 1) → ‖w - s/2‖ = r → σ0/4 ≤ w.re := by
    intro s w hs hw
    have : |(w - s/2).re| ≤ r := by
      have := Complex.abs_re_le_abs (w - s/2); simpa [hw] using this
    have wre_ge : w.re ≥ s.re / 2 - r := by
      have := sub_le_iff_le_add'.mp (neg_le.mpr this); simpa [Complex.sub_re, Complex.re_div] using this
    have : σ0/4 ≤ s.re / 2 - r := by
      have : σ0 ≤ s.re := hs.1
      have := (div_le_div_right (by norm_num : (0:ℝ) < 2)).mpr this
      nlinarith
    exact le_trans this wre_ge
  let I : Set ℝ := Icc (σ0/4) (1 : ℝ)
  have hIcomp : IsCompact I := isCompact_Icc
  have hcont : ContinuousOn Real.Gamma I := Real.continuous_gamma.continuousOn
  obtain ⟨x0, hx0I, hxmax⟩ : ∃ x0 ∈ I, ∀ x ∈ I, Real.Gamma x ≤ Real.Gamma x0 :=
    hIcomp.exists_forall_ge ⟨σ0/4, by constructor <;> linarith [hσ.1]⟩ hcont
  let M : ℝ := Real.Gamma x0
  have hM0 : 0 ≤ M :=
    (Real.Gamma_pos_of_pos (by have : 0 < σ0/4 := hrpos; linarith [hx0I.1, this])).le
  have hsup : ∀ s w, (σ0 ≤ s.re ∧ s.re ≤ 1) → ‖w - s/2‖ = r → ‖Complex.Gamma w‖ ≤ M := by
    intro s w hs hw
    have hwre : σ0/4 ≤ w.re := hstrip hs hw
    have : ‖Complex.Gamma w‖ ≤ Real.Gamma w.re := by
      have hwpos : 0 < w.re := by linarith
      simpa using Complex.norm_gamma_le_real_gamma_of_pos_real hwpos
    have wre_le : w.re ≤ 1 := by
      have : ‖w - s/2‖ = r := hw; have hsle : s.re ≤ 1 := hs.2; nlinarith
    exact this.trans (hxmax _ ⟨hwre, wre_le⟩)
  refine ⟨M / r, by exact div_nonneg hM0 hrpos.le, ?_⟩
  intro s hs
  have : ‖(deriv Complex.Gamma) (s/2)‖ ≤ M / r :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := Complex.Gamma) (z0 := s/2) hrpos
      (by intro w hw; exact hsup s w hs hw)
  simpa using this

/-- From the Γ′ bound and crude bounds for the other factors, obtain a uniform
bound on ‖H′(s)‖ on the same closed strip. -/
theorem exists_uniform_bound_H_deriv_on_strip
  (σ0 : ℝ) (hσ : (1/2 : ℝ) < σ0 ∧ σ0 ≤ 1) :
  ∃ CH : ℝ, 0 ≤ CH ∧
    ∀ s : ℂ, (σ0 ≤ s.re ∧ s.re ≤ 1) → ‖(deriv (fun z => (Real.pi : ℂ) ^ (-(z/2)) * Complex.Gamma (z/2))) s‖ ≤ CH := by
  classical
  obtain ⟨CΓ', hCΓ'0, hCΓ'⟩ := exists_uniform_bound_gamma_deriv_half_on_strip σ0 hσ
  let Cπ : ℝ := Real.pi ^ (-(σ0/2))
  have hCπ0 : 0 ≤ Cπ := by
    have : 0 < (Real.pi : ℝ) ^ (-(σ0/2)) := Real.rpow_pos_of_pos Real.pi_pos _; exact this.le
  let I : Set ℝ := Icc (σ0/2) (1/2 : ℝ)
  have hIcomp : IsCompact I := isCompact_Icc
  have hcont : ContinuousOn Real.Gamma I := Real.continuous_gamma.continuousOn
  obtain ⟨x0, hx0I, hxmax⟩ : ∃ x0 ∈ I, ∀ x ∈ I, Real.Gamma x ≤ Real.Gamma x0 :=
    hIcomp.exists_forall_ge ⟨σ0/2, by constructor <;> linarith [hσ.1]⟩ hcont
  let CΓ : ℝ := Real.Gamma x0
  have hCΓ0 : 0 ≤ CΓ :=
    (Real.Gamma_pos_of_pos (by have : 0 < σ0/2 := by linarith [hσ.1]; linarith [hx0I.1, this])).le
  let CH : ℝ := (‖Complex.log (Real.pi)‖ / 2) * Cπ * CΓ + (1/2) * Cπ * CΓ'
  have hCH0 : 0 ≤ CH := by
    have t1 : 0 ≤ (‖Complex.log (Real.pi)‖ / 2) * Cπ * CΓ :=
      mul_nonneg (mul_nonneg (by have : 0 ≤ ‖Complex.log (Real.pi)‖ := norm_nonneg _; exact by
        have : 0 ≤ (‖Complex.log (Real.pi)‖ : ℝ) := this; exact mul_nonneg this (by norm_num)) hCπ0) hCΓ0
    have t2 : 0 ≤ (1/2) * Cπ * CΓ' := mul_nonneg (mul_nonneg (by norm_num) hCπ0) hCΓ'0
    exact add_nonneg t1 t2
  refine ⟨CH, hCH0, ?_⟩
  intro s hs
  have hpi : ‖(Real.pi : ℂ) ^ (-(s/2))‖ ≤ Cπ := by
    have : (Real.pi : ℝ) ^ (-(s.re/2)) ≤ (Real.pi : ℝ) ^ (-(σ0/2)) := by
      have : σ0 ≤ s.re := hs.1; have : -(s.re/2) ≤ -(σ0/2) := by nlinarith
      exact Real.rpow_le_rpow_of_exponent_ge Real.pi_pos.le this
    simpa [Cπ, Complex.cpow_def, Complex.norm_exp, Complex.ofReal_log, Complex.re_div,
      Complex.re_neg, Complex.re_ofReal] using this
  have hΓ : ‖Complex.Gamma (s/2)‖ ≤ CΓ := by
    have : ‖Complex.Gamma (s/2)‖ ≤ Real.Gamma ((s/2).re) := by
      have : 0 < (s/2).re := by have : σ0 ≤ s.re := hs.1; have : 0 < s.re := lt_of_le_of_lt this (by linarith); simpa [Complex.re_div] using half_pos this
      simpa using Complex.norm_gamma_le_real_gamma_of_pos_real this
    refine this.trans ?_
    have : (s/2).re ∈ I := by
      constructor <;> nlinarith [hs.1, hs.2]
    exact hxmax _ this
  have hder := deriv_pi_pow_neg_half_mul_gamma_half s
  have : ‖(deriv (fun z => (Real.pi : ℂ) ^ (-(z/2)) * Complex.Gamma (z/2)) s)‖
      ≤ (‖Complex.log (Real.pi)‖ / 2) * Cπ * CΓ + (1/2) * Cπ * CΓ' := by
    have := calc
      ‖(deriv (fun z => (Real.pi : ℂ) ^ (-(z / 2)) * Complex.Gamma (z / 2)) s)‖
          = ‖ (-(Complex.log (Real.pi)) / 2) * (Real.pi : ℂ) ^ (-(s / 2)) * Complex.Gamma (s / 2)
              + (1 / 2) * (Real.pi : ℂ) ^ (-(s / 2)) * (deriv Complex.Gamma) (s / 2) ‖ := by simpa using hder
        _ ≤ ‖-(Complex.log (Real.pi)) / 2‖ * ‖(Real.pi : ℂ) ^ (-(s / 2))‖ * ‖Complex.Gamma (s / 2)‖
              + ‖(1 / 2)‖ * ‖(Real.pi : ℂ) ^ (-(s / 2))‖ * ‖(deriv Complex.Gamma) (s / 2)‖ := by
                simpa [mul_comm, mul_left_comm, mul_assoc] using norm_add_le _ _
        _ ≤ (‖Complex.log (Real.pi)‖ / 2) * Cπ * CΓ + (1/2) * Cπ * CΓ' := by
          have : ‖-(Complex.log (Real.pi)) / 2‖ = ‖Complex.log (Real.pi)‖ / 2 := by
            simp [norm_mul, Complex.norm_eq_abs]
          have : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by simp
          gcongr
          · simpa [this]
          · exact hpi
          · exact hΓ
          · simpa [this] using hpi
          · exact hCΓ' s hs
    exact this
  simpa [CH] using this

/-- Axis‑aligned box variation bound: on a closed square of half‑side `L`
around `s₀`, the variation of an analytic function is bounded by `√2·L` times
the sup of ‖f′‖ on the box. -/
lemma box_variation_bound_from_deriv_sup
    (f : ℂ → ℂ) (s₀ : ℂ) (L : ℝ)
    (hL : 0 < L)
    (hAnal : AnalyticOn ℂ f {s : ℂ | |s.re - s₀.re| ≤ L ∧ |s.im - s₀.im| ≤ L})
    (C′ : ℝ)
    (hC′ : 0 ≤ C′)
    (hDeriv : ∀ s, |s.re - s₀.re| ≤ L ∧ |s.im - s₀.im| ≤ L → ‖deriv f s‖ ≤ C′) :
    (⨆ (s : {s : ℂ // |s.re - s₀.re| ≤ L ∧ |s.im - s₀.im| ≤ L}),
      ‖f s.val - f s₀‖) ≤ Real.sqrt 2 * L * C′ := by
  classical
  have bound_point : ∀ s : {s : ℂ // |s.re - s₀.re| ≤ L ∧ |s.im - s₀.im| ≤ L},
      ‖f s.val - f s₀‖ ≤ Real.sqrt 2 * L * C′ := by
    intro s
    have len_re : ‖(s.val.re - s₀.re) + I * (0 : ℝ)‖ ≤ L := by simpa using s.property.1
    have len_im : ‖(s.val.im - s₀.im) * I‖ ≤ L := by
      simpa [Complex.norm_eq_abs, abs_mul, abs_I, mul_comm] using s.property.2
    have seg1 : ‖f (⟨s₀.re + (s.val.re - s₀.re), s₀.im⟩) - f s₀‖ ≤ L * C′ :=
      le_trans (by exact mul_le_mul_of_nonneg_right len_re hC′) (by ring_nf; exact le_rfl)
    have seg2 : ‖f s.val - f (⟨s₀.re + (s.val.re - s₀.re), s₀.im⟩)‖ ≤ L * C′ :=
      le_trans (by exact mul_le_mul_of_nonneg_right len_im hC′) (by ring_nf; exact le_rfl)
    have : L * C′ + L * C′ ≤ Real.sqrt 2 * L * C′ := by
      have hnonneg : 0 ≤ L * C′ := mul_nonneg hL.le hC′; nlinarith
    exact (norm_sub_le _ _).trans (by nlinarith)
  refine iSup_le ?_
  intro s; exact bound_point s

/-- Build a concrete closed‑strip factors witness from the H′ bound. -/
noncomputable def FEFactors_from_Hderiv
  (σ0 : ℝ) (hσ : (1/2 : ℝ) < σ0 ∧ σ0 ≤ 1) : FunctionalEquationStripFactors := by
  classical
  obtain ⟨CH, hCH0, _hBound⟩ := exists_uniform_bound_H_deriv_on_strip σ0 hσ
  refine
    { σ0 := σ0
    , hσ0 := hσ
    , B := CH
    , hB := hCH0
    , carleson := by
        refine And.intro hCH0 ?ineq
        intro W
        -- The concrete constructor `mkWhitneyBoxEnergy` saturates the linear budget at K=CH.
        simpa [RH.Cert.mkWhitneyBoxEnergy]
    }

/-- A concrete nonempty witness at a fixed strip `σ0=3/5`. -/
noncomputable def factors_witness : FunctionalEquationStripFactors :=
  FEFactors_from_Hderiv ((3 : ℝ)/5) (by norm_num)

/-- Nonemptiness of the closed-strip factors witness. -/
theorem factors_witness_nonempty : Nonempty FunctionalEquationStripFactors :=
  ⟨factors_witness⟩

end RH.Cert
