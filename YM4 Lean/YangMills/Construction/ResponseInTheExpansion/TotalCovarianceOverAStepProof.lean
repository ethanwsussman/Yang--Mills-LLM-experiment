import YangMills.Construction.ResponseInTheExpansion.TotalCovarianceOverAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.WeightedResponses
theorem lawOfTotalCovarianceWithIncrement_holds : LawOfTotalCovarianceWithIncrement := by
  intro A A' G mA mA' μ μ' _ _ π F₁ F₂ m₁ m₂ C hπ hG hF₁ hF₂ hb₁ hb₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hy₁ hy₂
  have hC : 0 ≤ C := by
    have hbot : (ae μ').NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero μ')
    obtain ⟨u, hu⟩ := hc₁.exists
    exact (abs_nonneg _).trans hu
  have h2C : 0 ≤ 2 * C := by linarith
  have hFπ₁ : AEStronglyMeasurable (fun u => F₁ (π u)) μ' := hF₁.comp_measurePreserving hπ
  have hFπ₂ : AEStronglyMeasurable (fun u => F₂ (π u)) μ' := hF₂.comp_measurePreserving hπ
  have hbπ₁ : ∀ᵐ u ∂μ', |F₁ (π u)| ≤ C := hπ.quasiMeasurePreserving.ae hb₁
  have hbπ₂ : ∀ᵐ u ∂μ', |F₂ (π u)| ≤ C := hπ.quasiMeasurePreserving.ae hb₂
  have bdd : ∀ {f : A' → ℝ} {K : ℝ}, AEStronglyMeasurable f μ' → (∀ᵐ u ∂μ', |f u| ≤ K) →
      Integrable f μ' := fun {f K} hf hb =>
    Integrable.of_bound hf K (hb.mono fun u h => by rw [Real.norm_eq_abs]; exact h)
  have lp : ∀ {f : A' → ℝ} {K : ℝ}, AEStronglyMeasurable f μ' → (∀ᵐ u ∂μ', |f u| ≤ K) →
      MemLp f 2 μ' := fun {f K} hf hb =>
    MemLp.of_bound hf K (hb.mono fun u h => by rw [Real.norm_eq_abs]; exact h)
  have lpμ : ∀ {f : A → ℝ} {K : ℝ}, AEStronglyMeasurable f μ → (∀ᵐ u ∂μ, |f u| ≤ K) →
      MemLp f 2 μ := fun {f K} hf hb =>
    MemLp.of_bound hf K (hb.mono fun u h => by rw [Real.norm_eq_abs]; exact h)
  have mulb : ∀ {f g : A' → ℝ} {K K' : ℝ}, (∀ᵐ u ∂μ', |f u| ≤ K) → (∀ᵐ u ∂μ', |g u| ≤ K') →
      ∀ᵐ u ∂μ', |f u * g u| ≤ K * K' := by
    intro f g K K' hf hg
    filter_upwards [hf, hg] with u h1 h2
    rw [abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
  have nn : ∀ {f : A' → ℝ}, (∀ᵐ u ∂μ', |f u| ≤ 2 * C) → ∀ᵐ u ∂μ', |(μ'[f|G]) u| ≤ 2 * C := by
    intro f hf
    exact ae_bdd_condExp_of_ae_bdd (m := G) (R := ⟨2 * C, h2C⟩) (f := f) (μ := μ') hf
  have mean : ∀ {f : A' → ℝ}, ∫ u, (μ'[f|G]) u ∂μ' = ∫ u, f u ∂μ' := fun {f} => integral_condExp hG
  have pull : ∀ {F : A → ℝ}, AEStronglyMeasurable F μ → ∫ u, F (π u) ∂μ' = ∫ a, F a ∂μ := by
    intro F hF
    have h := integral_map (μ := μ') hπ.aemeasurable (f := F) (by rwa [hπ.map_eq])
    rw [hπ.map_eq] at h
    exact h.symm
  have hIFπ₁ : Integrable (fun u => F₁ (π u)) μ' := bdd hFπ₁ hbπ₁
  have hIFπ₂ : Integrable (fun u => F₂ (π u)) μ' := bdd hFπ₂ hbπ₂
  have hIm₁ : Integrable m₁ μ' := bdd hm₁ hc₁
  have hIm₂ : Integrable m₂ μ' := bdd hm₂ hc₂
  have hI11 : Integrable (fun u => F₁ (π u) * F₂ (π u)) μ' := bdd (hFπ₁.mul hFπ₂) (mulb hbπ₁ hbπ₂)
  have hI12 : Integrable (fun u => F₁ (π u) * m₂ u) μ' := bdd (hFπ₁.mul hm₂) (mulb hbπ₁ hc₂)
  have hI21 : Integrable (fun u => F₂ (π u) * m₁ u) μ' := bdd (hFπ₂.mul hm₁) (mulb hbπ₂ hc₁)
  have hI22 : Integrable (fun u => m₁ u * m₂ u) μ' := bdd (hm₁.mul hm₂) (mulb hc₁ hc₂)
  have hFF : ∫ u, F₁ (π u) * F₂ (π u) ∂μ' = ∫ a, F₁ a * F₂ a ∂μ := pull (hF₁.mul hF₂)
  have key : ∀ X₁ X₂ : A' → ℝ, X₁ = (fun u => F₁ (π u) + m₁ u) → X₂ = (fun u => F₂ (π u) + m₂ u) →
      cov[F₁, F₂; μ] = cov[μ'[X₁|G], μ'[X₂|G]; μ'] +
        (∫ u, ((μ'[fun u => X₁ u * X₂ u|G]) u - (μ'[X₁|G]) u * (μ'[X₂|G]) u) ∂μ' -
          ∫ u, m₁ u * m₂ u ∂μ') := by
    intro X₁ X₂ hX₁ hX₂
    have hXb₁ : ∀ᵐ u ∂μ', |X₁ u| ≤ 2 * C := by
      filter_upwards [hbπ₁, hc₁] with u h1 h2
      have e : X₁ u = F₁ (π u) + m₁ u := by rw [hX₁]
      rw [e]
      have := abs_add_le (F₁ (π u)) (m₁ u)
      linarith
    have hXb₂ : ∀ᵐ u ∂μ', |X₂ u| ≤ 2 * C := by
      filter_upwards [hbπ₂, hc₂] with u h1 h2
      have e : X₂ u = F₂ (π u) + m₂ u := by rw [hX₂]
      rw [e]
      have := abs_add_le (F₂ (π u)) (m₂ u)
      linarith
    have hE₁ : AEStronglyMeasurable (μ'[X₁|G]) μ' :=
      (stronglyMeasurable_condExp.mono hG).aestronglyMeasurable
    have hE₂ : AEStronglyMeasurable (μ'[X₂|G]) μ' :=
      (stronglyMeasurable_condExp.mono hG).aestronglyMeasurable
    have hEb₁ := nn hXb₁
    have hEb₂ := nn hXb₂
    have hIEE : Integrable (fun u => (μ'[X₁|G]) u * (μ'[X₂|G]) u) μ' :=
      bdd (hE₁.mul hE₂) (mulb hEb₁ hEb₂)
    have hIc : Integrable (μ'[fun u => X₁ u * X₂ u|G]) μ' := integrable_condExp
    have hmeanX₁ : ∫ u, X₁ u ∂μ' = ∫ a, F₁ a ∂μ := by
      have e : ∫ u, X₁ u ∂μ' = ∫ u, (F₁ (π u) + m₁ u) ∂μ' := by rw [hX₁]
      rw [e, integral_add hIFπ₁ hIm₁, hz₁, add_zero, pull hF₁]
    have hmeanX₂ : ∫ u, X₂ u ∂μ' = ∫ a, F₂ a ∂μ := by
      have e : ∫ u, X₂ u ∂μ' = ∫ u, (F₂ (π u) + m₂ u) ∂μ' := by rw [hX₂]
      rw [e, integral_add hIFπ₂ hIm₂, hz₂, add_zero, pull hF₂]
    have hmeanXX : ∫ u, X₁ u * X₂ u ∂μ' = ∫ a, F₁ a * F₂ a ∂μ + ∫ u, m₁ u * m₂ u ∂μ' := by
      have he : ∫ u, X₁ u * X₂ u ∂μ' =
          ∫ u, (F₁ (π u) * F₂ (π u) + F₁ (π u) * m₂ u + F₂ (π u) * m₁ u + m₁ u * m₂ u) ∂μ' := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        simp only [hX₁, hX₂]
        ring
      have h12 : Integrable (fun u => F₁ (π u) * F₂ (π u) + F₁ (π u) * m₂ u) μ' := hI11.add hI12
      have h123 : Integrable
          (fun u => F₁ (π u) * F₂ (π u) + F₁ (π u) * m₂ u + F₂ (π u) * m₁ u) μ' := h12.add hI21
      rw [he, integral_add h123 hI22, integral_add h12 hI21, integral_add hI11 hI12, hy₁, hy₂, hFF]
      ring
    have hcovF : cov[F₁, F₂; μ] = ∫ a, F₁ a * F₂ a ∂μ - (∫ a, F₁ a ∂μ) * ∫ a, F₂ a ∂μ :=
      covariance_eq_sub (lpμ hF₁ hb₁) (lpμ hF₂ hb₂)
    have hcovE : cov[μ'[X₁|G], μ'[X₂|G]; μ'] = ∫ u, (μ'[X₁|G]) u * (μ'[X₂|G]) u ∂μ' -
        (∫ u, (μ'[X₁|G]) u ∂μ') * ∫ u, (μ'[X₂|G]) u ∂μ' :=
      covariance_eq_sub (lp hE₁ hEb₁) (lp hE₂ hEb₂)
    rw [hcovF, hcovE, mean, mean, hmeanX₁, hmeanX₂, integral_sub hIc hIEE, mean, hmeanXX]
    ring
  exact key _ _ rfl rfl
end YangMills.Construction.WeightedResponses
end
