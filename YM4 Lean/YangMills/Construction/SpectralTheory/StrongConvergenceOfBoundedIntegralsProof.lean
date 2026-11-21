import YangMills.Construction.SpectralTheory.BoundedBorelCalculus
import YangMills.Construction.SpectralTheory.StrongConvergenceOfBoundedIntegrals
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace
noncomputable section
namespace YangMills.Construction.BorelCalculus
open YangMills.Construction.BorelSpectral
theorem norm_integralOp_sub_sq {n : ℕ} {Y : Set (Fin n → ℝ)} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : SpectralMeasure Y H) (hE : BoundedFunctionalCalculus E)
    {u v : Y → ℂ} (hu : Measurable u) (hub : IsBoundedFn u) (hv : Measurable v)
    (hvb : IsBoundedFn v) (ψ : H) :
    ‖E.integralOp u ψ - E.integralOp v ψ‖ ^ 2 =
      ∫ y, ‖u y - v y‖ ^ 2 ∂E.diagMeasure ψ := by
  have hnv : Measurable ((-1 : ℂ) • v) := hv.const_smul _
  have hnvb : IsBoundedFn ((-1 : ℂ) • v) := by
    obtain ⟨c, hc⟩ := hvb
    exact ⟨c, fun y => by simpa using hc y⟩
  have hsum : Measurable (u + (-1 : ℂ) • v) := hu.add hnv
  have hsumb : IsBoundedFn (u + (-1 : ℂ) • v) := by
    obtain ⟨a, ha⟩ := hub
    obtain ⟨b, hb⟩ := hnvb
    exact ⟨a + b, fun y => (norm_add_le _ _).trans (add_le_add (ha y) (hb y))⟩
  have h₁ := hE.norm_sq _ hsum hsumb ψ
  rw [hE.add u _ hu hub hnv hnvb, hE.smul (-1) v hv hvb] at h₁
  have h₂ : (E.integralOp u + (-1 : ℂ) • E.integralOp v) ψ =
      E.integralOp u ψ - E.integralOp v ψ := by
    simp [sub_eq_add_neg]
  rw [h₂] at h₁
  rw [h₁]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [sub_eq_add_neg]
theorem strongConvergenceHolds
    (hB : YangMills.Construction.SpectralTheory.BoundedBorelCalculus.BoundedBorelCalculusHolds) :
    StrongConvergenceHolds := by
  intro H _ _ _ n Y E f g c Δ₀ hf hg hfc hcar hlim
  have hE : BoundedFunctionalCalculus E := hB H n Y E
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = max c 0 := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := hC ▸ le_max_right _ _
  have hfC : ∀ r y, ‖f r y‖ ≤ C := fun r y => (hfc r y).trans (hC ▸ le_max_left _ _)
  have hnull : ∀ ψ, ∀ᵐ y ∂E.diagMeasure ψ, y ∈ Δ₀.1 := fun ψ => by
    have h₀ : E.diagMeasure ψ Δ₀.1ᶜ = 0 := by
      have h₁ := E.diagMeasure_apply ψ ⟨Δ₀.1ᶜ, Δ₀.2.compl⟩
      have h₂ : E ⟨Δ₀.1ᶜ, Δ₀.2.compl⟩ = 0 := hcar
      rw [h₂] at h₁
      simpa using h₁
    filter_upwards [compl_mem_ae_iff.mpr h₀] with y hy
    simpa using hy
  have hgC : ∀ y ∈ Δ₀.1, ‖g y‖ ≤ C := fun y hy =>
    le_of_tendsto (hlim y hy).norm (Eventually.of_forall fun r => hfC r y)
  obtain ⟨gt, hgt⟩ : ∃ gt : Y → ℂ, gt = Δ₀.1.indicator g := ⟨_, rfl⟩
  have hgtm : Measurable gt := hgt ▸ hg.indicator Δ₀.2
  have hgtC : ∀ y, ‖gt y‖ ≤ C := fun y => by
    by_cases hy : y ∈ Δ₀.1
    · rw [hgt, indicator_of_mem hy]
      exact hgC y hy
    · rw [hgt, indicator_of_notMem hy, norm_zero]
      exact hC0
  have hgtg : ∀ y ∈ Δ₀.1, gt y = g y := fun y hy => by rw [hgt, indicator_of_mem hy]
  have hgtb : IsBoundedFn gt := ⟨C, hgtC⟩
  refine ⟨eq_univ_of_forall fun ψ => ?_, fun ψ => ?_⟩
  · show ∫⁻ y, ‖g y‖ₑ ^ 2 ∂E.diagMeasure ψ < ∞
    have hle : ∀ᵐ y ∂E.diagMeasure ψ, ‖g y‖ₑ ^ 2 ≤ ENNReal.ofReal C ^ 2 := by
      filter_upwards [hnull ψ] with y hy
      gcongr
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hgC y hy)
    refine (lintegral_mono_ae hle).trans_lt ?_
    rw [lintegral_const]
    exact ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)
  · have hval : E.integralApply g ψ = E.integralOp gt ψ := by
      refine Tendsto.limUnder_eq (tendsto_const_nhds.congr' ?_)
      obtain ⟨r₀, hr₀⟩ := exists_nat_ge C
      filter_upwards [eventually_ge_atTop r₀] with s hs
      have hsC : C ≤ s := hr₀.trans (by exact_mod_cast hs)
      have htm : Measurable (truncate g s) :=
        hg.indicator (measurableSet_le hg.norm measurable_const)
      have htb : IsBoundedFn (truncate g s) := by
        refine ⟨s, fun y => ?_⟩
        unfold truncate
        by_cases hy : ‖g y‖ ≤ (s : ℝ)
        · rw [indicator_of_mem (show y ∈ {y | ‖g y‖ ≤ (s : ℝ)} from hy)]
          exact hy
        · rw [indicator_of_notMem (show y ∉ {y | ‖g y‖ ≤ (s : ℝ)} from hy), norm_zero]
          positivity
      have h₀ := norm_integralOp_sub_sq E hE hgtm hgtb htm htb ψ
      have hz : ∫ y, ‖gt y - truncate g s y‖ ^ 2 ∂E.diagMeasure ψ = 0 := by
        refine integral_eq_zero_of_ae ?_
        filter_upwards [hnull ψ] with y hy
        have hy' : y ∈ {y | ‖g y‖ ≤ (s : ℝ)} := (hgC y hy).trans hsC
        simp [truncate, indicator_of_mem hy', hgtg y hy]
      rw [hz] at h₀
      have h₁ : ‖E.integralOp gt ψ - E.integralOp (truncate g s) ψ‖ = 0 :=
        pow_eq_zero_iff (two_ne_zero) |>.mp h₀
      exact sub_eq_zero.mp (norm_eq_zero.mp h₁)
    rw [hval]
    have hn : Tendsto (fun r => ‖E.integralOp (f r) ψ - E.integralOp gt ψ‖ ^ 2) atTop
        (𝓝 0) := by
      have heq : (fun r => ‖E.integralOp (f r) ψ - E.integralOp gt ψ‖ ^ 2) =
          fun r => ∫ y, ‖f r y - gt y‖ ^ 2 ∂E.diagMeasure ψ :=
        funext fun r => norm_integralOp_sub_sq E hE (hf r) ⟨C, hfC r⟩ hgtm hgtb ψ
      rw [heq]
      have hdom := tendsto_integral_of_dominated_convergence (μ := E.diagMeasure ψ)
        (F := fun r y => ‖f r y - gt y‖ ^ 2) (f := fun _ => (0 : ℝ))
        (fun _ => (C + C) ^ 2)
        (fun r => (((hf r).sub hgtm).norm.pow_const 2).aestronglyMeasurable)
        (integrable_const _)
        (fun r => Eventually.of_forall fun y => by
          have hb : ‖f r y - gt y‖ ≤ C + C :=
            (norm_sub_le _ _).trans (add_le_add (hfC r y) (hgtC y))
          rw [Real.norm_of_nonneg (by positivity)]
          gcongr)
        (by
          filter_upwards [hnull ψ] with y hy
          have h₁ : Tendsto (fun r => f r y - gt y) atTop (𝓝 0) := by
            have := (hlim y hy).sub_const (g y)
            simpa [hgtg y hy] using this
          simpa using h₁.norm.pow 2)
      simpa using hdom
    have hn' : Tendsto (fun r => ‖E.integralOp (f r) ψ - E.integralOp gt ψ‖) atTop
        (𝓝 0) := by
      simpa [Real.sqrt_sq (norm_nonneg _)] using hn.sqrt
    exact tendsto_iff_norm_sub_tendsto_zero.mpr hn'
end YangMills.Construction.BorelCalculus
