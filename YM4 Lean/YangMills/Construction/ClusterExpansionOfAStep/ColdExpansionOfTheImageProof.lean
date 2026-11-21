import YangMills.Construction.ClusterExpansionOfAStep.ColdExpansionOfTheImage
import YangMills.Construction.ClusterExpansionOfAStep.TheImageHasItsNumber
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusLumps StepSettings RenormalizationStepParameters ShareFamilies ImageColdExpansion
theorem weightGrowthSup_nonneg (rt n₁ : ℝ) : 0 ≤ weightGrowthSup rt n₁ := by
  unfold weightGrowthSup
  refine Real.iSup_nonneg fun m => mul_nonneg ?_ (Real.exp_pos _).le
  unfold expansionWeight
  exact mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (Real.exp_pos _).le
theorem imageHasColdExpansion_of (hnum : ImageCarriesItsNumber) (hcold : ColdExpansionOfDensities) :
    ImageHasColdExpansion := by
  obtain ⟨rt₀, hrt₀, h⟩ := hnum
  refine ⟨rt₀, hrt₀, fun T hT hC hr => ?_⟩
  obtain ⟨y₀, hy⟩ := h T hT hC hr
  refine ⟨y₀, fun y hy₀ R hR hA => ?_⟩
  have H := hy y hy₀ R hR hA
  have hcoupling : R.params.coupling = T.coupling := by
    rw [hR.params_eq]
    rfl
  have hside : R.params.side = T.side := by
    rw [hR.params_eq]
    rfl
  have hrenorm : R.renormalizedDensity T.lam = densitiesLessMultiple (coldInteractionDensity R T.lam)
      (coldExpansionDensity R) (coldFrameDensity R) R.blockDensity
      (levelShareFamily T.coupling T.side (R.depth + 1)) (R.couplingShift T.lam) := by
    unfold StepSetup.renormalizedDensity
    rw [hcoupling, hside]
  refine ⟨?_, ?_⟩
  · rw [hrenorm]
    exact hcold _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H
  have hb : |R.couplingShift T.lam| ≤
      expansionConstant T.Cs (maxOfFirstFour T.N) R.params.rt R.params.n₁ := by
    have hbase : 0 ≤ baseConstant T.Cs R.params.rt := le_trans (abs_nonneg _) H.abs_b_le
    have hprod : 0 ≤ weightGrowthSup R.params.rt R.params.n₁ *
        (2 * T.Cs + baseConstant T.Cs R.params.rt * maxOfFirstFour T.N) :=
      mul_nonneg (weightGrowthSup_nonneg _ _)
        (add_nonneg (by linarith [H.Cs_nonneg]) (mul_nonneg hbase H.Na_nonneg))
    unfold expansionConstant
    linarith [H.abs_b_le]
  have hBpos : 0 < R.params.B := H.admissible.B_pos
  have hB : R.params.B = expansionConstant T.Cs (maxOfFirstFour T.N) R.params.rt R.params.n₁ := by
    rw [hR.params_eq]
    rfl
  have hdiff : R.shiftedCoupling T.lam - R.coupling = -R.couplingShift T.lam := by
    unfold StepSetup.shiftedCoupling
    ring
  rw [hdiff, abs_neg]
  rw [← hB] at hb
  linarith
end YangMills.Construction.ClusterExpansionOfAStep
end
