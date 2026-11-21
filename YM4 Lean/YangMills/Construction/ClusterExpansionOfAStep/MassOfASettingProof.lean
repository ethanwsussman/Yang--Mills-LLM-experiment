import YangMills.Construction.ClusterExpansionOfAStep.CalculusOfASplit
import YangMills.Construction.ClusterExpansionOfAStep.MassOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.SplitOfASettingIsRegular
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours ColdStepAtMirrorFrames StepSettings StepGas TorusFields RenormalizationStepParameters TorusLumps
namespace SettingMass
variable {R : StepSetup} {n : ℕ} [NeZero n] {free : Finset (TorusBond (n * R.params.side))}
  {D : BlockDensitySplit R n free}
theorem aeBounded_potential (hreg : D.IsRegular) :
    AEBounded (volume.restrict (openBallsIn R free)) D.potential := by
  have hPsi : AEBounded (volume.restrict (openBallsIn R free)) D.totalInteraction :=
    AEBounded.sum _ fun Y _ => aeBounded_interaction hreg Y
  have hΦ : AEBounded (volume.restrict (openBallsIn R free)) fun η => ∑ Y : TorusSite n, D.density Y η :=
    AEBounded.sum _ fun Y _ => aeBounded_density hreg Y
  refine ((hPsi.add (AEBounded.const (R.coupling * D.totalCost 0 - ∑ Y : TorusSite n, D.logJacobian Y 0))).sub
    hΦ).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_openBallsIn] with η hη
  exact (potential_eq hreg (openBallsIn_subset_closedBallsIn hη)).symm
theorem integrable_and_integral_pos (hρ : 0 < R.ballRadius) (hp : IsCutoff R.ballRadius R.barrierFn)
    (hreg : D.IsRegular) :
    Integrable (fun η : FreeCoords free => cutoffProd (R := R) η * Real.exp (-D.potential η)) ∧
      0 < ∫ η : FreeCoords free, cutoffProd (R := R) η * Real.exp (-D.potential η) := by
  obtain ⟨hne, hw, -⟩ := cutoffProd_setup (R := R) (free := free) hρ hp
  obtain ⟨hm, K, hK⟩ := aeBounded_potential hreg
  have hexp : AEStronglyMeasurable (fun η : FreeCoords free => Real.exp (-D.potential η))
      (volume.restrict (openBallsIn R free)) := Real.continuous_exp.comp_aestronglyMeasurable hm.neg
  have hon : Integrable (fun η : FreeCoords free => cutoffProd (R := R) η * Real.exp (-D.potential η))
      (volume.restrict (openBallsIn R free)) := by
    have hdom : Integrable (fun η : FreeCoords free => cutoffProd (R := R) η * Real.exp K)
        (volume.restrict (openBallsIn R free)) := hw.mul_const _
    refine hdom.mono' (hw.aestronglyMeasurable.mul hexp) ?_
    filter_upwards [hK] with η h
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (cutoffProd_nonneg η)]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (cutoffProd_nonneg η)
    linarith [(abs_le.mp h).1]
  have hsupp : Function.support (fun η : FreeCoords free => cutoffProd (R := R) η * Real.exp (-D.potential η)) ⊆
      openBallsIn R free := by
    intro η hη
    by_contra h
    exact hη (by simp only [cutoffProd_eq_zero h, zero_mul])
  have hint : Integrable (fun η : FreeCoords free => cutoffProd (R := R) η * Real.exp (-D.potential η)) :=
    (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
  refine ⟨hint, ?_⟩
  have hnn : 0 ≤ fun η : FreeCoords free => cutoffProd (R := R) η * Real.exp (-D.potential η) :=
    fun η => mul_nonneg (cutoffProd_nonneg η) (Real.exp_pos _).le
  rw [integral_pos_iff_support_of_nonneg hnn hint]
  have h2 : 0 < volume (openBallsIn R free) :=
    pos_iff_ne_zero.mpr fun h0 => hne (Measure.restrict_eq_zero.mpr h0)
  refine lt_of_lt_of_le h2 (measure_mono fun η hη => ?_)
  exact (mul_pos (cutoffProd_pos hη) (Real.exp_pos _)).ne'
end SettingMass
theorem settingMassEqIntegral_of (hS : DensitySplitRegular) : SettingMassEqIntegral := by
  obtain ⟨rt, hrt, hS⟩ := hS
  refine ⟨rt, hrt, fun T hT hle => ?_⟩
  obtain ⟨y₁, hy₁⟩ := hS T hT hle
  refine ⟨max y₁ T.floorMin, fun y hy R hR n _ hn s hs => ?_⟩
  have hreg : s.densitySplit.IsRegular := hy₁ y (le_trans (le_max_left _ _) hy) R hR n hn s hs
  have hfit : R.params.Admissible := by
    rw [hR.params_eq]
    exact hT.fits y (le_trans (le_max_right _ _) hy)
  have hρ : 0 < R.ballRadius := by
    unfold StepSetup.ballRadius
    have := hfit.σ_pos
    positivity
  have hρT : R.ballRadius = T.ballRadius := by
    unfold StepSetup.ballRadius
    rw [hR.params_eq]
    rfl
  have hp : IsCutoff R.ballRadius R.barrierFn := by
    rw [hR.barrierFn_eq, hρT]
    exact hT.cut
  obtain ⟨h1, h2⟩ := SettingMass.integrable_and_integral_pos hρ hp hreg
  have h1' : Integrable fun η => s.cutoffProduct η * Real.exp (-s.potential η) := h1
  refine ⟨h1', h2, ?_⟩
  unfold StepGas.settingMass
  rw [ofReal_integral_eq_lintegral_ofReal h1' (Filter.Eventually.of_forall fun η =>
    mul_nonneg (cutoffProd_nonneg η) (Real.exp_pos _).le)]
end YangMills.Construction.ClusterExpansionOfAStep
end
