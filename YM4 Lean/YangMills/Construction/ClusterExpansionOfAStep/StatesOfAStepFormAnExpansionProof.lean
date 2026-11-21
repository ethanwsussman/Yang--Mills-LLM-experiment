import YangMills.Construction.ClusterExpansionOfAStep.FactorOfAClassIsOneRule
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateKeepsTheGauge
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateKeepsTranslations
import YangMills.Construction.ClusterExpansionOfAStep.StatesOfAStepAddUp
import YangMills.Construction.ClusterExpansionOfAStep.StatesOfAStepFormAnExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open YangMills.Construction.BlockAverages YangMills.Construction.StepSettings YangMills.Construction.TorusLumps
theorem coarseStates_formHullExpansion (hSum : StepSettings.coarseStatesSumStatement)
    (hGauge : CoarseWeightExpansionGaugeInvariant) (hTrans : CoarseWeightExpansionTranslationInvariant)
    (hLocal : CoarseFactorIsLocalStatement) : CoarseStatesFormHullExpansion := by
  classical
  intro R hR hF h
  obtain ⟨h1, h2, h3⟩ := hLocal R hR
  refine
    { nonneg := fun n _ hs W Y ω hY => ?_
      sum := fun n _ hs W => ?_
      gauge := fun n _ hs W Y ω g hY => hGauge R hR hF n hs W Y ω g hY
      translation := fun n _ hs W Y ω u hu hY => hTrans R hR hF n hs W Y ω u hu hY
      factor_nonneg := fun n _ hs W Y ω X => ?_
      one_rule := fun n n' _ _ hs hs' W W' Y Y' ω ω' X X' y y' m a1 a2 a3 a4 a5 a6 a7 a8 =>
        h3 n n' hs hs' W W' Y Y' ω ω' X X' y y' m a1 a2 a3 a4 a5 a6 a7 a8
      reads_class := fun n _ hs W W' Y Y' ω ω' X a1 a2 a3 a4 => h2 n hs W W' Y Y' X ω ω' a1 a2 a3 a4 }
  · unfold coarseWeightExpansion
    rw [dif_neg (NeZero.ne n)]
    exact ENNReal.toReal_nonneg
  · rw [← hSum R hR n hs W]
    refine Finset.sum_congr rfl fun Y _ => MeasureTheory.lintegral_congr fun ω => ?_
    show ENNReal.ofReal (coarseWeightExpansion R n W Y ω) = _
    unfold coarseWeightExpansion
    rw [dif_neg (NeZero.ne n)]
  · exact h1 n hs W Y X ω
end YangMills.Construction.ClusterExpansionOfAStep
end
