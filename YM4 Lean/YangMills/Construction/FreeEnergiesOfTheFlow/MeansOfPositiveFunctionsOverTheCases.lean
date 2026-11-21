import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import YangMills.Construction.ResponseInTheExpansion.ResponseOfAStep
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergies
def caseMeanTowerStatement : Prop :=
  WeightedResponses.HoldsAtAdmissibleParameters fun Tb y => ∀ (T : WeightedResponses.StageTower (Tb.stepParameters y)) (β : ℝ) (s n : ℕ) [NeZero n],
    ResponseInTheExpansion.IsTowerAtParameters Tb y T β s → ColdStepAtMirrorFrames.IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn → T.MarksMeasurable →
    (T.stage s).toStepSetup.IsWellPosed → TorusLumps.IsBlockTorusSide (Tb.stepParameters y) (n * (Tb.stepParameters y).side) → (Tb.stepParameters y).side ∣ n →
    ∀ F : TorusFields.TorusField n → WeightedResponses.CaseFunction (T.stage s).toStepSetup n,
      (∀ V W Yt ωt bad b, 0 ≤ F V W Yt ωt bad b) →
      (Measurable fun u : WeightedResponses.MarkedSample (Tb.stepParameters y) (s + 1) n =>
        F u.2.2.1 (WeightedResponses.topField (Tb.stepParameters y) s (n * (Tb.stepParameters y).side) u.1)
          (WeightedResponses.stageState T s (n * (Tb.stepParameters y).side) u.1).2.1 (WeightedResponses.stageState T s (n * (Tb.stepParameters y).side) u.1).2.2 u.2.2.2 u.2.1) →
      (∀ᵐ u ∂(WeightedResponses.markedSampleLaw T β (s + 1) n),
        WeightedResponses.CaseIntegrable (T.stage s).toStepSetup (StepSettings.hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
          (WeightedResponses.stageState T (s + 1) n u).2 (F u.2.2.1) ∧
        WeightedResponses.CaseIntegrable (T.stage s).toStepSetup (StepSettings.hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
          (WeightedResponses.stageState T (s + 1) n u).2 fun _ _ _ _ _ => 1) →
      AEMeasurable (fun u => WeightedResponses.caseMean (T.stage s).toStepSetup (StepSettings.hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
        (WeightedResponses.stageState T (s + 1) n u).2 (F u.2.2.1)) (WeightedResponses.markedSampleLaw T β (s + 1) n) ∧
      ∫⁻ u, ENNReal.ofReal (F u.2.2.1 (WeightedResponses.topField (Tb.stepParameters y) s (n * (Tb.stepParameters y).side) u.1)
          (WeightedResponses.stageState T s (n * (Tb.stepParameters y).side) u.1).2.1 (WeightedResponses.stageState T s (n * (Tb.stepParameters y).side) u.1).2.2 u.2.2.2 u.2.1)
          ∂(WeightedResponses.markedSampleLaw T β (s + 1) n) =
        ∫⁻ u, ENNReal.ofReal (WeightedResponses.caseMean (T.stage s).toStepSetup (StepSettings.hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
          (WeightedResponses.stageState T (s + 1) n u).2 (F u.2.2.1)) ∂(WeightedResponses.markedSampleLaw T β (s + 1) n)
end YangMills.Construction.FreeEnergies
end
