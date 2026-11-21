import YangMills.Construction.ColdStepAtMirrorFrames.RimMeanIsAWeightedMean
import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionOfAMeanInTheTop
import YangMills.Construction.SummableBoundsOfTheFlow.LogarithmAlongAMovingCut
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.Estimates
variable {F : BlockFrame}
def cutoffSlopeAlong (p : ℝ → ℝ) (e : F.GaugeField F.top → StepVariable (finiteCells F))
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) : ℝ :=
  cutoffSlope p (e V) η
def CutoffSlopeMeanExpansion : Prop :=
  ∀ (F : BlockFrame) (ρ : ℝ) (p : ℝ → ℝ) (V : F.GaugeField F.top)
    (A : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (e : F.GaugeField F.top → StepVariable (finiteCells F)), 0 < ρ → IsCutoff ρ p →
    JointlyContDiffOnBalls ρ V A →
    (∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => e (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0) →
    ContDiffThreeAlongBonds (gibbsMeanAt (cutoffLaw F ρ p) A (cutoffSlopeAlong p e)) V ∧
      GibbsMeanExpansions (cutoffLaw F ρ p) V A (cutoffSlopeAlong p e)
end YangMills.Construction.Estimates
end
