import YangMills.Construction.RunningCouplingSlope.CoordinatesOfTheStepsOfAChainForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Conventions BlockAverages ColdStepAtMirrorFrames TorusFields
namespace RunningCouplingSlope
def ChainLogRadiiAreStepLogRadii : Prop :=
  ∀ (a ρ : ℝ) (L : ℕ), IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n →
    ∀ (V : TorusField (2 * L ^ n)) (X : ChainPoint L n k), RepresentsMinimizerChain a ρ V X →
      logRadiusSum X = ∑ j : Fin k,
        ∑ c ∈ innerBonds (finiteCells (frameAtStep L n k j)) (frameAtStep L n k j).top,
          Real.log ‖contourAverage (fieldAboveFrame true a ρ 0 (topFieldAtStep a ρ L n k j V) 0) c‖
end RunningCouplingSlope
end YangMills.Construction
end
