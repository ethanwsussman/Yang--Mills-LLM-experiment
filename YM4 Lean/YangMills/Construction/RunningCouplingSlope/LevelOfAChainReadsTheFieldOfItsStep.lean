import YangMills.Construction.RunningCouplingSlope.CoordinatesOfTheStepsOfAChainForm
import Mathlib
set_option autoImplicit false
open scoped Quaternion
noncomputable section
namespace YangMills.Construction
open Conventions BlockAverages ColdStepAtMirrorFrames TorusFields
namespace RunningCouplingSlope
def ChainLevelIsStepMinimizer : Prop :=
  ∀ (a ρ : ℝ) (L : ℕ), IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n →
    ∀ (V : TorusField (2 * L ^ n)) (X : ChainPoint L n k), RepresentsMinimizerChain a ρ V X →
      ∀ (j : ℕ), j < k →
      ∀ e : (frameAtStep L n k j).Site (frameAtStep L n k j).depth × Fin 4,
        levelField X j (edgeOfCoords j e) = SoftAverages.quaternionToMatrix
          ((fieldAboveFrame true a ρ 0 (topFieldAtStep a ρ L n k j V) 0 e.1 e.2 : UnitQuaternion) : ℍ[ℝ])
end RunningCouplingSlope
end YangMills.Construction
end
