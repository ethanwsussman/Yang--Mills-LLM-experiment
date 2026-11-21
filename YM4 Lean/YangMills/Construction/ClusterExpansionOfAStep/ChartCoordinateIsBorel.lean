import YangMills.Construction.ClusterExpansionOfAStep.CumulantsOfTheKernelsAtMovedBonds
import YangMills.Construction.ClusterExpansionOfAStep.SharesAndCostsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace StepCosts
open BlockAverages TorusFields TorusLumps
def ChartCoordMeasurable : Prop :=
  ∀ (ℓ : StepParameters) (n : ℕ) [NeZero n] (b : TorusBond (n * ℓ.side)),
    MeasurableQuaternion fun p : TorusField n × TorusField (n * ℓ.side) =>
      ((chartCoord ℓ p.1 p.2 b : imaginaryQuaternions) : ℍ[ℝ])
end StepCosts
end YangMills.Construction
end
