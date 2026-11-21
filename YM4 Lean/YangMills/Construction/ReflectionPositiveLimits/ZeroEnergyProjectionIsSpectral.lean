import YangMills.Construction.EnergyMomentum.SemigroupGenerators
import YangMills.Construction.ReflectionPositiveLimits.ReconstructionOfAFunctional
import Mathlib
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.GroundStateSpectral
open ReflectionPositivity ReflectionPositivity.FunctionalReconstruction EnergyMomentum.Generators
def GroundStateProjectionSpectral : Prop :=
  ∀ (σ : Tuple → ℝ) (hσ : ReconstructionData σ),
    IsProjOntoEnergyKernel σ hσ (groundStateProjection σ hσ) ∧
      groundStateProjection σ hσ =
        jointSpectralMeasure σ hσ.reflectionPositive zeroEnergySet
end YangMills.Construction.ReflectionPositivity.GroundStateSpectral
