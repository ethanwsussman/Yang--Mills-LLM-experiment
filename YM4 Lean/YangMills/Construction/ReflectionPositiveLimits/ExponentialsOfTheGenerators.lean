import YangMills.Construction.ReflectionPositiveLimits.ReconstructionOfAFunctional
import Mathlib
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.GeneratorExponentials
open ReflectionPositivity ReflectionPositivity.FunctionalReconstruction EnergyMomentum
def GeneratorExponentialsHold : Prop :=
  ∀ (σ : Tuple → ℝ) (hσ : ReconstructionData σ),
    (∀ t : ℝ≥0, heatOperator σ hσ t =
      transferSemigroup σ hσ.reflectionPositive t) ∧
    (∀ y : Momentum3, translationOperator σ hσ y =
      spatialTranslationRep σ hσ.reflectionPositive y) ∧
    (∀ (k : Fin 3) (s : ℝ), coordTranslationOperator σ hσ k s =
      spatialTranslationRep σ hσ.reflectionPositive (s • EuclideanSpace.single k (1 : ℝ)))
end YangMills.Construction.ReflectionPositivity.GeneratorExponentials
