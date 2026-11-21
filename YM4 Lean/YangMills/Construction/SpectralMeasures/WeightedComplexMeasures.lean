import YangMills.Construction.SpectralMeasures.EuclideanComplexMeasures
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.EuclideanBorel
def WeightedMeasureTheorem : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (ν : BorelSubset n → ℂ), IsFiniteCombinationMeasure ν → ∀ (X : BorelSubset n)
    (f g : Space n → ℂ), IsBoundedMeasurableFn f → IsBoundedMeasurableFn g →
    complexIntegral (weightedBy g ν) f = complexIntegral ν (f * g) ∧
    (IsSupportedOn ν X → complexIntegral ν f = complexIntegral ν (f * X.1.indicator 1)) ∧
    (IsSupportedOn ν X → IsSupportedOn (weightedBy g ν) X)
end YangMills.Construction.EuclideanBorel
