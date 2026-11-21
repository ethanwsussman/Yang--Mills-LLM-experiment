import YangMills.Construction.ComplexAnalysis.PartialDerivativesAndLogarithm
import YangMills.Construction.Probability.BoundedComplexExpectation
import YangMills.Construction.ReflectionPositivity.IsometriesCentringTuplesAndTheTwoFunctionals
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Cumulants
variable {Ω : Type*} [MeasurableSpace Ω]
def IsBoundedFamilyOnProbabilitySpace {k : ℕ} (μ : Measure Ω) (X : Fin k → Ω → ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ Probability.AllBoundedRealRV X
def mixedPartialLogCumulant {k : ℕ} (μ : Measure Ω) (X : Fin k → Ω → ℝ) (J : Finset (Fin k)) : ℂ :=
  ComplexVariables.partialOverFinset J (fun t => Complex.log (momentGeneratingFunction μ X t)) 0
def complexCov (μ : Measure Ω) (f g : Ω → ℂ) : ℂ :=
  Probability.complexExpectation μ (fun x => f x * g x) -
    Probability.complexExpectation μ f * Probability.complexExpectation μ g
end YangMills.Construction.Cumulants
