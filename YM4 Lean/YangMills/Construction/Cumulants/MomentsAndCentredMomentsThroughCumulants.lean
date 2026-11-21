import YangMills.Construction.Cumulants.LogMomentGeneratingFunction
import YangMills.Construction.ReflectionPositivity.IsometriesCentringTuplesAndTheTwoFunctionals
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Cumulants
open Probability (IsBoundedRealRV)
open SetPartition (PartitionsFin singletonFree)
def MomentsViaCumulants : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ)
    (X : Fin n → Ω → ℝ), (∀ i, IsBoundedRealRV (X i)) →
    ((∫ ω, ∏ i, X i ω ∂μ : ℝ) : ℂ) =
        ∑ π : PartitionsFin n, ∏ B ∈ π.parts, finsetCumulant μ X B ∧
      ((∫ ω, ∏ i, (X i ω - ∫ ω', X i ω' ∂μ) ∂μ : ℝ) : ℂ) =
        ∑ π ∈ singletonFree n, ∏ B ∈ π.parts, finsetCumulant μ X B
end YangMills.Construction.Cumulants
