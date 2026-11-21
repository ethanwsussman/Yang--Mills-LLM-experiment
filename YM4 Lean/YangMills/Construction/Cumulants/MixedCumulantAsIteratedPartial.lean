import YangMills.Construction.Cumulants.LogMomentGeneratingFunction
import YangMills.Construction.Probability.BoundedRealRandomVariable
import Mathlib
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Cumulants.CumulantAsPartial
def MixedCumulantEqPartialOfLog : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] (n : ℕ)
    (x : Fin n → Ω → ℝ), 1 ≤ n →
    (∀ i, YangMills.Construction.Probability.IsBoundedRealRV (x i)) →
    ComplexVariables.HasPartialOverFinset (logDomain ν x) Finset.univ
        (logMomentGeneratingFunction ν x) ∧
      mixedCumulant ν x =
        ComplexVariables.partialOverFinset Finset.univ (logMomentGeneratingFunction ν x) 0
end YangMills.Construction.Cumulants.CumulantAsPartial
