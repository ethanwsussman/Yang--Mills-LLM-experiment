import YangMills.Construction.Cumulants.MixedDerivativeCumulantsAndComplexCovariance
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Cumulants.MomentCumulantFormula
open YangMills.Construction.Probability (subfamilyCumulant complexExpectation)
open YangMills.Construction.SetPartition (Partitions)
def Claim : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : ℕ) (Y : Fin k → Ω → ℝ),
    IsBoundedFamilyOnProbabilitySpace μ Y →
    (∀ J : Finset (Fin k), J.Nonempty →
      mixedPartialLogCumulant μ Y J = subfamilyCumulant μ Y J) ∧
    (∀ I : Finset (Fin k), complexExpectation μ (fun ω => ((∏ i ∈ I, Y i ω : ℝ) : ℂ)) =
      ∑ π : Partitions I, ∏ J ∈ π.parts, mixedPartialLogCumulant μ Y J) ∧
    (∀ i : Fin k, mixedPartialLogCumulant μ Y {i} = complexExpectation μ fun ω => (Y i ω : ℂ)) ∧
    (∀ (J : Finset (Fin k)) (c : Fin k → ℝ), 2 ≤ J.card →
      mixedPartialLogCumulant μ (fun i ω => Y i ω + c i) J = mixedPartialLogCumulant μ Y J) ∧
    ∀ i i' : Fin k, i ≠ i' →
      mixedPartialLogCumulant μ Y {i, i'} =
          complexExpectation μ (fun ω => (Y i ω : ℂ) * (Y i' ω : ℂ)) -
            complexExpectation μ (fun ω => (Y i ω : ℂ)) * complexExpectation μ (fun ω => (Y i' ω : ℂ)) ∧
      mixedPartialLogCumulant μ Y {i, i'} =
        complexCov μ (fun ω => (Y i ω : ℂ)) (fun ω => (Y i' ω : ℂ))
end YangMills.Construction.Cumulants.MomentCumulantFormula
