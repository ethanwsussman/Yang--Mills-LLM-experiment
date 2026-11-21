import YangMills.Construction.EuclideanAnalysis.FunctionsAndDistributions
import Mathlib
open MeasureTheory TopologicalSpace
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanAnalysis
def mulNormSqLog (c : YangMills.Construction.EuclideanAnalysis.RealSpace 4 → ℂ)
    (x : YangMills.Construction.EuclideanAnalysis.RealSpace 4) : ℂ :=
  if x = 0 then 0 else c x * ((‖x‖ ^ 2 * Real.log ‖x‖ : ℝ) : ℂ)
namespace BumpAndDensities
def ExistsRadialBump : Prop :=
  ∃ c : YangMills.Construction.EuclideanAnalysis.CompactSupportClass ⊤
      (⟨Metric.ball 0 1, Metric.isOpen_ball⟩ :
        Opens (YangMills.Construction.EuclideanAnalysis.RealSpace 4)) ℝ,
    YangMills.Construction.EuclideanAnalysis.IsRadial c ∧ (∀ x, 0 ≤ c x ∧ c x ≤ 1) ∧
      ∀ x : YangMills.Construction.EuclideanAnalysis.RealSpace 4, ‖x‖ ≤ 1 / 2 → c x = 1
def ContinuousEqZeroOfIntegralMul : Prop :=
  ∀ g : YangMills.Construction.EuclideanAnalysis.RealSpace 4 → ℂ, Continuous g →
    (∀ ψ : YangMills.Construction.EuclideanAnalysis.SmoothTestFunction, ∫ x, g x * ψ x = 0) →
      ∀ x, g x = 0
def MulNormSqLogContinuous : Prop :=
  ∀ c : YangMills.Construction.EuclideanAnalysis.RealSpace 4 → ℂ, Continuous c →
    Continuous (mulNormSqLog c) ∧ LocallyIntegrable (mulNormSqLog c) volume
def Combined : Prop :=
  ExistsRadialBump ∧ ContinuousEqZeroOfIntegralMul ∧ MulNormSqLogContinuous
end BumpAndDensities
end YangMills.Construction.EuclideanAnalysis
