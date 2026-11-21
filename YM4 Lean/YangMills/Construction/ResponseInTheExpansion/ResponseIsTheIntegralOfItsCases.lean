import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ResponseInTheExpansion.ResponseIntegral
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open YangMills.Construction.StepSettings YangMills.Construction.StepGas YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.ClusterExpansionOfAStep YangMills.Construction.BlockAverages
namespace YangMills.Construction.WeightedResponses
def responseEqCaseIntegralStatement : Prop :=
  ∀ (R : StepSetup) (A : ResponseSetup R) (hL : CoarseLabelFacts R), R.IsWellPosed → A.IsAdmissible →
    (∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n → ∀ (y : TorusSite n) (V : TorusField n)
      (Y : Finset (TorusSite n)), IsHullState R.params (clusterRange R.nextCoupling) V Y →
      Integrable (fun ω : Y → (coarseLabelSpace R hL).Ω =>
          A.hullStep n y V Y ω (constOneWeight _) * coarseWeightExpansion R n V Y ω)
        (Measure.pi fun _ : Y => (coarseLabelSpace R hL).μ)) ∧
    (∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n → ∀ (y : TorusSite n) (V : TorusField n),
      responseMass R.params (R.depth + 1) R.nextCoupling (coarseLabelSpace R hL) (coarseWeightExpansion R) A.hullStep n y V =
        blockResponseIntegral A V y) ∧
    ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ (y : TorusSite n) (V : TorusField n),
      caseIntegral R ∅ V (emptyCoarseState R) (caseResponse A V y (constOneWeight _)) = blockResponseIntegral A V y
end YangMills.Construction.WeightedResponses
end
