import YangMills.Construction.TotalDensitiesGiveASystem.FirstExitPathDefs
import YangMills.Construction.WindowOfTheParameters.FlowOfTheTotalDensities
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
def ExpansionFlowEqTotalFlowAt (p : TorusLumps.StepParameters) (Bs g : ℝ) : Prop :=
  ∀ K : ℕ, SequencePassage.definedPassageWindow (TotalDensityFlow.IsDefinedUpTo p) Bs g
      (TotalDensityFlow.coupling p) K = SequencePassage.passageWindow Bs g (ClusterExpansionOfAStep.flowCoupling p) K ∧
    ∀ β ∈ SequencePassage.passageWindow Bs g (ClusterExpansionOfAStep.flowCoupling p) K, ∀ k ≤ K,
      TotalDensityFlow.coupling p β k = ClusterExpansionOfAStep.flowCoupling p β k
def expansionFlowEqTotalFlow : Prop :=
  HoldsAtAdmissibleParameters fun T y => ∀ Bs : ℝ, 2 * T.B ≤ Bs → ForSmallCoupling fun g =>
    ExpansionFlowEqTotalFlowAt (T.stepParameters y) Bs g
end YangMills.Construction.TotalDensities
end
