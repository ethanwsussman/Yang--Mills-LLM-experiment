import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import YangMills.Construction.ResponseInTheExpansion.SupportsAlongTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.StepSettings YangMills.Construction.WeightedResponses
open YangMills.Construction.ClusterExpansionOfAStep YangMills.Construction.TorusLumps YangMills.Construction.BlockAverages
def StateMassPreservedByStep : Prop :=
  HoldsAtEveryStep fun T R _ => R.IsSymmetricWeight → ∀ (h : CoarseLabelFacts R) (x'' : ℝ) (n : ℕ) [NeZero n],
    IsBlockTorusSide R.params n →
    stateLIntegral R (n * R.params.side) (fun _ _ _ => 1) = stateLIntegral (nextStepSetup R h T.lam x'') n fun _ _ _ => 1
end YangMills.Construction.ResponseInTheExpansion
end
