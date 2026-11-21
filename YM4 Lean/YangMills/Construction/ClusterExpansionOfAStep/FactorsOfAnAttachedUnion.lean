import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.GeometryOfAKeptPart
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepFactors
open BlockAverages TorusFields TorusLumps RenormalizationStepParameters StepSettings StepCosts KeptRegion
def AttachedUnionFactorBound : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n → ∀ (V : TorusField n) (q : CoarseState R n)
      (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
      (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
      (P : Finset (Finset (TorusSite n))),
      IsHullState R.params R.nextRange V q.1 → IsHullState R.params R.range W Yt →
      coarseStateOf R (hotCoreSites R V) W Yt ωt bad b = q →
      attachedSites R.params.side R.range bad Yt (hotCoreSites R V) =
        clusterSites R.params.side bad Yt (hotCoreSites R V) →
      P ⊆ chainComponents R.nextRange q.1 → (∀ X ∈ chainComponents R.nextRange q.1, coarseFactor V q X ≠ 0) →
      ∏ X ∈ P, coarseFactor V q X ≤
        ∏ Xc ∈ (open Classical in (chainComponents R.range Yt).filter
            (· ⊆ attachedInBlocks R.params.side R.range bad Yt (hotCoreSites R V) (P.biUnion id))),
          R.clusterFactor (n * R.params.side) W Yt ωt Xc
end YangMills.Construction.StepFactors
end
