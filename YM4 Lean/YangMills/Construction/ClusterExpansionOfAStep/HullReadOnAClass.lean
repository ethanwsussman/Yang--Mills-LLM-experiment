import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusFields TorusLumps StepSettings
def HullRestrictedToComponent : Prop :=
  ∀ (R : StepSetup) (n : ℕ) [NeZero n] (V : TorusField n) (Y X : Finset (TorusSite n))
    (z : TorusSite n),
    R.params.Admissible → 2 ^ 16 ≤ R.nextRange → R.params.side ∣ n →
    IsHullState R.params R.nextRange V Y → X ∈ chainComponents R.nextRange Y → z ∈ X →
    (z ∈ hotNeighbourhoodOn R X V ↔ z ∈ hotCoreSites R V)
end YangMills.Construction.ClusterExpansionOfAStep
end
