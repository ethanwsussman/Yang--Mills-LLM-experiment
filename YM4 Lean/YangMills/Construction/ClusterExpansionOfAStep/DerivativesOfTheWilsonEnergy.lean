import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import YangMills.Construction.ColdChainAtEveryLevel.ChartsChainsAndShares
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace WilsonDerivatives
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
def BoundedDerivativesOfWilsonAction : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n] (W : TorusField n),
    ContDiffThreeAt (wilsonAction Finset.univ) W ∧
    ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 → AreUnitVectors X →
      |mixedDeriv (wilsonAction Finset.univ) W c X| ≤ C
end WilsonDerivatives
end YangMills.Construction
end
