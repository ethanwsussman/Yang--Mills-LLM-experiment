import YangMills.Construction.RunningCouplingSlope.TangentOfTheLastNoise
import YangMills.Construction.RunningCouplingSlope.TorusViewedOnATower
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def MinimalActionDerivAlongTopForm : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m n : ℕ, 0 < n →
    ∀ᶠ V in 𝓝 (TorusFields.trivialField (2 * L ^ n)),
      ∀ W : Edge L n (m + 1) (m + 1) → Matrices.ComplexMatrix2, RepresentsTorusField W V →
      ∀ X : ChainPoint L n (m + 1), IsMinimizerOver a W X → ∀ B : edgeFormSpace L n (m + 1) (m + 1),
        HasDerivAt (fun t : ℝ => minimalChainAction a
            (PeriodicLattice.expTwist (t • (B : Edge L n (m + 1) (m + 1) → Matrices.ComplexMatrix2)) W))
          (leftDeriv (chainAction a) X (lastNoiseTangent B)) 0
end YangMills.Construction.RunningCouplingSlope
end
