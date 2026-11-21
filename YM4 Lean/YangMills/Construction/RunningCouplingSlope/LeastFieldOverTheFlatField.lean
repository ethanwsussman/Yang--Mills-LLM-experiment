import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.RunningCouplingSlope.LogarithmOfTheChain
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def MinimizerOverTrivialFieldIsTrivial : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ (t m : ℕ) (ρ : ℝ), 0 < m → 0 < ρ → ρ ≤ 1 →
      SlopeCoefficient.minimizerOnFinerTorus a ρ L t (2 * L ^ m)
          (TorusFields.trivialField (2 * L ^ m)) =
        TorusFields.trivialField (2 * L ^ m * L)
end YangMills.Construction.RunningCouplingSlope
end
