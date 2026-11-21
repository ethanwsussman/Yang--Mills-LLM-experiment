import YangMills.Construction.InfiniteLattice.GeneratingFunctionsAndConnectedFunctionsOfAMeasureAndOfATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.TestFunctions YangMills.Construction.PeriodicLattice
namespace YangMills.Construction
namespace FourPointBounds
def dilateToSide (L m M : ℕ) (f : FourTorus L m → ℝ) : FourTorus L M → ℝ := fun y =>
  f (TorusMetric.torusProj (torusSide L m) fun i => torusSide L m / torusSide L M * liftPoint y i)
def CutoffRescalingInvariance : Prop :=
  ∀ (L m K M k p : ℕ) (β : ℝ), 3 ≤ L → M + k = m + K → ∀ f : Fin p → FourTorus L m → ℝ,
    torusUrsellFunction L m K β f = torusUrsellFunction L M k β fun i => dilateToSide L m M (f i)
end FourPointBounds
end YangMills.Construction
end
