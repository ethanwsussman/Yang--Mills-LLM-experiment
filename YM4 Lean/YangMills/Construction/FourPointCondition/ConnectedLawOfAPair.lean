import YangMills.Construction.ResponseInTheExpansion.ConnectedFunctionsOfTheExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Set
namespace YangMills.Construction.FourPointCondition
def gaussianTwoPointPair : Prop :=
  ∀ (L m : ℕ) (d ϑ : ℝ), 0 < L → 0 < d → 40 * d ≤ PeriodicLattice.torusSide L m →
    ∀ f h : PeriodicLattice.FourTorus L m → ℝ,
    (f, h) ∈ TestFunctions.separatedPairsFourTorus L m d ϑ →
    ResponseInTheExpansion.gaussianCumulantLimit (q := 1) (PeriodicLattice.torusSide L m) ![f, h] =
      9 / Real.pi ^ 4 * TestFunctions.inverseEighthKernelTorus (ℓ := PeriodicLattice.torusSide L m) f h
end YangMills.Construction.FourPointCondition
end
