import YangMills.Construction.ResponseInTheExpansion.ConnectedFunctionsOfTheExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
def pairCumulantEqFreeKernelStatement : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters) (m : ℕ) (n vt : ℝ) (f h : PeriodicLattice.FourTorus ℓ.side m → ℝ), 0 < n → 0 < vt →
    40 * n ≤ PeriodicLattice.torusSide ℓ.side m →
    WeightedResponses.IsNormalizedPairAt ℓ m n vt f h →
    gaussianCumulantLimit (PeriodicLattice.torusSide ℓ.side m) (q := 1) ![f, h] =
      9 / Real.pi ^ 4 * TestFunctions.inverseEighthKernelTorus f h
end YangMills.Construction.ResponseInTheExpansion
end
