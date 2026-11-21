import YangMills.Construction.FourPointCondition.FourPointFunctionDefs
import YangMills.Construction.Torus.FreeKernelsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Set
namespace YangMills.Construction.FourPointCondition
def gaussianFourPointCollinear : Prop :=
  ∀ (s : Conventions.StandingParameters) (d ϑ : ℝ), ∀ f ∈ QuadrupleClasses.collinearQuadsTorus s d ϑ,
    ResponseInTheExpansion.gaussianCumulantLimit (q := 3) (PeriodicLattice.torusSide s.L s.m) f =
      gaugeGroupDim * FreeRingKernels.freeBoxKernelTorus f ∧
    27 * Real.pi ^ (-8 : ℤ) * (25 / 4 : ℝ) ^ (-16 : ℤ) * ϑ ^ 4 * ∏ i, TestFunctions.uniformNorm (f i) ≤
      ResponseInTheExpansion.gaussianCumulantLimit (q := 3) (PeriodicLattice.torusSide s.L s.m) f ∧
    ResponseInTheExpansion.gaussianCumulantLimit (q := 3) (PeriodicLattice.torusSide s.L s.m) f ≤
      54 * Real.pi ^ (-8 : ℤ) * TorusMeasure.omega4 ^ 4 * (16 : ℝ) ^ (-16 : ℤ) *
        ∏ i, TestFunctions.uniformNorm (f i)
end YangMills.Construction.FourPointCondition
end
