import YangMills.Construction.ResponseInTheExpansion.ConnectedFunctionsOfTheExpansion
import YangMills.Construction.Torus.LiftsShapeConditionAndCollinearQuadruples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
def collinearCumulantBoundsStatement : Prop :=
  ∀ (s : Conventions.StandingParameters) (d ϑ : ℝ), ∀ f ∈ QuadrupleClasses.collinearQuadsTorus s d ϑ,
    27 * Real.pi ^ (-8 : ℤ) * (25 / 4 : ℝ) ^ (-16 : ℤ) * ϑ ^ 4 * ∏ i, TestFunctions.uniformNorm (f i) ≤
      gaussianCumulantLimit (q := 3) (PeriodicLattice.torusSide s.L s.m) f ∧
    gaussianCumulantLimit (q := 3) (PeriodicLattice.torusSide s.L s.m) f ≤
      54 * Real.pi ^ (-8 : ℤ) * TorusMeasure.omega4 ^ 4 * (16 : ℝ) ^ (-16 : ℤ) *
        ∏ i, TestFunctions.uniformNorm (f i)
end YangMills.Construction.ResponseInTheExpansion
end
