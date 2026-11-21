import YangMills.Construction.FourPointCondition.FourPointFunctionDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Set
namespace YangMills.Construction.FourPointCondition
def cumulantLawsAtBareLevel : Prop :=
  ResponseInTheExpansion.HoldsOnParameterFamilies fun Tb y => ∀ vt : ℝ, 0 < vt → vt ≤ 1 → ∃ C X : ℝ, ∀ β : ℝ, X ≤ β →
    ∀ (K m : ℕ) (d : ℝ),
      Real.exp (Real.log β ^ 3) ≤
        PeriodicLattice.torusSide (Tb.stepParameters y).side m / levelMesh (Tb.stepParameters y).side K 0 →
      1 ≤ d / levelMesh (Tb.stepParameters y).side K 0 →
      d / levelMesh (Tb.stepParameters y).side K 0 ≤ β ^ ((1 : ℝ) / 90) →
      CumulantLawsOnTorus (Tb.stepParameters y) vt C β 1
        (1 / (d / levelMesh (Tb.stepParameters y).side K 0)) β K m d
end YangMills.Construction.FourPointCondition
end
