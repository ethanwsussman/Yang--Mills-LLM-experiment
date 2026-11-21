import YangMills.Construction.TotalDensitiesGiveASystem.FirstExitPathDefs
import YangMills.Construction.TotalDensitiesGiveASystem.TopStatementDefs
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
def CumulantBoundsExist : Prop :=
  TotalDensities.HoldsAtAdmissibleParameters fun T y => TotalDensities.ForSmallCoupling fun g =>
    ∃ (cV : ℝ) (Cn : ℕ → ℝ → ℝ) (C : SystemsWithFiveBounds.LimitConstants),
    C.Valid ∧ TotalDensitySystem.TorusCumulantBound (T.stepParameters y) (2 * T.B) g cV Cn ∧
      TotalDensitySystem.LocalCumulantBounds (T.stepParameters y) (2 * T.B) g C
end YangMills.Construction.TotalDensities
end
