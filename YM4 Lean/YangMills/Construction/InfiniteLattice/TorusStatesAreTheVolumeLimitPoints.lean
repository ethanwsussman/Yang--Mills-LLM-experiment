import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def TorusLimitsAreInfiniteVolumeLimits : Prop :=
  ∀ (L K : ℕ) (β : ℝ), 2 ≤ L → torusLimitSet L K β = {ν | IsInfiniteVolumeLimit L K β ν}
end YangMills.Construction.InfiniteLattice
end
