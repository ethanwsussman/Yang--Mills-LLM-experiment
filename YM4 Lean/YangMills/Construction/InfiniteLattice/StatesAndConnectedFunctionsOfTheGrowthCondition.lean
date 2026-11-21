import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice.GrowthCondition
def torusWeakLimits (L K : ℕ) (β : ℝ) :
    Set (Measure (GaugeField (PeriodicLattice.meshSize L (K : ℤ)))) :=
  {μ | IsInfiniteVolumeLimit L K β μ}
end YangMills.Construction.InfiniteLattice.GrowthCondition
end
