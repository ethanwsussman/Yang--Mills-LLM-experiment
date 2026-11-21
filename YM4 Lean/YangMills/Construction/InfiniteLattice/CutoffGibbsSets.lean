import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def cutoffExtremalSet (L K : ℕ) (β : ℝ) :
    Set (Measure (GaugeField (PeriodicLattice.meshSize L (K : ℤ)))) :=
  {ν | IsExtremalPeriodicGibbs β ν}
end YangMills.Construction.InfiniteLattice
