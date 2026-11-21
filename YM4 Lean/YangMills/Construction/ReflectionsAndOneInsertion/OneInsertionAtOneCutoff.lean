import YangMills.Construction.ReflectionsAndOneInsertion.PeriodicGibbsLimitStandingDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
namespace ReflectionsAndOneInsertion
def complexSmeared (D : InsertionData) (h : AmbientSpace → ℝ) : D.GaugeField → ℂ :=
  fun U => ((InfiniteLattice.smearedEnergy h U : ℝ) : ℂ)
end ReflectionsAndOneInsertion
end YangMills.Construction
end
