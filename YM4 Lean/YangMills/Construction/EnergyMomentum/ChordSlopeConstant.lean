import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace EnergyMomentum
def chordSlopeConstant : ℝ :=
  2 / Real.pi * Real.log (1 + Real.sqrt 2)
end EnergyMomentum
end YangMills.Construction
