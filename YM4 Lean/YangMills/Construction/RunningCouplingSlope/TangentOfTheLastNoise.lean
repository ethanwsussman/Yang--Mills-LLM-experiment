import YangMills.Construction.RunningCouplingSlope.SoftChainOnATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
variable {L n m : ℕ}
def lastNoiseTangent (B : Tower.edgeFormSpace L n (m + 1) (m + 1)) : LevelForms L n (m + 1) :=
  (0, Pi.single (Fin.last m) B)
end YangMills.Construction.RunningCouplingSlope
end
