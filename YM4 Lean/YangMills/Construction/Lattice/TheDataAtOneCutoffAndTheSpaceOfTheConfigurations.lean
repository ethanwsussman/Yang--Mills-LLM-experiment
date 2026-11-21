import YangMills.Construction.Conventions.StandingParameters
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Conventions.StandingParameters
variable (s : StandingParameters)
def spacing : ℝ := PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)
end YangMills.Construction.Conventions.StandingParameters
end
