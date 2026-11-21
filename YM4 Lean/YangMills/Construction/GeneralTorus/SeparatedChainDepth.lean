import YangMills.Construction.Geometry.ToriGeneralSide
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GeneralTorus.SeparatedChain
variable {D : ScaleData} (B : SeparatedChain D)
def depthIndex (x : D.Space) : ℕ :=
  open Classical in
  if x ∈ B.set 1 then sSup {m | 1 ≤ m ∧ x ∈ B.set m} else 0
end YangMills.Construction.GeneralTorus.SeparatedChain
