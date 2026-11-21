import YangMills.Construction.Towers.TheLeftChart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace FullSpace
def expForm {L k j : ℕ} (B : Edge L k j → Matrices.ComplexMatrix2) :
    Edge L k j → Matrices.ComplexMatrix2 :=
  expTwist B 1
end FullSpace
end Tower
end YangMills.Construction
end
