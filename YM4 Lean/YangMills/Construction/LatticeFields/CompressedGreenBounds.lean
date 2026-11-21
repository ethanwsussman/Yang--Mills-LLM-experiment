import YangMills.Construction.LatticeFields.BondCompressionBounds
import YangMills.Construction.LatticeFields.MassiveLaplacianCoercive
import YangMills.Construction.LatticeFields.WeightConjugateBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields
def greenDecayConst (d : ℕ) (a : ℝ) : ℝ :=
  coerciveConst d a / (4 * ((d : ℝ) + 1) * conjFormConst d a)
end YangMills.Construction.LatticeFields
