import YangMills.Construction.LatticeFields.DirichletBlockOps
import YangMills.Construction.LatticeFields.ScaleParameters
import YangMills.Construction.LatticeFields.SobolevOneNorm
import YangMills.Construction.LatticeFields.WeightConjugation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields
def conjProjConst (d : ℕ) : ℝ := 2256 * (d : ℝ) ^ 5 * blockMomentLowerBound d ^ (-2 : ℤ)
def conjFormConst (d : ℕ) (a : ℝ) : ℝ := conjProjConst d + 6 + 3 * a
end YangMills.Construction.LatticeFields
