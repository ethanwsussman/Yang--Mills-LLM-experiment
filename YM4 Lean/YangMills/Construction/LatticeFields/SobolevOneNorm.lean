import YangMills.Construction.LatticeFields.FieldsAndDifferences
import Mathlib
noncomputable section
namespace YangMills.Construction.LatticeFields
variable {d N r : ℕ} {ℓ : Fin d → ℕ} {hℓ : ∀ μ, 1 ≤ ℓ μ}
def sobolevOneNorm (_hrank : r ≤ 1) (F : LatticeTensor N (LatticeShape.torus ℓ hℓ) r) : ℝ :=
  Real.sqrt (fieldNorm (tensorGrad F) ^ 2 + fieldNorm F ^ 2)
theorem sobolevOneNorm_sq (hrank : r ≤ 1) (F : LatticeTensor N (LatticeShape.torus ℓ hℓ) r) :
    sobolevOneNorm hrank F ^ 2 = fieldNorm (tensorGrad F) ^ 2 + fieldNorm F ^ 2 :=
  Real.sq_sqrt (by positivity)
end YangMills.Construction.LatticeFields
