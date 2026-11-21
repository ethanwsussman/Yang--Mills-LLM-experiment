import YangMills.Construction.LatticeFields.SobolevOneNorm
import Mathlib
namespace YangMills.Construction.LatticeFields
def SobolevOneNormProducts.Claim : Prop :=
  ∀ (d N r : ℕ) (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ), 0 < N → ∀ (hr : r ≤ 1)
    (F F' : LatticeTensor N (LatticeShape.torus ℓ hℓ) r),
    fieldNorm F' * fieldNorm (tensorGrad F) + fieldNorm (tensorGrad F') * fieldNorm F ≤
        sobolevOneNorm hr F' * sobolevOneNorm hr F ∧
      fieldNorm F' * fieldNorm F ≤ sobolevOneNorm hr F' * sobolevOneNorm hr F ∧
      fieldNorm (tensorGrad F') * fieldNorm (tensorGrad F) ≤
        sobolevOneNorm hr F' * sobolevOneNorm hr F
end YangMills.Construction.LatticeFields
