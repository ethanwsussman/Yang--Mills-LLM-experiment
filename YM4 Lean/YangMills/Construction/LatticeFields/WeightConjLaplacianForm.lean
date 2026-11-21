import YangMills.Construction.LatticeFields.DirichletBlockOps
import YangMills.Construction.LatticeFields.ScaleParameters
import YangMills.Construction.LatticeFields.SobolevOneNorm
import YangMills.Construction.LatticeFields.WeightConjugation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields
def WeightConjMassiveLaplacianFormBound : Prop :=
  ∀ (P : ScaleData) (ℓ : Fin P.d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ) (δ : ℝ)
    (θ : LatticeSite P.N (LatticeShape.torus ℓ hℓ) → ℝ),
    δ ≤ 1 / (2 * ((P.d : ℝ) + 1)) → LipschitzWeight δ θ →
    2256 * (P.d : ℝ) ^ 5 * blockMomentLowerBound P.d ^ (-2 : ℤ) *
      (2 * ((P.d : ℝ) + 1) * δ) ≤ 1 →
    ∀ A A' : LatticeOneForm P.N (LatticeShape.torus ℓ hℓ),
      |fieldInner A' (weightConj θ .fine .fine (massiveLaplacian P.a) A -
          massiveLaplacian P.a A)| ≤
        (2256 * (P.d : ℝ) ^ 5 * blockMomentLowerBound P.d ^ (-2 : ℤ) + 6 + 3 * P.a) *
            (2 * ((P.d : ℝ) + 1) * δ) *
          sobolevOneNorm le_rfl A' * sobolevOneNorm le_rfl A
end YangMills.Construction.LatticeFields
