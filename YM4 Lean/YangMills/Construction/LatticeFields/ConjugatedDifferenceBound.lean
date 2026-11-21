import YangMills.Construction.LatticeFields.ScaleParameters
import YangMills.Construction.LatticeFields.WeightConjugation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields
def ConjugatedDifferenceBound.Claim : Prop :=
  ∀ (P : ScaleData) (ℓ : Fin P.d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ) (δ : ℝ)
    (θ : LatticeSite P.N (LatticeShape.torus ℓ hℓ) → ℝ),
    δ ≤ 1 / (2 * ((P.d : ℝ) + 1)) → LipschitzWeight δ θ →
    (∀ f : ScalarField P.N (LatticeShape.torus ℓ hℓ),
      fieldNorm (weightConj θ .fine .fine latticeGrad f - latticeGrad f) ≤
        2 * ((P.d : ℝ) + 1) * δ * fieldNorm f) ∧
    (∀ A : LatticeOneForm P.N (LatticeShape.torus ℓ hℓ),
      fieldNorm (weightConj θ .fine .fine latticeDiv A - latticeDiv A) ≤
        2 * ((P.d : ℝ) + 1) * δ * fieldNorm A) ∧
    (∀ (r : ℕ) (F : LatticeTensor P.N (LatticeShape.torus ℓ hℓ) r),
      fieldNorm (weightConj θ .fine .fine (tensorGrad (r := r)) F - tensorGrad F) ≤
        2 * ((P.d : ℝ) + 1) * δ * fieldNorm F) ∧
    ∀ (r : ℕ) (F : LatticeTensor P.N (LatticeShape.torus ℓ hℓ) (r + 1)),
      fieldNorm (weightConj θ .fine .fine (tensorGradAdjoint (r := r)) F - tensorGradAdjoint F) ≤
        2 * ((P.d : ℝ) + 1) * δ * fieldNorm F
end YangMills.Construction.LatticeFields
