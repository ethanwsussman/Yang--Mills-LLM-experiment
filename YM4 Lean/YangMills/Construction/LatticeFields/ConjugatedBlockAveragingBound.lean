import YangMills.Construction.LatticeFields.BlockAveraging
import YangMills.Construction.LatticeFields.ScaleParameters
import YangMills.Construction.LatticeFields.WeightConjugation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields
def ConjugatedBlockAveragingBound.Claim : Prop :=
  ∀ (P : ScaleData) (ℓ : Fin P.d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ) (δ : ℝ)
    (θ : LatticeSite P.N (LatticeShape.torus ℓ hℓ) → ℝ),
    δ ≤ 1 / (2 * ((P.d : ℝ) + 1)) → LipschitzWeight δ θ →
    (∀ f : ScalarField P.N (LatticeShape.torus ℓ hℓ),
      fieldNorm (weightConj θ .fine .unit siteBlockAvg f - siteBlockAvg f) ≤
        2 * ((P.d : ℝ) + 1) * δ * fieldNorm f) ∧
    (∀ ω : ScalarField 1 (LatticeShape.torus ℓ hℓ),
      fieldNorm (weightConj θ .unit .fine siteBlockAvgAdj ω - siteBlockAvgAdj ω) ≤
        2 * ((P.d : ℝ) + 1) * δ * fieldNorm ω) ∧
    (∀ A : LatticeOneForm P.N (LatticeShape.torus ℓ hℓ),
      fieldNorm (weightConj θ .fine .unit bondBlockAvg A - bondBlockAvg A) ≤
        2 * ((P.d : ℝ) + 1) * δ * fieldNorm A) ∧
    (∀ B : LatticeOneForm 1 (LatticeShape.torus ℓ hℓ),
      fieldNorm (weightConj θ .unit .fine bondBlockAvgAdj B - bondBlockAvgAdj B) ≤
        2 * ((P.d : ℝ) + 1) * δ * fieldNorm B)
end YangMills.Construction.LatticeFields
