import YangMills.Construction.LatticeFields.BlockAveraging
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields
def BlockBumpFunctions.Claim : Prop :=
  ∀ (d L k : ℕ), 2 ≤ d → 2 ≤ L → ∀ (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ)
    (ω : ScalarField 1 (LatticeShape.torus ℓ hℓ)),
    ∃ ψ : ScalarField (L ^ k) (LatticeShape.torus ℓ hℓ),
      (∀ y, ScalarField.eval ω y = 0 → ∀ x ∈ coarseBlock (L ^ k) y, ScalarField.eval ψ x = 0) ∧
      siteBlockAvg ψ = ω ∧
      fieldNorm (tensorLaplacian ψ) ≤ 6 * (d : ℝ) * 30 ^ d * 16 ^ (1 - (d : ℤ)) * fieldNorm ω
end YangMills.Construction.LatticeFields
