import YangMills.Construction.LatticeFields.BlockAveraging
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields.MassiveLaplacianForms
def Claim : Prop :=
  ∀ (d L k : ℕ), 2 ≤ d → 2 ≤ L → ∀ (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ),
    (∀ A : LatticeOneForm (L ^ k) (LatticeShape.torus ℓ hℓ),
      latticeCurlAdjoint (latticeCurl A) + latticeGrad (latticeDiv A) = tensorLaplacian A) ∧
    ∀ a : ℝ, 0 < a →
      (∀ A : LatticeOneForm (L ^ k) (LatticeShape.torus ℓ hℓ),
        massiveLaplacian a A = massiveLaplacianAlt a A) ∧
      (∀ A A' : LatticeOneForm (L ^ k) (LatticeShape.torus ℓ hℓ),
        fieldInner A' (massiveLaplacian a A) = fieldInner (massiveLaplacian a A') A) ∧
      (∀ A : LatticeOneForm (L ^ k) (LatticeShape.torus ℓ hℓ),
        fieldInner A (massiveLaplacian a A) =
          fieldNorm (latticeCurl A) ^ 2 + fieldNorm (kerLaplacianProj (latticeDiv A)) ^ 2 +
            a * fieldNorm (bondBlockAvg A) ^ 2)
end YangMills.Construction.LatticeFields.MassiveLaplacianForms
