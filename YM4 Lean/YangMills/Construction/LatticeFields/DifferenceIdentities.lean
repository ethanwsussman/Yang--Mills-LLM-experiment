import YangMills.Construction.LatticeFields.ScaleParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields.DifferenceIdentities
structure Relations (P : ScaleData) (κ : LatticeShape P.d) : Prop where
  norm_tensorGrad_sq : ∀ A : LatticeOneForm P.N κ, FieldSquareSummable A →
    fieldNorm (tensorGrad A) ^ 2 = fieldNorm (latticeCurl A) ^ 2 + fieldNorm (latticeDiv A) ^ 2
  latticeCurl_latticeGrad : ∀ f : ScalarField P.N κ, FieldSquareSummable f →
    latticeCurl (latticeGrad f) = 0
  norm_tensorGrad_tensorGrad : ∀ (r : ℕ) (F : LatticeTensor P.N κ r), FieldSquareSummable F →
    fieldNorm (tensorGrad (tensorGrad F)) = fieldNorm (tensorLaplacian F)
  norm_tensorGrad_le : ∀ (r : ℕ) (F : LatticeTensor P.N κ r), FieldSquareSummable F →
    fieldNorm (tensorGrad F) ≤ 2 * Real.sqrt P.d * P.η⁻¹ * fieldNorm F
  norm_tensorGradAdjoint_le : ∀ (r : ℕ) (F : LatticeTensor P.N κ (r + 1)),
    FieldSquareSummable F →
    fieldNorm (tensorGradAdjoint F) ≤ 2 * Real.sqrt P.d * P.η⁻¹ * fieldNorm F
def Claim : Prop :=
  ∀ (P : ScaleData) (κ : LatticeShape P.d), Relations P κ
end YangMills.Construction.LatticeFields.DifferenceIdentities
