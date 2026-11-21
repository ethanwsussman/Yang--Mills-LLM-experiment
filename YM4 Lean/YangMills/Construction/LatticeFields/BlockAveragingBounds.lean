import YangMills.Construction.LatticeFields.BlockAveraging
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields
def IsFieldOperatorNorm {d N M : ℕ} {κ : LatticeShape d} {I J : Type}
    (T : LatticeField N κ I → LatticeField M κ J) (c : ℝ) : Prop :=
  IsLeast {C : ℝ | 0 ≤ C ∧ ∀ F, fieldNorm (T F) ≤ C * fieldNorm F} c
def siteBlockProj {d N : ℕ} {κ : LatticeShape d} (f : ScalarField N κ) : ScalarField N κ :=
  siteBlockAvgAdj (siteBlockAvg f)
def blockConstantFields {d : ℕ} (N : ℕ) (κ : LatticeShape d) : Set (ScalarField N κ) :=
  {g | ∀ y : LatticeSite 1 κ, ∀ x ∈ coarseBlock N y, ∀ x' ∈ coarseBlock N y,
    ScalarField.eval g x = ScalarField.eval g x'}
def BlockAveragingBounds : Prop :=
  ∀ (d L k : ℕ), 2 ≤ d → 2 ≤ L → ∀ (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ),
    ((∀ ω : ScalarField 1 (LatticeShape.torus ℓ hℓ),
        siteBlockAvg (siteBlockAvgAdj (N := L ^ k) ω) = ω) ∧
      IsFieldOperatorNorm
        (siteBlockAvg :
          ScalarField (L ^ k) (LatticeShape.torus ℓ hℓ) → ScalarField 1 (LatticeShape.torus ℓ hℓ))
        1 ∧
      IsFieldOperatorNorm
        (siteBlockAvgAdj :
          ScalarField 1 (LatticeShape.torus ℓ hℓ) → ScalarField (L ^ k) (LatticeShape.torus ℓ hℓ))
        1 ∧
      (∀ f : ScalarField (L ^ k) (LatticeShape.torus ℓ hℓ),
        IsOrthProj (blockConstantFields (L ^ k) (LatticeShape.torus ℓ hℓ)) f
          (siteBlockProj f)) ∧
      ∃ c : ℝ, c ≤ 1 ∧ IsFieldOperatorNorm
        (bondBlockAvg :
          LatticeOneForm (L ^ k) (LatticeShape.torus ℓ hℓ) → LatticeOneForm 1 (LatticeShape.torus ℓ hℓ))
        c) ∧
    (∀ f : ScalarField (L ^ k) (LatticeShape.torus ℓ hℓ),
      bondBlockAvg (latticeGrad f) = latticeGrad (siteBlockAvg f)) ∧
    (∀ A : LatticeOneForm (L ^ k) (LatticeShape.torus ℓ hℓ),
      siteBlockAvg (latticeDiv A) = latticeDiv (exitFaceAvg A)) ∧
    (∀ f : ScalarField (L ^ k) (LatticeShape.torus ℓ hℓ),
      fieldNorm (f - siteBlockProj f) ^ 2 ≤ (d : ℝ) / 2 * fieldNorm (latticeGrad f) ^ 2) ∧
    (∀ A : LatticeOneForm (L ^ k) (LatticeShape.torus ℓ hℓ),
      fieldNorm (bondBlockAvg A - exitFaceAvg A) ^ 2 ≤
        4 * (d : ℝ) * fieldNorm (tensorGrad A) ^ 2) ∧
    (∀ A : LatticeOneForm (L ^ k) (LatticeShape.torus ℓ hℓ),
      fieldNorm A ^ 2 ≤
        8 * (d : ℝ) * fieldNorm (tensorGrad A) ^ 2 + 2 * fieldNorm (bondBlockAvg A) ^ 2)
end YangMills.Construction.LatticeFields
