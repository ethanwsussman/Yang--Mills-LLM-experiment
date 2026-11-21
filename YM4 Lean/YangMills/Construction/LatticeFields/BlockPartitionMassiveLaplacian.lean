import YangMills.Construction.LatticeFields.BlockAveraging
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields
namespace BlockPartitionMassiveLaplacian
def BlocksPartitionSites {d : ℕ} (N : ℕ) (κ : LatticeShape d) : Prop :=
  (∀ y : LatticeSite 1 κ, (coarseBlock N y).ncard = N ^ d) ∧
    (∀ x : LatticeSite N κ, ∃! y : LatticeSite 1 κ, x ∈ coarseBlock N y) ∧
    ∀ (ω : ScalarField 1 κ) (y : LatticeSite 1 κ) (x : LatticeSite N κ), x ∈ coarseBlock N y →
      ScalarField.eval (siteBlockAvgAdj ω : ScalarField N κ) x = ScalarField.eval ω y
def AveragesTrivialAtUnitSpacing {d : ℕ} (κ : LatticeShape d) : Prop :=
  (∀ f : ScalarField 1 κ, siteBlockAvg f = f) ∧
    (∀ A : LatticeOneForm 1 κ, bondBlockAvg A = A) ∧
    ∀ A : LatticeOneForm 1 κ, exitFaceAvg A = A
def TorusMassiveLaplacianIdentities {d : ℕ} (N : ℕ) (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ)
    (a : ℝ) : Prop :=
  (∀ A : LatticeOneForm N (LatticeShape.torus ℓ hℓ),
      tensorLaplacian A = latticeCurlAdjoint (latticeCurl A) + latticeGrad (latticeDiv A)) ∧
    (∀ A : LatticeOneForm N (LatticeShape.torus ℓ hℓ),
      massiveLaplacian a A = massiveLaplacianAlt a A) ∧
    (∀ A B : LatticeOneForm N (LatticeShape.torus ℓ hℓ),
      fieldInner (massiveLaplacian a A) B = fieldInner A (massiveLaplacian a B)) ∧
    ∀ A : LatticeOneForm N (LatticeShape.torus ℓ hℓ),
      fieldInner A (massiveLaplacian a A) =
        fieldNorm (latticeCurl A) ^ 2 + fieldNorm (kerLaplacianProj (latticeDiv A)) ^ 2 +
          a * fieldNorm (bondBlockAvg A) ^ 2
def TorusUnitSpacingIdentities {d : ℕ} (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ) (a : ℝ) : Prop :=
  siteBlockAvgKer 1 ℓ hℓ = {0} ∧
    (∀ f : ScalarField 1 (LatticeShape.torus ℓ hℓ), kerLaplacianProj f = 0) ∧
    (∀ f : ScalarField 1 (LatticeShape.torus ℓ hℓ), kerLaplacianProjCompl f = f) ∧
    (∀ A : LatticeOneForm 1 (LatticeShape.torus ℓ hℓ), bondBlockAvg A = A) ∧
    ∀ A : LatticeOneForm 1 (LatticeShape.torus ℓ hℓ),
      massiveLaplacian a A = massiveLaplacianUnit a A
end BlockPartitionMassiveLaplacian
def BlockPartitionMassiveLaplacian.Claim : Prop :=
  ∀ (d L k : ℕ), 2 ≤ d → 2 ≤ L → ∀ a : ℝ, 0 < a →
    (∀ κ : LatticeShape d, BlockPartitionMassiveLaplacian.BlocksPartitionSites (L ^ k) κ) ∧
    (∀ κ : LatticeShape d, BlockPartitionMassiveLaplacian.AveragesTrivialAtUnitSpacing κ) ∧
    (∀ (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ),
      BlockPartitionMassiveLaplacian.TorusMassiveLaplacianIdentities (L ^ k) ℓ hℓ a) ∧
    ∀ (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ),
      BlockPartitionMassiveLaplacian.TorusUnitSpacingIdentities ℓ hℓ a
end YangMills.Construction.LatticeFields
