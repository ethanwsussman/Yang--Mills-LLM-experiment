import YangMills.Construction.LatticeFields.FieldsAndDifferences
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LatticeFields.MetricAdjointCubes
variable {d : ℕ}
structure MetricProps (N : ℕ) (κ : LatticeShape d) : Prop where
  dist_self : ∀ x : LatticeSite N κ, siteDist x x = 0
  eq_of_dist_eq_zero : ∀ x y : LatticeSite N κ, siteDist x y = 0 → x = y
  dist_comm : ∀ x y : LatticeSite N κ, siteDist x y = siteDist y x
  dist_triangle : ∀ x y z : LatticeSite N κ,
    siteDist x z ≤ siteDist x y + siteDist y z
  dist_add_right : ∀ x y z : LatticeSite N κ, siteDist (x + z) (y + z) = siteDist x y
  spacing_le_dist : ∀ x y : LatticeSite N κ, x ≠ y → latticeSpacing N ≤ siteDist x y
structure DiffOperatorProps (N : ℕ) (κ : LatticeShape d) : Prop where
  shiftForward_comm : ∀ (r : ℕ) (μ ν : Fin d) (F : LatticeTensor N κ r), FieldSquareSummable F →
    shiftForward μ (shiftForward ν F) = shiftForward ν (shiftForward μ F)
  shiftForward_shiftBackward_comm : ∀ (r : ℕ) (μ ν : Fin d) (F : LatticeTensor N κ r),
    FieldSquareSummable F →
    shiftForward μ (shiftBackward ν F) = shiftBackward ν (shiftForward μ F)
  shiftBackward_comm : ∀ (r : ℕ) (μ ν : Fin d) (F : LatticeTensor N κ r), FieldSquareSummable F →
    shiftBackward μ (shiftBackward ν F) = shiftBackward ν (shiftBackward μ F)
  shiftForward_norm : ∀ (r : ℕ) (μ : Fin d) (F : LatticeTensor N κ r), FieldSquareSummable F →
    FieldSquareSummable (shiftForward μ F) ∧ fieldNorm (shiftForward μ F) = fieldNorm F
  shiftBackward_norm : ∀ (r : ℕ) (μ : Fin d) (F : LatticeTensor N κ r), FieldSquareSummable F →
    FieldSquareSummable (shiftBackward μ F) ∧ fieldNorm (shiftBackward μ F) = fieldNorm F
  forwardDiff_adjoint : ∀ (r : ℕ) (μ : Fin d),
    IsFieldAdjoint (forwardDiff μ : LatticeTensor N κ r → LatticeTensor N κ r) (backwardDiff μ)
  grad_adjoint : IsFieldAdjoint (latticeGrad : ScalarField N κ → LatticeOneForm N κ) latticeDiv
  tensorGrad_adjoint : ∀ r : ℕ,
    IsFieldAdjoint (tensorGrad : LatticeTensor N κ r → LatticeTensor N κ (r + 1)) tensorGradAdjoint
  laplacian_eq_sum : ∀ (r : ℕ) (F : LatticeTensor N κ r), FieldSquareSummable F → ∀ x i,
    tensorLaplacian F x i = ∑ μ, backwardDiff μ (forwardDiff μ F) x i
structure MulRestrictProps (N : ℕ) (κ : LatticeShape d) : Prop where
  bond_comm : ∀ (θ : LatticeSite N κ → ℝ) (S : Set (LatticeBond N κ)) (A : LatticeOneForm N κ),
    mulBase θ (restrictBonds S A) = restrictBonds S (mulBase θ A)
  plaquette_comm : ∀ (θ : LatticeSite N κ → ℝ) (S : Set (LatticePlaquette N κ))
    (B : LatticeTwoForm N κ),
    mulBase θ (restrictPlaquettes S B) = restrictPlaquettes S (mulBase θ B)
structure DoubledCubeProps (N : ℕ) [NeZero N] (κ : LatticeShape d) : Prop where
  dist_center_le : ∀ (y : LatticeSite 1 κ), ∀ x ∈ doubledCube N y,
    siteDist x (unitSiteHom N κ y) ≤ d
  finite_volume_le : ∀ y : LatticeSite 1 κ, (doubledCube N y).Finite ∧
    ∑ᶠ _x ∈ doubledCube N y, latticeSpacing N ^ d ≤ (2 : ℝ) ^ d
  setDist_ge : ∀ y z : LatticeSite 1 κ,
    siteDist (unitSiteHom N κ y) (unitSiteHom N κ z) - 2 * d ≤
      siteSetDist (doubledCube N y) (doubledCube N z)
  holder_le_sup : ∀ (r : ℕ) (F : LatticeTensor N κ r) (α : ℝ), 0 ≤ α → α < 1 →
    fieldHolderSeminorm α F ≤ ENNReal.ofReal (2 * latticeSpacing N ^ (-α)) * fieldSupNorm F
def BasicLatticeFacts : Prop :=
  ∀ (d L k N : ℕ) [NeZero N], 2 ≤ d → 2 ≤ L → N = L ^ k → ∀ κ : LatticeShape d,
    MetricProps N κ ∧ DiffOperatorProps N κ ∧ MulRestrictProps N κ ∧ DoubledCubeProps N κ
end YangMills.Construction.LatticeFields.MetricAdjointCubes
