import YangMills.Construction.Averaging.UnitCovarianceStandingData
import YangMills.Construction.SeparatedSequences.NumbersOfTheSettingOfThePropagators
import YangMills.Construction.SeparatedSequences.PairRadiusOfTheTreeExpansions
import YangMills.Construction.SeparatedSequences.SequenceOfThePiecesAndItsFloors
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedSequences.CellSetting
open Set PeriodicLattice TorusMetric
open scoped ENNReal
variable {L m : ℕ}
structure CellParameters (L : ℕ) where
  top : ℕ
  unitLevel : ℕ
  blockExp : ℕ
  gapExp : ℕ
  α₀ : ℝ
  α₁ : ℝ
  γ₀ : ℝ
  covBlockLower : ℝ
  covRadius : ℝ
  walkRadius : ℕ
namespace CellParameters
variable (P : CellParameters L)
def blockSize : ℝ := (L : ℝ) ^ P.blockExp
def gapSize : ℝ := (L : ℝ) ^ P.gapExp
structure Admissible : Prop where
  unit_cases : P.unitLevel = P.top ∨ P.unitLevel + 1 = P.top
  sq_le_blockSize : (L : ℝ) ^ 2 ≤ P.blockSize
  scaleFloor_le : (propagatorScaleFloor L : ℝ) ≤ P.blockSize
  le_gapSize : (L : ℝ) ≤ P.gapSize
  gapFloor_le : propagatorGapFloor L ≤ P.gapSize * P.blockSize
  α₀_pos : 0 < P.α₀
  α₁_pos : 0 < P.α₁
  γ₀_pos : 0 < P.γ₀
  α₀_le_radius : P.α₀ ≤ PieceChain.treePairRadius L
  α₁_le_radius : P.α₁ ≤ PieceChain.treePairRadius L
  γ₀_le_radius : P.γ₀ ≤ PieceChain.treePairRadius L
  scaleFloor_le_cov : P.unitLevel + 1 = P.top → (propagatorScaleFloor L : ℝ) ≤ P.covBlockLower
  covRadius_pos : P.unitLevel + 1 = P.top → 0 < P.covRadius
  covRadius_le : P.unitLevel + 1 = P.top →
    P.covRadius ≤ PieceChain.treePairRadius L
  cov_le_blockSize : P.unitLevel + 1 = P.top → P.covBlockLower ≤ P.blockSize
  α₀_le_covRadius : P.unitLevel + 1 = P.top → P.α₀ ≤ P.covRadius
  α₁_le_covRadius : P.unitLevel + 1 = P.top → P.α₁ ≤ P.covRadius
  γ₀_le_covRadius : P.unitLevel + 1 = P.top → P.γ₀ ≤ P.covRadius
  one_le_walkRadius : 1 ≤ P.walkRadius
structure IsCellSetting (S : ScaleData) (Ω : ℕ → Set (FourTorus L m)) : Prop where
  admissible : P.Admissible
  covariance : Averaging.UnitCovarianceSetting 4 L S.levels m Matrices.ComplexMatrix2.specialUnitary
    (torusSide L m) (L ^ P.blockExp) (L ^ P.gapExp)
  top_eq : S.top = P.top
  unit_eq : S.unitLevel = P.unitLevel
  exp_eq : S.blockExp = P.blockExp
  partition_index : -(m : ℤ) ≤ S.blockPartitionIndex S.top
  side_bound : 2 * (L : ℝ) * P.blockSize * S.levelMesh L S.top ≤ PieceChain.sideInUnits S L m
  separated : IsSeparatedSequence S P.gapSize Ω
  vanish_above : ∀ n, S.top < n → Ω n = ∅
end CellParameters
variable (S : ScaleData) (Ω : ℕ → Set (FourTorus L m))
end YangMills.Construction.SeparatedSequences.CellSetting
end
