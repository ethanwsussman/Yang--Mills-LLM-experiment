import YangMills.Construction.Lattice.FormOnTheLieAlgebraAndTransposes
import YangMills.Construction.SeparatedSequences.CellAndWalkCounts
import YangMills.Construction.SeparatedSequences.RatioOfTheEnds
import YangMills.Construction.SeparatedSequences.SourceDatumNumberOfTheExpansion
import YangMills.Construction.SeparatedSequences.TreeExpansionWalkCount
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SeparatedSequences
def treeExpansionTreeWalkCount (L : ℕ) : ℕ :=
  treeWalkCount L (treeExpansionWalkCount L).toPNat'
def pauliCoordinate (a : Fin 3) (Z : ↥Matrices.ComplexMatrix2.traceless) : ℂ :=
  PeriodicLattice.halfTracePairing (Matrices.ComplexMatrix2.pauli a) (Z : Matrices.ComplexMatrix2)
def bilinearUnitBallSup
    (β : ↥Matrices.ComplexMatrix2.traceless →ₗ[ℂ] ↥Matrices.ComplexMatrix2.traceless →ₗ[ℂ]
      ↥Matrices.ComplexMatrix2.traceless) : ℝ≥0∞ :=
  ⨆ (X : ↥Matrices.ComplexMatrix2.traceless) (X' : ↥Matrices.ComplexMatrix2.traceless)
    (_ : Matrices.ComplexMatrix2.operatorNorm (X : Matrices.ComplexMatrix2) ≤ 1)
    (_ : Matrices.ComplexMatrix2.operatorNorm (X' : Matrices.ComplexMatrix2) ≤ 1),
    ENNReal.ofReal (Matrices.ComplexMatrix2.operatorNorm (β X X' : Matrices.ComplexMatrix2))
def IsLieAlgebraConstant (n : ℝ) : Prop :=
  (∀ (a : Fin 3) (Z : ↥Matrices.ComplexMatrix2.traceless),
      ‖pauliCoordinate a Z‖ ≤ n * Matrices.ComplexMatrix2.operatorNorm (Z : Matrices.ComplexMatrix2)) ∧
    ∀ β : ↥Matrices.ComplexMatrix2.traceless →ₗ[ℂ] ↥Matrices.ComplexMatrix2.traceless →ₗ[ℂ]
        ↥Matrices.ComplexMatrix2.traceless,
      bilinearUnitBallSup β ≤ ENNReal.ofReal (n * ∑ a : Fin 3, ∑ a' : Fin 3, ∑ a'' : Fin 3,
        ‖pauliCoordinate a'' (β (Matrices.ComplexMatrix2.pauliTraceless a')
          (Matrices.ComplexMatrix2.pauliTraceless a))‖)
def lieAlgebraConstant : ℝ := sInf {n : ℝ | 1 ≤ n ∧ IsLieAlgebraConstant n}
def treeOperatorConst (L : ℕ) : ℝ :=
  1728 * lieAlgebraConstant ^ 2 * (L : ℝ) ^ 3 * PeriodicLattice.complexBackgroundKernelConstant L
def treeOperatorConstSecond (L : ℕ) : ℝ :=
  3456 * lieAlgebraConstant ^ 2 * (L : ℝ) ^ 2 * PeriodicLattice.complexBackgroundKernelConstant L
def treeTermConst (L : ℕ) : ℝ :=
  8 * PieceChain.expansionInverseConst L * treeOperatorConst L *
    Real.exp (Lattice.siteNearnessRadius L) * PieceChain.sourceDatumConst L
def treeTermConstSecond (L : ℕ) : ℝ :=
  EndConstants.mainBound L (1 / 4) (1 / 4) * treeOperatorConstSecond L *
    Real.exp (Lattice.siteNearnessRadius L) * PieceChain.sourceDatumConst L
def treeWalkConst (L : ℕ) : ℝ :=
  max (81 * EndConstants.ratioConst L)
    (162 * (pieceOverlapCount L : ℝ) * Real.exp (Lattice.siteNearnessRadius L) *
      max 1 (max (treeTermConst L) (treeTermConstSecond L)))
def treeRatio (L : ℕ) (𝔐 : ℝ) : ℝ :=
  expSiteSeries L (1 / 2 * blockOperatorRate L) * EndConstants.endRatio L 𝔐
structure IsTreeBlockScale (L : ℕ) (𝔐 : ℝ) : Prop where
  overlap_mul_ratio_le : (pieceOverlapCount L : ℝ) * treeRatio L 𝔐 ≤ 1 / 2
  operator_mul_ratio_le :
    4 * max (treeOperatorConst L * expansionBound L)
        (treeOperatorConstSecond L * EndConstants.mainBound L (1 / 4) (1 / 4)) *
      PieceChain.sourceDatumConst L * (pieceOverlapCount L : ℝ) *
      Real.exp (Lattice.siteNearnessRadius L) * treeRatio L 𝔐 ≤ 1
  ratio_le_zpow : treeRatio L 𝔐 ≤ 𝔐 ^ (-9 : ℤ)
  walk_mul_const_le : 2 * (treeExpansionTreeWalkCount L : ℝ) * treeWalkConst L ≤ 𝔐 ^ 3
  overlap_le_pow : 162 * (pieceOverlapCount L : ℝ) ≤ 𝔐 ^ 8
  log_le_rate : 64 * (4 * Real.log L + Real.log 2) ≤ blockOperatorRate L * (L : ℝ) * 𝔐
def treeBlockLower (L : ℕ) : ℝ :=
  sInf {M : ℝ | EndConstants.blockLower L ≤ M ∧
    ∀ 𝔐 : ℝ, M ≤ 𝔐 → IsTreeBlockScale L 𝔐}
end YangMills.Construction.SeparatedSequences
end
