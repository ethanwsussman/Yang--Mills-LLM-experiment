import YangMills.Construction.Lattice.LeastNumbersOfThreeLemmas
import YangMills.Construction.SeparatedSequences.NumbersOfTheExpansionOverThePieces
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedSequences.EndConstants
def exponentBoundReal (L : ℕ) (β₁ ε₁ : ℝ) : ℝ :=
  (YangMills.Construction.LeastConstants.exponentBoundInf L β₁ ε₁).toReal
def l2BoundReal (L : ℕ) : ℝ :=
  (YangMills.Construction.LeastConstants.l2BoundInf L).toReal
def seminormConst (L : ℕ) : ℝ :=
  (YangMills.Construction.LeastConstants.seminormConstantInf L).toReal
def exponentConst (L : ℕ) (β : ℝ) : ℝ :=
  (YangMills.Construction.LeastConstants.exponentConstantInf L β).toReal
def endsBound (L : ℕ) (β ε : ℝ) : ℝ :=
  if 1 ≤ β + ε then
    max (l2BoundReal L) (max (exponentBoundReal L β ε) (exponentBoundReal L β β))
  else
    max (l2BoundReal L)
      (max (exponentBoundReal L β ε) (max (exponentBoundReal L β β) (exponentBoundReal L β (β + ε))))
def endsSmallness (L : ℕ) : ℝ :=
  min (YangMills.Construction.SeparatedSequences.SmallTripleSystem.tripleRadius L)
    (4 * seminormConst L * l2BoundReal L *
      Real.exp (YangMills.Construction.Lattice.siteNearnessRadius L))⁻¹
def localEndConst (L : ℕ) (β ε : ℝ) : ℝ :=
  2 * exponentConst L β * Real.exp (YangMills.Construction.Lattice.siteNearnessRadius L) *
      (1 + seminormConst L * Real.exp (YangMills.Construction.Lattice.siteNearnessRadius L)) *
      endsBound L β ε *
    (1 + 52 * (L : ℝ) ^ 5 * Real.exp (2 * YangMills.Construction.Lattice.siteNearnessRadius L) *
      endsBound L β ε * exponentConst L β)
def localEndL2Const (L : ℕ) : ℝ :=
  4 * seminormConst L * Real.exp (YangMills.Construction.Lattice.siteNearnessRadius L) *
    (1 + seminormConst L * Real.exp (YangMills.Construction.Lattice.siteNearnessRadius L)) *
    l2BoundReal L
def baseLayerConst (L : ℕ) : ℝ :=
  468 * (L : ℝ) * Real.exp 12 * YangMills.Construction.SequenceTriples.baseLayerBound L
def localConst (L : ℕ) (β ε : ℝ) : ℝ :=
  max (localEndConst L β ε) (baseLayerConst L)
def localL2Const (L : ℕ) : ℝ :=
  max (localEndL2Const L) (baseLayerConst L)
def firstLocalConst (L : ℕ) (β ε : ℝ) : ℝ :=
  seminormConst L ^ 2 * YangMills.Construction.SeparatedSequences.piecePartitionConstant L *
    Real.exp (YangMills.Construction.Lattice.siteNearnessRadius L + 4) * localConst L β ε
def secondLocalConst (L : ℕ) (β ε : ℝ) : ℝ :=
  seminormConst L * exponentConst L β *
    YangMills.Construction.SeparatedSequences.piecePartitionConstant L *
    Real.exp (2 * YangMills.Construction.Lattice.siteNearnessRadius L + 4) * localConst L β ε
def fourthLocalConst (L : ℕ) (β ε : ℝ) : ℝ :=
  seminormConst L * exponentConst L β *
    Real.exp (2 * YangMills.Construction.Lattice.siteNearnessRadius L + 4) * localConst L β ε
def ratioConst (L : ℕ) : ℝ :=
  max (YangMills.Construction.SeparatedSequences.expansionRatioConst L)
    (Real.exp (4 * YangMills.Construction.Lattice.siteNearnessRadius L + 4) * seminormConst L ^ 2 *
      YangMills.Construction.SeparatedSequences.piecePartitionConstant L * localL2Const L)
def blockLower (L : ℕ) : ℝ :=
  max (YangMills.Construction.SeparatedSequences.expansionBlockSizeFloor L)
    (2 * (YangMills.Construction.SeparatedSequences.pieceOverlapCount L : ℝ) * ratioConst L)
def termBound (L : ℕ) (β ε : ℝ) : ℝ :=
  26 * (L : ℝ) ^ 5 * Real.exp (YangMills.Construction.Lattice.siteNearnessRadius L) *
      max (4 * YangMills.Construction.SeparatedSequences.PieceChain.expansionInverseConst L)
        (fourthLocalConst L β ε) *
    max 1 (firstLocalConst L β ε / YangMills.Construction.SeparatedSequences.expansionRatioConst L) *
    max 1 (secondLocalConst L β ε / YangMills.Construction.SeparatedSequences.expansionRatioConst L)
def mainBound (L : ℕ) (β ε : ℝ) : ℝ :=
  max (endsBound L β ε)
    (max (localEndConst L β ε)
      (max (baseLayerConst L)
        (2 * (YangMills.Construction.SeparatedSequences.pieceOverlapCount L : ℝ) * termBound L β ε)))
end YangMills.Construction.SeparatedSequences.EndConstants
end
