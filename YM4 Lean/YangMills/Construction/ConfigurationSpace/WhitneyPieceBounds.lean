import YangMills.Construction.ConfigurationSpace.WhitneyPiecesCubesConstants
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
open scoped ENNReal
namespace WhitneyPieceBounds
variable {n : ℕ}
def CubesNested (n : ℕ) : Prop :=
  ∀ (j : ℕ) (z : IntPoint n) (i : Fin n),
    innerCube j z i ⊆ middleCube j z i ∧ middleCube j z i ⊆ outerCube j z i
def closedCoreBox (j : ℕ) (z : IntPoint n) : Set (Config n) :=
  translateSet (pieceCenter j z)
    {x | ∀ ι, coords x ι ∈ Set.Icc (-(3 / 8 * WhitneyScales.whitneySide j)) (3 / 8 * WhitneyScales.whitneySide j)}
def PieceProperties (j : ℕ) (z : IntPoint n) : Prop :=
  ofRealFun (whitneyPiece j z) ∈ testFunctionSet (Config n) ∧
  (∀ x : Config n, 0 ≤ whitneyPiece j z x ∧ whitneyPiece j z x ≤ 1) ∧
  tsupport (whitneyPiece j z) ⊆ closedCoreBox j z ∧
  closedCoreBox j z ⊆ pieceBox j z ∧
  pieceBox j z ⊆ boxProduct (innerCube j z) ∧
  IsCompact (tsupport (whitneyPiece j z)) ∧
  tsupport (whitneyPiece j z) ⊆ TestFunctions.injectiveTuples (Fin 4 → ℝ) n ∧
  ∀ (γ : MultiIdx (CoordIndex n)) (x : Config n),
    ‖configMultiDeriv γ (ofRealFun (whitneyPiece j z)) x‖ ≤
      pieceDerivBound n (MultiIdx.order γ) * 2 ^ (j * MultiIdx.order γ)
def PartitionOfUnityProperties (n : ℕ) : Prop :=
  ∀ x ∈ TestFunctions.injectiveTuples (Fin 4 → ℝ) n,
    setCard {p : ℕ × IntPoint n | whitneyPiece p.1 p.2 x ≠ 0} ≤ 3 * 2 ^ (4 * n) ∧
    ∑' p : pieceIndexSet n, whitneyPiece p.1.1 p.1.2 x = 1
def DerivBoundFormula (n : ℕ) : Prop :=
  ∀ r : ℕ, pieceDerivBound n r =
    2 * BumpFunctions.integralConstBound ^ (4 * n) * (pieceDerivConst * n) ^ r * (r.factorial : ℝ) ^ 2
def CubeBoxProperties (j : ℕ) (z : IntPoint n) : Prop :=
  (∀ i : Fin n, outerCube j z i ⊆
    TestFunctions.closedBallR4 (pieceCenter j z i) (2 * WhitneyScales.whitneySide j)) ∧
  2 * WhitneyScales.whitneySide j ≤ 1 ∧
  (∀ i i' : Fin n, i ≠ i' →
    ENNReal.ofReal (WhitneyScales.whitneyScale j / 2) ≤
      TestFunctions.setDistR4 (outerCube j z i) (outerCube j z i')) ∧
  (1 ≤ j → ∀ x ∈ pieceBox j z,
    minSeparation x ≤ ENNReal.ofReal (separationConst * WhitneyScales.whitneyScale j) ∧
    ∃ y ∈ fatDiagonal n, configNorm (x - y) ≤ diagonalDistConst * WhitneyScales.whitneyScale j) ∧
  ∀ x ∈ pieceBox j z,
    configNorm (x - pieceCenter j z) ≤ Real.sqrt n ∧
    1 + configNorm (pieceCenter j z) ≤ (1 + Real.sqrt n) * (1 + configNorm x) ∧
    1 + configNorm x ≤ (1 + Real.sqrt n) * (1 + configNorm (pieceCenter j z))
def shellCenters (n j t : ℕ) : Set (IntPoint n) :=
  {z | (j, z) ∈ pieceIndexSet n ∧
    (t : ℝ) ≤ configNorm (pieceCenter j z) ∧ configNorm (pieceCenter j z) < t + 1}
def ShellCenterCount (n : ℕ) : Prop :=
  ∀ j t : ℕ,
    (1 ≤ j → (setCard (shellCenters n j t) : ℝ≥0∞) ≤
      ENNReal.ofReal (pieceCountConst n * (1 + (t : ℝ)) ^ (4 * n - 4) *
        WhitneyScales.whitneyScale j ^ (4 - 4 * (n : ℤ)))) ∧
    (j = 0 → (setCard (shellCenters n j t) : ℝ≥0∞) ≤
      ENNReal.ofReal (pieceCountConst n * (1 + (t : ℝ)) ^ (4 * n)))
end WhitneyPieceBounds
def WhitneyPieceBounds : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    WhitneyPieceBounds.CubesNested n ∧
    (∀ (j : ℕ) (z : IntPoint n), WhitneyPieceBounds.PieceProperties j z) ∧
    WhitneyPieceBounds.PartitionOfUnityProperties n ∧
    WhitneyPieceBounds.DerivBoundFormula n ∧
    (∀ p ∈ pieceIndexSet n, WhitneyPieceBounds.CubeBoxProperties p.1 p.2) ∧
    WhitneyPieceBounds.ShellCenterCount n
end YangMills.Construction.ConfigurationSpace
end
