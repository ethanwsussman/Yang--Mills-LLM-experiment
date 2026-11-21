import YangMills.Construction.Continuum.PiecesOfTheShellsTheirCubesAndNumbers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ShellPieceBounds
open scoped ENNReal
variable {n : ℕ}
def BoxesNested (n : ℕ) : Prop :=
  ∀ (j : ℕ) (z : ShellPieces.LatticePt n) (i : Fin n),
    ShellPieces.innerBox j z i ⊆ ShellPieces.middleBox j z i ∧
      ShellPieces.middleBox j z i ⊆ ShellPieces.outerBox j z i
def pieceC (j : ℕ) (z : ShellPieces.LatticePt n) : ConfigSpace.Config n → ℂ :=
  fun x => (ShellPieces.piece j z x : ℂ)
def closedCoreBox (j : ℕ) (z : ShellPieces.LatticePt n) : Set (ConfigSpace.Config n) :=
  ShellPieces.shiftSet (ShellPieces.pieceCentre j z)
    {x | ∀ i c, x i c ∈ Set.Icc (-(3 / 8 * PieceScales.pieceSide j)) (3 / 8 * PieceScales.pieceSide j)}
def PieceProperties (j : ℕ) (z : ShellPieces.LatticePt n) : Prop :=
  pieceC j z ∈ SmoothMaps.smoothCompactSet (ConfigSpace.Config n) ∧
  (∀ x : ConfigSpace.Config n, 0 ≤ ShellPieces.piece j z x ∧ ShellPieces.piece j z x ≤ 1) ∧
  tsupport (ShellPieces.piece j z) ⊆ closedCoreBox j z ∧
  closedCoreBox j z ⊆ ShellPieces.openBox j z ∧
  ShellPieces.openBox j z ⊆ ConfigSpace.cylinderSet (ShellPieces.innerBox j z) ∧
  IsCompact (tsupport (ShellPieces.piece j z)) ∧
  tsupport (ShellPieces.piece j z) ⊆ TestFunctions.injectiveTuples (Fin 4 → ℝ) n ∧
  ∀ (γ : ConfigSpace.MultiIndex n) (x : ConfigSpace.Config n),
    ‖ConfigSpace.iteratedPartial γ (pieceC j z) x‖ ≤
      ShellPieces.derivBound n γ.order * 2 ^ (j * γ.order)
def SumsToOne (n : ℕ) : Prop :=
  ∀ x ∈ TestFunctions.injectiveTuples (Fin 4 → ℝ) n,
    ShellPieces.cardOf {p : ℕ × ShellPieces.LatticePt n | ShellPieces.piece p.1 p.2 x ≠ 0} ≤
        3 * 2 ^ (4 * n) ∧
    ∑' p : ShellPieces.activeIndices n, ShellPieces.piece p.1.1 p.1.2 x = 1
def DerivBoundFormula (n : ℕ) : Prop :=
  ∀ r : ℕ, ShellPieces.derivBound n r =
    2 * Bumps.normalizerBound ^ (4 * n) * (ShellPieces.derivConst * n) ^ r *
      (r.factorial : ℝ) ^ 2
def BoxGeometry (j : ℕ) (z : ShellPieces.LatticePt n) : Prop :=
  (∀ i : Fin n, ShellPieces.outerBox j z i ⊆
    TestFunctions.closedBallR4 (ShellPieces.pieceCentre j z i) (2 * PieceScales.pieceSide j)) ∧
  2 * PieceScales.pieceSide j ≤ 1 ∧
  (∀ i i' : Fin n, i ≠ i' →
    ENNReal.ofReal (PieceScales.dyadicScale j / 2) ≤
      TestFunctions.setDistR4 (ShellPieces.outerBox j z i) (ShellPieces.outerBox j z i')) ∧
  (1 ≤ j → ∀ x ∈ ShellPieces.openBox j z,
    ConfigSpace.minSeparation x ≤
        ENNReal.ofReal (ShellPieces.pairDistConst * PieceScales.dyadicScale j) ∧
    ∃ y ∈ ConfigSpace.diagonalSet n,
      ConfigSpace.euclidNorm (x - y) ≤ ShellPieces.diagDistConst * PieceScales.dyadicScale j) ∧
  ∀ x ∈ ShellPieces.openBox j z,
    ConfigSpace.euclidNorm (x - ShellPieces.pieceCentre j z) ≤ Real.sqrt n ∧
    1 + ConfigSpace.euclidNorm (ShellPieces.pieceCentre j z) ≤
      (1 + Real.sqrt n) * (1 + ConfigSpace.euclidNorm x) ∧
    1 + ConfigSpace.euclidNorm x ≤
      (1 + Real.sqrt n) * (1 + ConfigSpace.euclidNorm (ShellPieces.pieceCentre j z))
def centresInAnnulus (n j t : ℕ) : Set (ShellPieces.LatticePt n) :=
  {z | (j, z) ∈ ShellPieces.activeIndices n ∧
    (t : ℝ) ≤ ConfigSpace.euclidNorm (ShellPieces.pieceCentre j z) ∧
    ConfigSpace.euclidNorm (ShellPieces.pieceCentre j z) < t + 1}
def CentreCount (n : ℕ) : Prop :=
  ∀ j t : ℕ,
    (1 ≤ j → (ShellPieces.cardOf (centresInAnnulus n j t) : ℝ≥0∞) ≤
      ENNReal.ofReal (ShellPieces.countConst n * (1 + (t : ℝ)) ^ (4 * n - 4) *
        PieceScales.dyadicScale j ^ (4 - 4 * (n : ℤ)))) ∧
    (j = 0 → (ShellPieces.cardOf (centresInAnnulus n j t) : ℝ≥0∞) ≤
      ENNReal.ofReal (ShellPieces.countConst n * (1 + (t : ℝ)) ^ (4 * n)))
def ShellPiecesBound : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    BoxesNested n ∧
    (∀ (j : ℕ) (z : ShellPieces.LatticePt n), PieceProperties j z) ∧
    SumsToOne n ∧
    DerivBoundFormula n ∧
    (∀ p ∈ ShellPieces.activeIndices n, BoxGeometry p.1 p.2) ∧
    CentreCount n
end YangMills.Construction.ShellPieceBounds
end
