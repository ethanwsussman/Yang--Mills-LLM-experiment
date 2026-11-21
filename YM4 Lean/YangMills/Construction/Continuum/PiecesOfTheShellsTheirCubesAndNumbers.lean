import YangMills.Construction.Continuum.DyadicPieceScales
import YangMills.Construction.Continuum.FlatSchwartzAndTuples
import YangMills.Construction.Continuum.ShellFunctionsAroundTheDiagonals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ShellPieces
open MeasureTheory YangMills.Construction.Bumps YangMills.Construction.ConfigSpace YangMills.Construction.PieceScales YangMills.Construction.DiagonalShells
variable {n : ℕ}
abbrev LatticePt (n : ℕ) : Type := Fin n → Fin 4 → ℤ
def shiftSet (a : Config n) (S : Set (Config n)) : Set (Config n) := (fun x => a + x) '' S
def bumpProduct (j : ℕ) (z : LatticePt n) (x : Config n) : ℝ :=
  ∏ i, ∏ c, mollifiedIndicator (2 * x i c / pieceSide j - z i c)
def piece (j : ℕ) (z : LatticePt n) : Config n → ℝ :=
  fun x => shellLayer j x * bumpProduct j z x
def pieceCentre (j : ℕ) (z : LatticePt n) : Config n :=
  fun i c => 1 / 2 * pieceSide j * z i c
def openBox (j : ℕ) (z : LatticePt n) : Set (Config n) :=
  shiftSet (pieceCentre j z)
    {x | ∀ i c, x i c ∈ Set.Ioo (-(1 / 2 * pieceSide j)) (1 / 2 * pieceSide j)}
def activeIndices (n : ℕ) : Set (ℕ × LatticePt n) :=
  {p | piece p.1 p.2 ≠ 0}
def closedBox (a : Fin 4 → ℝ) (s : ℝ) : Set (Fin 4 → ℝ) :=
  {y | YangMills.Construction.EuclideanCoords.supCoord (y - a) ≤ s / 2}
def innerBox (j : ℕ) (z : LatticePt n) (i : Fin n) : Set (Fin 4 → ℝ) :=
  closedBox (pieceCentre j z i) (pieceSide j)
def middleBox (j : ℕ) (z : LatticePt n) (i : Fin n) : Set (Fin 4 → ℝ) :=
  closedBox (pieceCentre j z i) (3 / 2 * pieceSide j)
def outerBox (j : ℕ) (z : LatticePt n) (i : Fin n) : Set (Fin 4 → ℝ) :=
  closedBox (pieceCentre j z i) (2 * pieceSide j)
def lebesgueOn (D : ℕ) : Measure (Fin D → ℝ) := volume
def unitBallVol : ℕ → ℝ
  | 0 => 1
  | D + 1 =>
    (lebesgueOn (D + 1) {x | YangMills.Construction.EuclideanCoords.sqrtSumSq x ≤ 1}).toReal
def cardOf {α : Type*} (S : Set α) : ℕ∞ := S.encard
def halfPairs (n : ℕ) : ℝ := 1 / 2 * n * (n - 1)
def derivConst : ℝ :=
  2 * max tupleCutoffConst (2 * twiceGevreyConst * sideConstant⁻¹)
def derivBound (n r : ℕ) : ℝ :=
  2 * normalizerBound ^ (4 * n) * (derivConst * n) ^ r * (r.factorial : ℝ) ^ 2
def pairDistConst : ℝ := 4 + 2 * sideConstant
def diagDistConst : ℝ := Real.sqrt 2 * pairDistConst
def volumeCountConst : ℝ := (2 * pairDistConst) ^ 4 * (2 / sideConstant) ^ 4
def countConst (n : ℕ) : ℝ :=
  volumeCountConst ^ n * (1 + Real.sqrt n) ^ (4 * n) *
    max (halfPairs n * unitBallVol (4 * n - 4)) (unitBallVol (4 * n))
end YangMills.Construction.ShellPieces
