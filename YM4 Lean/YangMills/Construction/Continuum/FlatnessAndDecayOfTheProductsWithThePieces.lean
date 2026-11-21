import YangMills.Construction.Continuum.SystemsModesAndScaledNorms
import YangMills.Construction.Continuum.SystemsOfThePiecesAndTheLeibnizAndTaylorNumbers
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.PieceProducts
open PieceSystems ConfigSpace PieceScales ShellPieces SmoothMaps
variable {n : ℕ}
def pieceBoxSystem (p : activeIndices n) : PointSystem n where
  base := (centreAndSide p).1
  scale := (centreAndSide p).2
  scale_pos := mul_pos isSideConstant_sideConstant.1 (zpow_pos (by norm_num) _)
  scale_le_half := by
    have h₁ : dyadicScale p.1.1 ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by simp)
    have h₀ : 0 < dyadicScale p.1.1 := zpow_pos (by norm_num) _
    have h₂ := isSideConstant_sideConstant
    show sideConstant * dyadicScale p.1.1 ≤ 1 / 2
    nlinarith [h₂.1, h₂.2]
def pieceMul (j : ℕ) (z : LatticePt n) (φ : Config n → ℂ) : Config n → ℂ :=
  fun x => (piece j z x : ℂ) * φ x
def ProductBounds : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (j : ℕ) (z : LatticePt n) (hp : (j, z) ∈ activeIndices n),
    let Q : PointSystem n := pieceBoxSystem ⟨(j, z), hp⟩
    (Q.IsSeparated ∧
      (∀ i, Q.box i = innerBox j z i) ∧
      (∀ i, Q.midBox i = middleBox j z i) ∧
      (∀ i, Q.outerBox i = outerBox j z i) ∧
      ENNReal.ofReal (1 / 2 * (2 : ℝ) ^ (-(j : ℤ))) ≤ Q.boxGap ∧
      ∀ φ ∈ smoothSet (Config n),
        ContDiff ℝ ∞ (pieceMul j z φ) ∧
        tsupport (pieceMul j z φ) ⊆ tsupport φ ∩ cylinderSet Q.box ∧
        pieceMul j z φ ∈ Q.supportedClass) ∧
    ∀ φ ∈ flatSchwartzSet n,
      (1 ≤ j → ∀ r : ℕ, 1 ≤ r →
        ENNReal.ofReal (scaledSupNorm (5 * n + 1) (pieceSide j) (pieceMul j z φ)) ≤
          ENNReal.ofReal (leibnizConst n * taylorConst n * (2 : ℝ) ^ (-((j * r : ℕ) : ℤ)) *
            ((1 + ConfigSpace.euclidNorm (pieceCentre j z)) ^ (4 * n + 2))⁻¹) *
          decaySeminorm (4 * n + 2) (5 * n + 1 + r) φ) ∧
      (j = 0 →
        ENNReal.ofReal (scaledSupNorm (5 * n + 1) (pieceSide j) (pieceMul j z φ)) ≤
          ENNReal.ofReal (leibnizConst n * taylorConst n *
            ((1 + ConfigSpace.euclidNorm (pieceCentre j z)) ^ (4 * n + 2))⁻¹) *
          decaySeminorm (4 * n + 2) (5 * n + 1) φ)
end YangMills.Construction.PieceProducts
