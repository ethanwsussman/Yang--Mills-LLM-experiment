import YangMills.Construction.ColdChainAtEveryLevel.PropertiesOfTheColdChainForm
import YangMills.Construction.ColdChainAtEveryLevel.ReferenceAndCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
def IsInnerOffset (L n : ℕ) (r : ℕ) (j : ℕ) (p : Fin 4 → ℤ) : Prop :=
  ∀ i, (L : ℤ) ^ j * |p i| ≤ ((r : ℤ) - 100) * (L : ℤ) ^ n
def agreeingPairsLocalityStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (F F' : BlockFrame) (m : ℕ) (S : Finset F.Cell) (S' : Finset F'.Cell) (s : ℝ)
    (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ),
    F'.blockSide = F.blockSide → F'.depth = F.depth → Odd F.blockSide → IsAdmissibleAmbient F →
    IsAdmissibleAmbient F' → 1024 ≤ m → IsOrthantRegular S m → IsOrthantRegular S' m → 0 < s → s ≤ c →
    IsCold S F.top s V → IsCold S' F'.top s V' → AgreeOnBall S V S' V' Y Y' r →
    (∀ (b h : Fin 4 → ℤ), IsInnerOffset F.blockSide F.top r 0 b →
      cellCentre 0 Y + siteOfCoords 0 b ∈ sitesOfCells S 0 → WithinRadius r h →
      Y + siteOfCoords F.top h ∈ S →
      leadingFrame S V (cellCentre 0 Y + siteOfCoords 0 b) (Y + siteOfCoords F.top h) =
        leadingFrame S' V' (cellCentre 0 Y' + siteOfCoords 0 b) (Y' + siteOfCoords F'.top h)) ∧
    ∀ (j : ℕ) (p : Fin 4 → ℤ) (i : Fin 4), j < F.top → IsInnerOffset F.blockSide F.top r j p →
      IsInnerOffset F.blockSide F.top r j (p + Pi.single i 1) →
      (cellCentre j Y + siteOfCoords j p, i) ∈ innerBonds S j →
      referenceGaugeField S V j (cellCentre j Y + siteOfCoords j p) i =
        referenceGaugeField S' V' j (cellCentre j Y' + siteOfCoords j p) i
end YangMills.Construction.BlockAverages
end
