import YangMills.Construction.ResponseInTheExpansion.CoordinateOfASmallForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.WeightedResponses
open BlockAverages ColdStepAtMirrorFrames
def FlatLinearPartLocality : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), Odd L → c.Admissible a L → ∃ C r₀ : ℝ, 0 ≤ C ∧ 0 < r₀ ∧
    ∀ (F F' : BlockFrame) (Y : F.Cell) (Y' : F'.Cell) (R : ℕ) (o : Fin 4 → ℤ) (i : Fin 4)
      (B : F.Cell → Fin 4 → imaginaryQuaternions) (D : F'.Cell → Fin 4 → imaginaryQuaternions)
      (X : imaginaryQuaternions) (s : ℝ),
      IsBlockTorus L F → IsBlockTorus L F' → F'.depth = F.depth → (∀ l, 2 * R + 2 < F.extent l) →
      (∀ l, 2 * R + 2 < F'.extent l) →
      1 ≤ R → o ∈ centredCube L → fineBondAt Y 0 o i ∈ chordBonds (finiteCells F) →
      fineBondAt Y' 0 o i ∈ chordBonds (finiteCells F') → ‖X‖ = 1 → 0 ≤ s → (∀ z l, ‖B z l‖ ≤ s) →
      (∀ z l, ‖D z l‖ ≤ s) →
      (∀ (h : Fin 4 → ℤ) (l : Fin 4), BondWithinRadius R (h, l) →
        B (Y + siteOfCoords F.top h) l = D (Y' + siteOfCoords F'.top h) l) →
      ‖((flatLinearPart a c.ρA X (fineBondAt Y 0 o i) B : imaginaryQuaternions) : ℍ[ℝ]) -
          (flatLinearPart a c.ρA X (fineBondAt Y' 0 o i) D : imaginaryQuaternions)‖ ≤
        C * s * Real.exp (-(r₀ * (R : ℝ)))
end YangMills.Construction.WeightedResponses
end
