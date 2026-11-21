import YangMills.Construction.ResponseInTheExpansion.CoordinateOfASmallForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.MomentMethod
variable {F : BlockAverages.BlockFrame}
def decayWeightedNorm (δ : ℝ) (Y : F.Cell) (D : F.Cell → Fin 4 → BlockAverages.imaginaryQuaternions) : ℝ :=
  ∑ z ∈ ColdStepAtMirrorFrames.finiteCells F, ∑ i : Fin 4,
    Real.exp (-(δ / 2 * (BlockAverages.cellSupDist Y z : ℝ))) * ‖D z i‖
def coldFormCoordinateStatement : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdStepAtMirrorFrames.ColdChainParameters), Odd L → c.Admissible a L → ∃ K : ℝ, 0 ≤ K ∧
    ∀ (F : BlockAverages.BlockFrame) (b : F.Site F.depth × Fin 4) (D : F.Cell → Fin 4 → BlockAverages.imaginaryQuaternions)
      (X : BlockAverages.imaginaryQuaternions), ColdStepAtMirrorFrames.IsBlockTorus L F →
      b ∈ BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells F) → ‖X‖ = 1 →
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 → ColdStepAtMirrorFrames.IsSmallCurvature c.σA
        (ColdStepAtMirrorFrames.leftTranslate (fun y i => u • D y i) (BlockAverages.flatTopField (F := F)))) →
      ‖((ColdStepAtMirrorFrames.torusCoordinate a c.ρA b
          (ColdStepAtMirrorFrames.leftTranslate D (BlockAverages.flatTopField (F := F))) -
          WeightedResponses.flatLinearPart a c.ρA X b D : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ ≤
        K * decayWeightedNorm c.δ₁ (BlockAverages.enclosingCell b.1) D ^ 2 ∧
      ‖((WeightedResponses.flatLinearPart a c.ρA X b D : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ ≤
        K * decayWeightedNorm c.δ₁ (BlockAverages.enclosingCell b.1) D
end YangMills.Construction.MomentMethod
end
