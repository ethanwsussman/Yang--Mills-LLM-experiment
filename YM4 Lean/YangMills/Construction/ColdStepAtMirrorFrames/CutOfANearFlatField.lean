import YangMills.Construction.ColdStepAtMirrorFrames.DerivativeAlongAFlow
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsInABlock
import YangMills.Construction.ColdStepAtMirrorFrames.SumAgainstThreeFlatResponses
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
open BlockOffsets
variable {F : BlockFrame}
def CutoffNearFlatField : Prop :=
  ∀ (C₉ : ℝ) (R₁ : ℕ), 1 ≤ C₉ → 4 ≤ R₁ → ∃ (R₂ : ℕ) (σ₀ A : ℝ), R₁ ≤ R₂ ∧ 0 < σ₀ ∧ 0 ≤ A ∧
    ∀ (σ : ℝ) (F : BlockFrame) (W : F.GaugeField F.depth) (Y : F.Cell), 0 < σ → σ ≤ σ₀ →
      Odd F.blockSide → 3 ≤ F.blockSide →
      IsLargeCubicTorus F → IsSmallCurvature (3 / 4 * σ) W →
      (∀ b : F.Site F.depth × Fin 4, cellSupDist (enclosingCell b.1) Y ≤ R₂ + 2 →
        distFromOne (W b.1 b.2) ≤ C₉ * (1 + cellSupDist (enclosingCell b.1) Y) * σ) →
      ∃ B : F.Site F.depth → Fin 4 → imaginaryQuaternions,
        (∀ u : ℝ, 0 ≤ u → u ≤ 1 → IsSmallCurvature σ (expFlow B (uniformField F F.depth) u)) ∧
        (∀ b : F.Site F.depth × Fin 4, cellSupDist (enclosingCell b.1) Y ≤ R₁ →
          expFlow B (uniformField F F.depth) 1 b.1 b.2 = W b.1 b.2) ∧
        ∑ b ∈ fineBonds F, ‖B b.1 b.2‖ ≤ A * (F.blockSide : ℝ) ^ 4 * σ
end ColdStepAtMirrorFrames
end YangMills.Construction
end
