import YangMills.Construction.ColdStepAtMirrorFrames.DerivativeAlongAFlow
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsInABlock
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
open BlockOffsets
def FlowBetweenFields : Prop :=
  ∀ (F F' : BlockFrame) (T : Finset (F.Site F.depth × Fin 4)) (W : F.GaugeField F.depth)
    (W' : F'.GaugeField F'.depth) (y : F.Site F.depth) (y' : F'.Site F'.depth) (R : ℕ) (ε s σ : ℝ),
    (∀ b, b ∈ T) → (∀ i, 2 * R + 2 < F.period F.depth i) →
    (∀ i, 2 * R + 2 < F'.period F'.depth i) → 0 ≤ ε → ε ≤ 1 → IsSmallCurvature s W → s + 8 * ε < σ →
    (∀ (g : Fin 4 → ℤ) (i : Fin 4), WithinRadius R g →
      distFromOne (W' (y' + siteOfCoords F'.depth g) i * (W (y + siteOfCoords F.depth g) i)⁻¹) ≤ ε) →
    ∃ B : F.Site F.depth → Fin 4 → imaginaryQuaternions,
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 → IsSmallCurvature σ (expFlow B W u)) ∧
      AgreeOnBox (expFlow B W 1) W' y y' R ∧ ∑ b ∈ T, ‖B b.1 b.2‖ ≤ 4 * (2 * (R : ℝ) + 1) ^ 4 * (2 * ε)
end ColdStepAtMirrorFrames
end YangMills.Construction
end
