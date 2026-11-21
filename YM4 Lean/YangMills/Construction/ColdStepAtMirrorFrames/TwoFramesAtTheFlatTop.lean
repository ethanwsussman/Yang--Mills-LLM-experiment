import YangMills.Construction.ColdStepAtMirrorFrames.FramesAgainstTheLeastField
import YangMills.Construction.ColdStepAtMirrorFrames.StepDensityAndItsFrame
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def twoFramesGapBound (K : ℝ → ℝ) (T : StepParameters) (Cf Cw : ℝ) (m : ℕ) : ℝ :=
  K T.chainParams.δ₂ * (T.L : ℝ) ^ 12 * T.E * (Cw + 2) ^ 6 * Cf * Real.exp (-(3 / 8 * T.chainParams.δ₂ * m))
structure FramesAtUniformTop (T : StepParameters) (Cf Cw : ℝ) (m t : ℕ) (F : BlockFrame) : Prop where
  near : (∀ i, 4 * m + 5 < F.extent i) →
    FrameNearMinimizer T.a T.chainParams.ρA T.chainParams.δ₂ Cf T.σ m (uniformField F F.top)
  small : ∀ star, FrameSmallness star T.a T.chainParams.ρA T.chainParams.δ₂ T.chainParams.κ₂ Cw T.σ
    T.chainParams.Kk m (uniformField F F.top)
def twoFramesAtUniformTopStatement : Prop :=
  ∃ K : ℝ → ℝ, (∀ r, 0 ≤ K r) ∧ ∀ (T : StepParameters) (Cf Cw : ℝ), T.IsOrdered → 64 ≤ T.n₀ → 0 < Cf → 0 ≤ Cw →
    Cw * T.σ ≤ 1 →
    ∀ (t : ℕ) (x : ℝ) (f : LocalFamily), T.coupling ≤ x → 16 ≤ frameRadius x →
      IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f →
      (∀ n : ℕ, T.n₀ ≤ n → FramesAtUniformTop T Cf Cw (frameRadius x) t (cubicTorusFrame T.L t n)) →
      ∀ (b b' : (Fin 4 → ℤ) × Fin 4) (X X' : imaginaryQuaternions), ‖X‖ = 1 → ‖X'‖ = 1 → ∀ᶠ n in Filter.atTop,
        |secondDerivAtUniform (expansionAtFrameFamily T false x f) T.L t n b b' X X' -
          secondDerivAtUniform (expansionAtFrameFamily T true x f) T.L t n b b' X X'| ≤
          twoFramesGapBound K T Cf Cw (frameRadius x)
end YangMills.Construction.ColdStepAtMirrorFrames
end
