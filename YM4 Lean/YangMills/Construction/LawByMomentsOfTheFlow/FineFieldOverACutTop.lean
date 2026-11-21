import YangMills.Construction.LawByMomentsOfTheFlow.CurlOverAReference
import YangMills.Construction.LawByMomentsOfTheFlow.FrameOverACutTop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.MomentLaw
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
open Classical in
def freeImaginaryCoord (s : StepSettings.ChartSetting R n) (η : StepSettings.FreeCoords s.free)
    (b : TorusFields.TorusBond (n * R.params.side)) : BlockAverages.imaginaryQuaternions :=
  if hb : b ∈ s.free then ColdStepAtMirrorFrames.toImaginary (η ⟨b, hb⟩) else 0
open Classical in
def freeCoordSize (s : StepSettings.ChartSetting R n) (η : StepSettings.FreeCoords s.free)
    (b : TorusFields.TorusBond (n * R.params.side)) : ℝ :=
  if hb : b ∈ s.free then StepSettings.coordNorm (η ⟨b, hb⟩) else 0
structure FramesNearResponse (R : StepSettings.StepSetup) {n : ℕ} [NeZero n]
    (A : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions)
    (M : TorusFields.TorusBond (n * R.params.side) → BlockAverages.imaginaryQuaternions)
    (o : TorusFields.TorusSite (n * R.params.side)) (D : ℕ) (v ω κ : ℝ) : Prop where
  eq_zero_of_not_mem : ∀ b, b ∉ StepCosts.chartBonds R.params.side n → M b = 0
  frame_le : ∀ b ∈ StepCosts.chartBonds R.params.side n, TorusFields.supDist b.1 o ≤ D →
    ‖StepCosts.frameCoord R.params R.anchorRadius R.depth R.frameReach (expField 1 A) b +
        crossingComponent R.params A b - M b‖ ≤ κ * weightedBondSize o v b ^ 2 + ω
  response_le : ∀ b ∈ StepCosts.chartBonds R.params.side n, TorusFields.supDist b.1 o ≤ D →
    ‖M b - crossingComponent R.params A b‖ ≤ κ * weightedBondSize o v b
  crossing_le : ∀ b ∈ StepCosts.chartBonds R.params.side n, TorusFields.supDist b.1 o ≤ D →
    ‖crossingComponent R.params A b‖ ≤ κ * weightedBondSize o v b
  curl_le : ∀ (x : TorusFields.TorusSite (n * R.params.side)) (μ ν : Fin 4), μ < ν →
    ‖ResponseInTheExpansion.lieFormCurl M (x, μ, ν)‖ ≤ v / 16
def fineFieldOverCutTopStatement : Prop :=
  ∀ (R : StepSettings.StepSetup) (n : ℕ) [NeZero n] (A : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions)
    (M : TorusFields.TorusBond (n * R.params.side) → BlockAverages.imaginaryQuaternions)
    (o : TorusFields.TorusSite (n * R.params.side)) (D : ℕ)
    (v ω κ : ℝ), Odd R.params.side → 2 ≤ n → FramesNearResponse R A M o D v ω κ → 1 ≤ κ → 0 ≤ v → 0 ≤ ω →
    ω ≤ 1 / 64 → 0 ≤ R.ballRadius → R.ballRadius ≤ 1 / 64 → κ * (((D : ℝ) + 1) * v) ≤ 1 / 64 →
    ∀ η : StepSettings.FreeCoords (coldSettingOver R (expField 1 A)).free,
      (∀ b, StepSettings.coordNorm (η b) ≤ R.ballRadius) →
      IsNearReference o D ((coldSettingOver R (expField 1 A)).field η) ((coldSettingOver R (expField 1 A)).field 0) M
        (freeImaginaryCoord (coldSettingOver R (expField 1 A)) η) (freeCoordSize (coldSettingOver R (expField 1 A)) η)
        v ω (100 * κ ^ 2)
end YangMills.Construction.MomentLaw
end
