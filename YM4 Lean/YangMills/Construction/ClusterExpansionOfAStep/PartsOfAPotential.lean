import YangMills.Construction.ClusterExpansionOfAStep.SettingsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace StepSettings
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields
variable {R : StepSetup} {n : ℕ}
def ChartSetting.totalDensity [NeZero n] (s : ChartSetting R n) (η : FreeCoords s.free) : ℝ :=
  ∑ Y : TorusSite n, s.blockDensity (s.field η) Y
structure ChartSetting.IsPotentialPiece [NeZero n] (s : ChartSetting R n) (g : FreeCoords s.free → ℝ) (K : ℝ) :
    Prop where
  smooth : ∀ η, s.InBalls η → ContDiffAt ℝ 3 g η
  standingConstraints : ∃ M : s.free → s.free → ℝ, (∀ η, s.InBalls η → ∀ b b' X X', ‖X‖ = 1 → ‖X'‖ = 1 →
      |mixedSecondDeriv g η b b' X X'| ≤ M b b') ∧
    ∀ b, ∑ b', M b b' * Real.exp (2 * R.params.rt * bondBlockDist (R := R) (n := n) b.1 b'.1) ≤ K
  first : ∀ η, s.InBalls η → ∀ b X, ‖X‖ = 1 →
    |deriv (fun τ : ℝ => g (Function.update η b (η b + τ • X))) 0| ≤ K
theorem ChartSetting.IsPotentialPiece.mono [NeZero n] {s : ChartSetting R n} {g : FreeCoords s.free → ℝ}
    {K K' : ℝ} (h : s.IsPotentialPiece g K) (hK : K ≤ K') : s.IsPotentialPiece g K' := by
  obtain ⟨M, h1, h2⟩ := h.standingConstraints
  exact ⟨h.smooth, ⟨M, h1, fun b => (h2 b).trans hK⟩, fun η hη b X hX => (h.first η hη b X hX).trans hK⟩
end StepSettings
end YangMills.Construction
end
