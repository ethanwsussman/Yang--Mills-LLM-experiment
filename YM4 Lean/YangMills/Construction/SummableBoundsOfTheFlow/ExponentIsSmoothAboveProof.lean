import YangMills.Construction.SummableBoundsOfTheFlow.ExponentIsSmoothAbove
import YangMills.Construction.SummableBoundsOfTheFlow.ExponentReadAbove
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames IteratedDerivative Interpolation
namespace Interpolation
theorem interpolatedBlockExponentSmooth (hA : JointMixedDerivEqDerivAlong)
    (hRay : RayGradientSumSmoothAndBounded) (hRead : cellExponentRotatedEvalStatement) :
    interpolatedBlockExponentSmoothStatement := by
  intro F s a ρA ρ x κ κ₂ δ₂ m Kf Dk V Y η k c X hne hker hη hX
  have hball : ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ b, ‖(v • η) b‖ ≤ ρ := by
    intro v hv b
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hv.1]
    nlinarith [norm_nonneg (η b), hη b, hv.2]
  have hs : ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ n : ℕ, ContDiffAt ℝ (n : WithTop ℕ∞)
      (rotatedEval (interpolatedEnergy s a ρA m) V c X) (v • η, 0) := fun v hv n =>
    (hA F V _ (v • η) k c X).1 hne
      (fun l b u hl hu => ((hker _ (hball v hv)).energy l k b u c X hl hu hX).1) n
  have hray : ContDiffAt ℝ ((k + 2 : ℕ) : WithTop ℕ∞)
      (rayGradientSum (rotatedEval (interpolatedEnergy s a ρA m) V c X) (cellChordBonds Y)) (η, 0) := by
    have := (hRay _ _ (Fin k → ℝ) (rotatedEval (interpolatedEnergy s a ρA m) V c X) (cellChordBonds Y) η (parameterBasis k)
      (fun v hv => hs v hv _)).1
    simpa [parameterBasis] using this
  have e := hRead.1 F s a ρA x m Y V η k c X fun v hv => hs v hv 1
  have hg : ContDiffAt ℝ ((k + 2 : ℕ) : WithTop ℕ∞) (fun p => ∑ c₀ ∈ (innerBonds (finiteCells F) F.top).filter
      (fun c => c.1 = Y), (rotatedEval (contourHaarGap s a ρA x m c₀) V c X p - haarGap (a * x))) (η, 0) :=
    ContDiffAt.sum fun c₀ _ => ((hA F V _ η k c X).1 hne
      (fun l b u hl hu => ((hker η hη).gap c₀ l k b u c X (by omega) hu hX).1) _).sub contDiffAt_const
  have hh : ContDiffAt ℝ ((k + 2 : ℕ) : WithTop ℕ∞) (fun p => ∑ b ∈ cellChordBonds Y,
      rotatedEval (interpolatedHaarLogRatio s a ρA m b) V c X p) (η, 0) :=
    ContDiffAt.sum fun b₀ _ => (hA F V _ η k c X).1 hne
      (fun l b u hl hu => ((hker η hη).haar b₀ l k b u c X (by omega) hu hX).1) _
  exact (((contDiffAt_const.mul hray).sub hg).sub hh).congr_of_eventuallyEq e
end Interpolation
end YangMills.Construction
end
