import YangMills.Construction.ClusterExpansionOfAStep.ConvexMeasureOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours ColdStepAtMirrorFrames StepSettings TorusFields TorusLumps
variable {R : StepSetup} {n : ℕ}
def weightedCov {free : Finset (TorusBond n)} (d F G : FreeCoords free → ℝ) : ℝ :=
  weightedMean d (fun η => F η * G η) - weightedMean d F * weightedMean d G
def partialSlope {free : Finset (TorusBond n)} (G : FreeCoords free → ℝ) (η : FreeCoords free) (b : free)
    (X : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  deriv (fun τ : ℝ => G (Function.update η b (η b + τ • X))) 0
def _root_.YangMills.Construction.StepSettings.ChartSetting.IsC1NearBalls (s : ChartSetting R n)
    (G : FreeCoords s.free → ℝ) : Prop :=
  ∃ U : Set (FreeCoords s.free), IsOpen U ∧ (∀ η, s.InBalls η → η ∈ U) ∧ ContDiffOn ℝ 1 G U
def _root_.YangMills.Construction.StepSettings.ChartSetting.SlopesBoundedBy (s : ChartSetting R n)
    (G : FreeCoords s.free → ℝ) (B : s.free → ℝ) : Prop :=
  ∀ η, s.InBalls η → ∀ b X, ‖X‖ = 1 → |partialSlope G η b X| ≤ B b
def ConvexLawEstimates : Prop :=
  ∀ (ℓ : StepParameters) (lam Cu : ℝ), 0 < ℓ.threshold → 0 < ℓ.rt → 0 < lam → 0 ≤ Cu → ∃ C : ℝ, 0 < C ∧
    ∀ (y : ℝ) (R : StepSetup), R.params = { ℓ with y₁ := y } → IsCutoff R.ballRadius R.barrierFn →
      0 < R.coupling →
      ∀ (n : ℕ) [NeZero n] (s : ChartSetting R n) (u : FreeCoords s.free → ℝ), s.HasFullDecay u lam Cu →
        (∀ (F G : FreeCoords s.free → ℝ) (BF BG : s.free → ℝ), s.IsC1NearBalls F → s.IsC1NearBalls G →
          s.SlopesBoundedBy F BF → s.SlopesBoundedBy G BG →
          |weightedCov (fun η => s.cutoffProduct η * Real.exp (-(u η))) F G| ≤
            C / R.coupling * ∑ b, ∑ b', BF b * Real.exp (-(R.params.rt * s.bondDist b b')) * BG b') ∧
        (∀ (A : s.free → ℝ), (∀ b X, ‖X‖ = 1 → |partialSlope u 0 b X| ≤ A b) → ∀ b,
          weightedMean (fun η => s.cutoffProduct η * Real.exp (-(u η))) (fun η => ‖η b‖ ^ 2) ≤
            C / R.coupling + C / R.coupling ^ 2 *
              ∑ b', Real.exp (-(2 * R.params.rt * s.bondDist b b')) * A b' ^ 2) ∧
        ∀ (X : Finset s.free) (F G : FreeCoords s.free → ℝ) (B : s.free → ℝ) (O : ℝ), Measurable F →
          (∀ η η' : FreeCoords s.free, (∀ b ∈ X, η b = η' b) → F η = F η') →
          (∀ η η', s.InBalls η → s.InBalls η' → |F η - F η'| ≤ O) →
          s.IsC1NearBalls G → s.SlopesBoundedBy G B →
          |weightedCov (fun η => s.cutoffProduct η * Real.exp (-(u η))) F G| ≤
            C * O * ∑ b ∈ X, ∑ b', B b' * Real.exp (-(R.params.rt * s.bondDist b b'))
end YangMills.Construction.ClusterExpansionOfAStep
end
