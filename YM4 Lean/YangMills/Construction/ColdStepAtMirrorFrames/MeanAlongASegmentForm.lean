import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
def openPolyball (ι : Type) (ρ : ℝ) : Set (BondField ι) := {η | ∀ b, ‖η b‖ < ρ}
variable {ι : Type}
def segmentInterpolant (A B : BondField ι → ℝ) (v : ℝ) : BondField ι → ℝ :=
  fun η => v * B η + (1 - v) * A η
def MeanDifferenceBoundAlongSegment : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : ℝ) (r : ℝ → ℝ)
    (A B H₀ H₁ : BondField ι → ℝ) (M c : ℝ), 0 < ρ → IsRadialCutoff ρ r →
    ContinuousOn A (openPolyball ι ρ) → ContinuousOn B (openPolyball ι ρ) →
    ContinuousOn H₀ (openPolyball ι ρ) → ContinuousOn H₁ (openPolyball ι ρ) →
    (∀ η ∈ openPolyball ι ρ, |A η| ≤ M ∧ |B η| ≤ M ∧ |H₀ η| ≤ M ∧ |H₁ η| ≤ M) →
    (∀ v : ℝ, 0 ≤ v → v ≤ 1 →
      |ballExpectation r (segmentInterpolant A B v) (fun η => H₁ η - H₀ η) -
        ballCovariance r (segmentInterpolant A B v) (segmentInterpolant H₀ H₁ v)
          (fun η => B η - A η)| ≤ c) →
    |ballExpectation r B H₁ - ballExpectation r A H₀| ≤ c
end ColdStepAtMirrorFrames
end YangMills.Construction
end
