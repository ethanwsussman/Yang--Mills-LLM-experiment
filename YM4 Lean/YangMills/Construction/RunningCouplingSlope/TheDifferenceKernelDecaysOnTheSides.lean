import YangMills.Construction.RunningCouplingSlope.WaveSumsOfTheKernels
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def DifferenceKernelDecaysUniformly : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ θ C : ℝ, 0 < θ ∧ 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ x : TorusFields.TorusSite (2 * L ^ n),
      |differenceKernelFinite a L n k (centredCoords x)| ≤
        C * Real.exp (-(θ * ∑ μ, |(centredCoords x μ : ℝ)|))
end YangMills.Construction.RunningCouplingSlope
end
