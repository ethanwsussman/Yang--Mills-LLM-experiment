import YangMills.Construction.SystemsWithFiveBounds.BoundsAtNumbers
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
open TestFunctions (IsLipschitzFor euclidDistR4 closedBallR4 sharpNormR4)
open InfiniteLattice (AmbientSpace smearedEnergy)
def radiusTransferConstant (M : ℝ) (N : BoundConstants) : ℝ :=
  256 * (1 + 80 * Real.pi * M) * (1 + N.onePointConst 1)
def OnePointDifferenceAllRadii : Prop :=
  ∀ (F : StatedSideFamily) (N : BoundConstants), BoundsHoldAt F N → ∀ (K : ℕ+) (β : ℝ),
    F.IsFirstPassage K β →
    ∀ ν ∈ F.stateSet F.L K β, ∀ ν' ∈ F.stateSet F.L K β, ∀ R : ℝ, 0 < R →
      ∀ f : AmbientSpace → ℝ, IsLipschitzFor euclidDistR4 f → (∃ x, tsupport f ⊆ closedBallR4 x R) →
        |(∫ U, smearedEnergy f U ∂ν) - ∫ U, smearedEnergy f U ∂ν'| ≤
          radiusTransferConstant F.M N * (1 + R) ^ 4 * sharpNormR4 F.M f
end YangMills.Construction.SystemsWithFiveBounds
end
