import YangMills.Construction.Towers.TheSecondDerivativesOfTheDensity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity
def SecondDerivativeSumAtLinearAngle : Prop :=
  ∀ z : ℝ, 0 < z → ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L →
    secondDerivativeSum z (FullSpace.linearAbelianAngle :
        FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) = (massiveStiffness hL z : ℂ)
end YangMills.Construction.Tower.AbelianFieldDensity
end
