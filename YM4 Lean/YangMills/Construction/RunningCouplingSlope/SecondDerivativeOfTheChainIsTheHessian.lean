import YangMills.Construction.RunningCouplingSlope.FirstOrderOfTheLeastPoint
import YangMills.Construction.RunningCouplingSlope.HessianOfTheWholeChain
import YangMills.Construction.RunningCouplingSlope.TestOfATotal
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def SecondDerivAlongWaveEqHessian : Prop :=
  ∀ a : ℝ, 0 < a → ∀ (L : ℕ) [∀ n : ℕ, NeZero (2 * L ^ n)], Conventions.IsAdmissibleBlockingFactor L →
    ∀ k : ℕ, 1 ≤ k → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∀ᶠ n in atTop,
      ∀ (f : TorusFields.TorusSite (2 * L ^ n) → ℝ) (B : Tower.edgeFormSpace L n k k),
        (B : Tower.Edge L n k k → Matrices.ComplexMatrix2) = planeWaveValues L n k f →
        ∀ t : LevelTriple L n k, IsFirstVariation a B t →
          SlopeCoefficient.secondDerivAlong (SlopeCoefficient.chainLogarithm a ρ L k) (2 * L ^ n)
              (planeWaveOnTorus f) = hessianOfFreeEnergy a t t
end YangMills.Construction.RunningCouplingSlope
end
