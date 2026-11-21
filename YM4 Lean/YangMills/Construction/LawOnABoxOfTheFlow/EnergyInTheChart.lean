import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.LawOnABoxOfTheFlow.BoxDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
def chartEnergyStatement : Prop :=
  ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → ∀ κ₀ : ℝ, 1 / 27 ≤ κ₀ → κ₀ ≤ 1 / 21 →
    ∀ C₀ : ℝ, 0 < C₀ → ∃ K x₀ : ℝ,
    ∀ (x : ℝ) (R k n : ℕ) [NeZero n] (o : TorusFields.TorusSite n)
      (A : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions),
      x₀ ≤ x → R = boxRadius κ₀ x → 16 * R < n → IsAxialSmall o R (boxScale x) A →
      ∀ ζ ∈ sliceEllipsoid T.coupling T.side k o R A (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2),
        ∀ W : TorusFields.TorusField n, IsInChart (ResponseInTheExpansion.supBall o (2 * R)) A ζ W →
          |x * TorusFields.actionAtLevel T.coupling T.side k (ResponseInTheExpansion.supBall o (2 * R)) W -
              x / 2 * hessianForm T.coupling T.side k (ResponseInTheExpansion.supBall o (2 * R))
                (A + ζ) (A + ζ)| ≤
            K * (R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3
end YangMills.Construction.BoxGaussian
end
