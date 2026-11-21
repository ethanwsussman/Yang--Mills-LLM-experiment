import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.LawOnABoxOfTheFlow.LimitFormDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction
namespace LimitForms
open TorusFields TorusLumps RenormalizationStepParameters ResponseInTheExpansion
def cubeLimitFormStatement : Prop :=
  ∀ Tb : ParameterAssignment, Tb.Admissible → ∃ (c C : ℝ) (R₀ : ℕ), 0 < c ∧ ∀ k : ℕ,
    ∃ Q : IntBond → IntBond → ℝ,
    IsLimitForm Tb.coupling Tb.coercivity c C Tb.side k Q ∧
    ∀ (n : ℕ) [NeZero n] (o : TorusSite n) (R : ℕ), R₀ ≤ R → 16 * R < n → ∀ b b' : IntBond,
      TorusFields.BondOffsetInBox (3 * R / 2) b → TorusFields.BondOffsetInBox (3 * R / 2) b' →
      |mixedDeriv (actionAtLevel Tb.coupling Tb.side k (supBall o (2 * R))) (trivialField n)
          ![bondFrom o b, bondFrom o b'] ![quaternionI, quaternionI] -
          Q b b'| ≤ Real.exp (-(c * R))
end LimitForms
end YangMills.Construction
end
