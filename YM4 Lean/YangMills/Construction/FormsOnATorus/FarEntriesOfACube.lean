import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.LawOnABoxOfTheFlow.LimitFormDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.LimitForms
open RenormalizationStepParameters TorusFields
def offDiagonalDecayStatement : Prop :=
  ∀ Tb : ParameterAssignment, Tb.Admissible → ∃ (c : ℝ) (R₀ : ℕ), 0 < c ∧
    ∀ (k n : ℕ) [NeZero n] (o : TorusSite n) (R : ℕ), R₀ ≤ R → 16 * R < n → ∀ b b' : IntBond,
      BondOffsetInBox (2 * R) b → BondOffsetInBox (2 * R) b' → R ≤ 4 * bondSupDist b b' →
      |mixedDeriv (actionAtLevel Tb.coupling Tb.side k (ResponseInTheExpansion.supBall o (2 * R))) (trivialField n)
          ![TorusLumps.bondFrom o b, TorusLumps.bondFrom o b'] ![TorusLumps.quaternionI, TorusLumps.quaternionI]| ≤
        Real.exp (-(c * R))
end YangMills.Construction.LimitForms
end
