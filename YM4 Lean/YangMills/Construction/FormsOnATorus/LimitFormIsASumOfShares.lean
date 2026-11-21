import YangMills.Construction.ClusterExpansionOfAStep.SharesAreACurvatureFamily
import YangMills.Construction.LawOnABoxOfTheFlow.LimitFormDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped Quaternion
namespace YangMills.Construction.LimitForms
open RenormalizationStepParameters TorusFields
def limitFormTranslateSumStatement : Prop :=
  ∀ Tb : ParameterAssignment, Tb.Admissible → ∀ (c C : ℝ) (k : ℕ) (Q : IntBond → IntBond → ℝ), 0 < c →
    IsLimitForm Tb.coupling Tb.coercivity c C Tb.side k Q →
    ∃ q : IntBond → IntBond → ℝ,
      (∀ b b', Tendsto (fun n => mixedDeriv (ShareFamilies.levelShareFamily Tb.coupling Tb.side k n 0) (trivialField n)
        ![TorusLumps.bondFrom 0 b, TorusLumps.bondFrom 0 b']
        ![TorusLumps.quaternionI, TorusLumps.quaternionI]) atTop (𝓝 (q b b'))) ∧
      ∀ b b', HasSum (fun u : Fin 4 → ℤ => q (b.1 + u, b.2) (b'.1 + u, b'.2)) (Q b b')
end YangMills.Construction.LimitForms
end
