import YangMills.Construction.TotalDensitiesGiveASystem.PhasesOfALimitDefs
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
open SystemsWithFiveBounds LimitTheorem SeparatedTuples
def phaseMomentsBoundedStatement : Prop :=
  ∀ (L : ℕ), Conventions.IsAdmissibleBlockingFactor L → ∀ (IsPair : ℕ+ → ℝ → Prop) (Q : PairSequence L IsPair)
    (S : CumulantFamily), (∀ j, 0 < Q.coupling j) → Q.Defines S → ∀ κ, IsConditionalKernel Q κ →
    ∀ (X : SepTuple) (t : ℕ), ∃ C : ℝ, ∀ j,
      Integrable (fun U => |centredMean Q j (κ j U).1 X| ^ t) (Q.state j) ∧
        ∫ U, |centredMean Q j (κ j U).1 X| ^ t ∂Q.state j ≤ C
end YangMills.Construction.TotalDensitiesGiveASystem
end
