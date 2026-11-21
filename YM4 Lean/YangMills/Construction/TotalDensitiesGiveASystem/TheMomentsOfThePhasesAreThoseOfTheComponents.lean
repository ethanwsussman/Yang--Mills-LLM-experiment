import YangMills.Construction.TotalDensitiesGiveASystem.PhasesOfALimitDefs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
open SystemsWithFiveBounds LimitTheorem SeparatedTuples
def phaseMomentsConvergeStatement : Prop :=
  ∀ (L : ℕ), Conventions.IsAdmissibleBlockingFactor L → ∀ (IsPair : ℕ+ → ℝ → Prop) (Q : PairSequence L IsPair)
    (S : CumulantFamily), (∀ j, 0 < Q.coupling j) → Q.Defines S → ∀ κ, IsConditionalKernel Q κ →
    ∀ A : DecompositionData, A.IsCanonical (centredOf S) →
    ∀ (X : SepTuple) (Y : List SepTuple),
      Tendsto (phaseMoment Q κ X Y) atTop
        (𝓝 (∫ ξ, A.comp ξ X * (Y.map fun Z => A.comp ξ Z).prod ∂A.law))
end YangMills.Construction.TotalDensitiesGiveASystem
end
