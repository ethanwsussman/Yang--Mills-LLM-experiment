import YangMills.Construction.Conventions.LeveledParameters
import YangMills.Construction.Conventions.QuantityDependence
import YangMills.Construction.Towers.TheFamiliesOfTheTotalNormaliser
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OneLoopLaw.IncrementSum
open YangMills.Construction.PeriodicOperators.Tempered
structure StepData extends YangMills.Construction.Conventions.LeveledParameters where
  index : ℕ
theorem StepData.factor_pos (p : StepData) : 0 < p.L :=
  lt_of_lt_of_le (by norm_num) p.isAdmissible.2
def stepIncrement (p : StepData) : ℝ :=
  YangMills.Construction.OneLoopLaw.FunctionalStiffness.stiffnessConstant p.factor_pos
    (YangMills.Construction.Tower.stepNormaliserFamily p.L p.index)
def IncrementsSumToTotal : Prop :=
  (∀ L : ℕ, YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L →
    ∀ n : ℕ, IsTemperedFunctional L (YangMills.Construction.Tower.stepNormaliserFamily L n)) ∧
  YangMills.Construction.Conventions.DependsOnlyOnQuantities
    (fun p : StepData => (p.index, p.L)) stepIncrement ∧
  ∀ (L : ℕ) (hpos : 0 < L), YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L →
    ∀ k : ℕ,
    ∑ n ∈ Finset.range k,
        YangMills.Construction.OneLoopLaw.FunctionalStiffness.stiffnessConstant hpos
          (YangMills.Construction.Tower.stepNormaliserFamily L n) =
      YangMills.Construction.OneLoopLaw.FunctionalStiffness.stiffnessConstant hpos
        (YangMills.Construction.Tower.logNormaliserFamily L k)
end YangMills.Construction.OneLoopLaw.IncrementSum
end
