import YangMills.Construction.InfiniteLattice.BondFamiliesJoinsAndContinuousFunctionsOfFinitelyManyBonds
import YangMills.Construction.InfiniteLattice.SpecificationOnObservables
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
def GibbsCharacterizations : Prop :=
  ∀ (a : ℝ) (ha : 0 < a) (β : ℝ), 0 < β → ∀ ν : GibbsAtFixedSpacing.BorelProb a,
    List.TFAE
      [IsGibbs β ν.1,
        ∀ (W : LinkWindow a) (F : GaugeField a → ℂ), IsBoundedObservable F →
          ν.integral (W.conditionalAverage ha β F) = ν.integral F,
        ∀ (W : LinkWindow a), ∀ F ∈ FieldsAtSpacing.continuousFiniteLinkFunctions a,
          ν.integral (W.conditionalAverage ha β F) = ν.integral F]
end InfiniteLattice
end YangMills.Construction
