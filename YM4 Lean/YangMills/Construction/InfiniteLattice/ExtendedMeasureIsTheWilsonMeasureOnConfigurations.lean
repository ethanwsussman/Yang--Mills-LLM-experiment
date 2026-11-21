import YangMills.Construction.InfiniteLattice.PeriodicExtensionsStatesAndTorusFunctionalsAtOneSpacing
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
namespace FixedSpacing
def LiftedGibbsIsLiftedWilsonMeasure : Prop :=
  ∀ D : Setup, D.liftedGibbs = InfiniteLattice.liftedWilsonMeasure D.L D.m D.level D.β
end FixedSpacing
end YangMills.Construction
