import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric PeriodicLattice.DirichletOperators
namespace SeparatedClasses.SingleSequence
open SequenceData
def NestedOneFormsCorrespond : Prop :=
  ∀ s : SequenceData,
    ∀ R, s.IsNestedRegions R → s.oneFormData.Corresponds (oneFormDataOfNested R) (s.toTorus R.side)
end SeparatedClasses.SingleSequence
end YangMills.Construction
end
