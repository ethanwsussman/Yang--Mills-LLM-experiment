import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric PeriodicLattice.DirichletOperators
namespace SeparatedClasses.ClassOneFormsOfParameters
open SingleSequence SingleSequence.SequenceData
def Statement : Prop :=
  ∀ s : SequenceData,
    OneFormData.Corresponds s.oneFormData.toOneFormData s.classOneForms id
end SeparatedClasses.ClassOneFormsOfParameters
end YangMills.Construction
