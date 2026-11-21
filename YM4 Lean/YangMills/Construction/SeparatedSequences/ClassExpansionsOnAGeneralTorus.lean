import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric PeriodicLattice.DirichletOperators
namespace SeparatedClasses.SingleSequence
open SequenceData
def GaugeOneFormsCorrespond : Prop :=
  ∀ s : SequenceData,
    ∀ W, s.IsGaugeSetting W →
      s.oneFormData.Corresponds (oneFormDataOfGauge W) (s.toTorus W.data.torusSide)
end SeparatedClasses.SingleSequence
end YangMills.Construction
end
