import YangMills.Construction.Matrices.GroupsOfFactsOfHarmonicAnalysisOnG
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpinHarmonics
def CoeffProjections.Statement : Prop :=
  ∀ j k : HalfNatural, CoeffProjectionFacts j k
end YangMills.Construction.SpinHarmonics
