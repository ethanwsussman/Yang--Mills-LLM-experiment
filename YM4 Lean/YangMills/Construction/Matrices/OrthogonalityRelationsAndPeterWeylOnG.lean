import YangMills.Construction.Matrices.GroupsOfFactsOfHarmonicAnalysisOnG
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpinHarmonics
def PeterWeylOrthogonality.Statement : Prop :=
  ∀ j k : HalfNatural, PeterWeylFacts j k
end YangMills.Construction.SpinHarmonics
