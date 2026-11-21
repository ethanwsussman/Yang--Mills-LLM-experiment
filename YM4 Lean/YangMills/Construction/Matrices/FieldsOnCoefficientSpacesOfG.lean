import YangMills.Construction.Matrices.GroupsOfFactsOfHarmonicAnalysisOnG
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpinHarmonics
def AllRightFieldFacts : Prop :=
  ∀ l : HalfNatural, RightFieldFacts l
end YangMills.Construction.SpinHarmonics
end
