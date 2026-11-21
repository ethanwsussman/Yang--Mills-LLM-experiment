import YangMills.Construction.Matrices.GroupsOfFactsOfHarmonicAnalysisOnG
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpinHarmonics
def AllCharacterFacts : Prop :=
  ∀ l : HalfNatural, SpinCharacterFacts l
end YangMills.Construction.SpinHarmonics
end
