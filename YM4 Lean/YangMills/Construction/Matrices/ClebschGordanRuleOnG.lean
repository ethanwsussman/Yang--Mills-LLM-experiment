import YangMills.Construction.Matrices.GroupsOfFactsOfHarmonicAnalysisOnG
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpinHarmonics
def AllClebschGordan : Prop :=
  ∀ l : HalfNatural, ClebschGordanFacts l
end YangMills.Construction.SpinHarmonics
end
