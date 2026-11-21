import YangMills.Construction.Matrices.GroupsOfFactsOfHarmonicAnalysisOnG
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpinHarmonics
def SpinRepsUnitaryIrreducible.Statement : Prop :=
  ∀ j k : HalfNatural, SpinRepFacts j k
end YangMills.Construction.SpinHarmonics
