import YangMills.Construction.Matrices.GroupsOfFactsOfHarmonicAnalysisOnG
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpinHarmonics
def AllConjInvariantKernels : Prop :=
  ∀ l : HalfNatural, ConjInvariantKernelFormula l
end YangMills.Construction.SpinHarmonics
end
