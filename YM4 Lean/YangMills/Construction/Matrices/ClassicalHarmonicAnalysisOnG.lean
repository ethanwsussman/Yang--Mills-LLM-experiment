import YangMills.Construction.Matrices.GroupsOfFactsOfHarmonicAnalysisOnG
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpinHarmonics
def HarmonicAnalysisFacts : Prop :=
  ∀ l m : HalfNatural,
    SpinRepFacts l m ∧ PeterWeylFacts l m ∧ SpinCharacterFacts l ∧ WeylIntegralFormula ∧
      CoeffProjectionFacts l m ∧ ClebschGordanFacts l ∧ RightFieldFacts l ∧
      ConjInvariantKernelFormula l
end YangMills.Construction.SpinHarmonics
end
