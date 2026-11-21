import YangMills.Construction.Matrices.PropertiesOfFunctionsOfSeveralVariablesOnTheGroup
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.SpinHarmonics
def TensorOneDisjointCommuteForAll : Prop :=
  ∀ (J : Type) [Finite J] [Nonempty J] (B : Set J), B.Nonempty → B ≠ Set.univ →
    ∀ X : HaarL2 ↥B →L[ℂ] HaarL2 ↥B, SeveralVariables.TensorOneDisjointCommute B X
end YangMills.Construction.SpinHarmonics
end
