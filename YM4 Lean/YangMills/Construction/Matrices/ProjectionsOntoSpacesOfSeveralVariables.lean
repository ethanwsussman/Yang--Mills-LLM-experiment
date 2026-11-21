import YangMills.Construction.Matrices.PropertiesOfFunctionsOfSeveralVariablesOnTheGroup
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpinHarmonics
open MeasureTheory Matrices.ComplexMatrix2 HilbertSpaceBasics SeveralVariables
def IsotypicProjProperties : Prop :=
  ∀ (J : Type) [Finite J] [Nonempty J] (l : J → HalfNatural) (κ : HalfNatural),
    (∀ F : HaarL2 J, isotypicProj l F =
      ∑ α ∈ indicesWithSpins l, (inner ℂ (peterWeylVec α) F : ℂ) • peterWeylVec α) ∧
    IsOrthProjOnto (isotypicProj l) (prodCoeffSpanL2 l : Set _) ∧
    IsOrthProjOnto (truncationProj J κ) (truncatedCoeffSpanL2 J κ : Set _) ∧
    Pairwise fun l₁ l₂ : J → HalfNatural =>
      prodCoeffSpanL2 l₁ ⟂ prodCoeffSpanL2 l₂
end YangMills.Construction.SpinHarmonics
end
