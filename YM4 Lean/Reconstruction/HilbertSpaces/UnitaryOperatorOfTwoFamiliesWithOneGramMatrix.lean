import YangMills.Construction.HilbertSpaces.FormsOperatorsAndFamiliesInAHilbertSpace
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.GramUnitary
open FormsOperators
def Claim : Prop :=
  ∀ {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    {ι : Type} (u : ι → H) (v : ι → H'), (∀ i j, ⟪u i, u j⟫_ℂ = ⟪v i, v j⟫_ℂ) →
    Dense (Submodule.span ℂ (Set.range u) : Set H) →
    Dense (Submodule.span ℂ (Set.range v) : Set H') →
    ∃ W : UnitaryMap H H', ∀ i, W (u i) = v i
end YangMills.Construction.GramUnitary
end
