import YangMills.Construction.Continuum.FunctionalsOnSeparatedTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TestSpaces
def UncentringFormula : Prop :=
  ∀ (σ : SepTuple → ℝ) (κ : ℝ), IsSepFunctional σ →
    (∀ X : SepTupleOfCard 1, cumulant σ X = κ * ∫ u, X.1 0 u) →
      (∀ n : ℕ, 1 ≤ n → ∀ X : SepTupleOfCard n,
        σ ⟨n, X⟩ = ∑ A : Finset (Fin n),
          (∏ i ∈ A, (κ * ∫ u, X.1 i u)) * centredPart σ ⟨Aᶜ.card, sepRestrict X Aᶜ⟩) ∧
      centredPart σ sepTupleNil = 1 ∧ ∀ X : SepTupleOfCard 1, centredPart σ ⟨1, X⟩ = 0
end YangMills.Construction.TestSpaces
