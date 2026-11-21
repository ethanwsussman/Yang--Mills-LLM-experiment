import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ClusterExpansionOfAStep
open YangMills.Construction.StepSettings YangMills.Construction.TorusFields YangMills.Construction.TorusLumps
def CoarseFactorIsLocalStatement : Prop :=
  ∀ S : StepSetup, S.IsWellPosed →
    (∀ (n : ℕ) [NeZero n], IsBlockTorusSide S.params n → ∀ (V : TorusField n) (Y X : Finset (TorusSite n))
      (ω : Y → CoarseLabel S.labels.Ω S.params.side), 0 ≤ coarseFactorExpansion S n V Y ω X) ∧
    (∀ (n : ℕ) [NeZero n], IsBlockTorusSide S.params n →
      ∀ (V V' : TorusField n) (Y Y' X : Finset (TorusSite n))
      (ω : Y → CoarseLabel S.labels.Ω S.params.side)
      (ω' : Y' → CoarseLabel S.labels.Ω S.params.side), X ⊆ Y → X ⊆ Y' →
      (∀ b : TorusBond n, b.1 ∈ X → b.1 + unitStep n b.2 ∈ X → V b.1 b.2 = V' b.1 b.2) →
      (∀ z (hz : z ∈ Y) (hz' : z ∈ Y'), z ∈ X → ω ⟨z, hz⟩ = ω' ⟨z, hz'⟩) →
      coarseFactorExpansion S n V Y ω X = coarseFactorExpansion S n V' Y' ω' X) ∧
    (∀ (n n' : ℕ) [NeZero n] [NeZero n'], IsBlockTorusSide S.params n → IsBlockTorusSide S.params n' →
      ∀ (V : TorusField n) (V' : TorusField n') (Y : Finset (TorusSite n)) (Y' : Finset (TorusSite n'))
        (ω : Y → CoarseLabel S.labels.Ω S.params.side)
        (ω' : Y' → CoarseLabel S.labels.Ω S.params.side)
        (X : Finset (TorusSite n)) (X' : Finset (TorusSite n')) (y : TorusSite n) (y' : TorusSite n') (m : ℕ),
        2 * m + 2 < n → 2 * m + 2 < n' → X ⊆ Y → X' ⊆ Y' → SameBlockPosition S.params y y' →
        CongruentInBoxes X X' y y' m → FieldsAgreeOnSet V V' y y' m X → LabelsAgreeNear Y Y' ω ω' y y' m X →
        coarseFactorExpansion S n V Y ω X = coarseFactorExpansion S n' V' Y' ω' X')
end ClusterExpansionOfAStep
end YangMills.Construction
end
