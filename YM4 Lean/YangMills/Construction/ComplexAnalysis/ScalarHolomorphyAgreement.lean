import YangMills.Construction.ComplexAnalysis.BanachValuedHolomorphy
import Mathlib
noncomputable section
namespace YangMills.Construction.BanachValued.ScalarAgreement
open YangMills.Construction.Coordinates
def Agreement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (O : Set (ComplexCoordinates n)), IsOpen O →
    ∀ f : ComplexCoordinates n → ℂ,
      ComplexCoordinates.IsHolomorphicIn O ((Equiv.funUnique (Fin 1) ℂ).symm ∘ f) ↔
        IsHolomorphicOnOpen O f
end YangMills.Construction.BanachValued.ScalarAgreement
