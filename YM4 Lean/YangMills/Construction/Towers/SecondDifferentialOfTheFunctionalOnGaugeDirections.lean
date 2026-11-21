import YangMills.Construction.Towers.TheFieldsAndTheTwoOperatorFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def HessianVanishesOnGaugeDirections : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    ∀ l ∈ vertexFunctionSpace L n k 0, ∀ g : edgeFormSpace L n k 0,
      (g : Edge L n k 0 → Matrices.ComplexMatrix2) = vertexCoboundary l →
        ∀ ζ : RealPeriodicField L n k,
          fieldFunctionalSecondDeriv L n k (g, 0, 0) ζ = 0
end YangMills.Construction.Tower
end
