import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def LeftSecondDerivBilinear : Prop :=
  ∀ L n k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → j ≤ k →
    ∀ (U : Set (Edge L n k j → Matrices.ComplexMatrix2))
      (F : (Edge L n k j → Matrices.ComplexMatrix2) → ℝ),
      IsAnalyticFieldFunction U F → ∀ V ∈ U,
        (∀ X ∈ edgeFormSpace L n k j, ∀ Y ∈ edgeFormSpace L n k j,
          leftSecondDeriv F V X Y = leftSecondDeriv F V Y X) ∧
        ∀ X₁ ∈ edgeFormSpace L n k j, ∀ X₂ ∈ edgeFormSpace L n k j,
          ∀ Y ∈ edgeFormSpace L n k j, ∀ c : ℝ,
          leftSecondDeriv F V (c • X₁ + X₂) Y =
            c * leftSecondDeriv F V X₁ Y + leftSecondDeriv F V X₂ Y
end YangMills.Construction.Tower
end
