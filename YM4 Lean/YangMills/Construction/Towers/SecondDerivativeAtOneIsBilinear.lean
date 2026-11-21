import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
def LeftSecondDerivAtIdentityBilinear : Prop :=
  ∀ L n k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → j ≤ k →
    ∀ (U : Set (Edge L n k j → Matrices.ComplexMatrix2))
      (G : (Edge L n k j → Matrices.ComplexMatrix2) → ℝ),
      IsOpenNhdOfOne U → IsAnalyticFieldFunction U G →
        (∀ X ∈ edgeFormSpace L n k j, ∀ Y ∈ edgeFormSpace L n k j,
          leftSecondDeriv G (trivialField L n k j) X Y =
            leftSecondDeriv G (trivialField L n k j) Y X) ∧
        ∀ X₁ ∈ edgeFormSpace L n k j, ∀ X₂ ∈ edgeFormSpace L n k j,
          ∀ Y ∈ edgeFormSpace L n k j, ∀ c : ℝ,
          leftSecondDeriv G (trivialField L n k j) (c • X₁ + X₂) Y =
            c * leftSecondDeriv G (trivialField L n k j) X₁ Y +
              leftSecondDeriv G (trivialField L n k j) X₂ Y
end Tower
end YangMills.Construction
end
