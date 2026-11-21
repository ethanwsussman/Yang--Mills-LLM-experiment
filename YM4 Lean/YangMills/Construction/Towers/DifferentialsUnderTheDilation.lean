import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.DilationOfATower
import YangMills.Construction.Towers.TheLeftChart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def ScalingTransportsDerivatives : Prop :=
  ∀ (L n k j : ℕ) (hL : 0 < L) (hj : j ≤ k), Conventions.IsAdmissibleBlockingFactor L → 0 < n →
    ∀ a ≤ j, ∀ b ≤ j,
      (∀ (f : (Edge L n k a → Matrices.ComplexMatrix2) → Edge L n k b → Matrices.ComplexMatrix2)
        (f' : (Edge L (scaledExponent n k j) j a → Matrices.ComplexMatrix2) →
          Edge L (scaledExponent n k j) j b → Matrices.ComplexMatrix2),
        (∀ A ∈ fieldSpace L n k a, f' (transportTotal (scaleEdge hL hj a) A) =
          transportTotal (scaleEdge hL hj b) (f A)) →
        ∀ U ∈ fieldSpace L n k a, ∀ X ∈ edgeFormSpace L n k a,
          leftDifferential f' (transportTotal (scaleEdge hL hj a) U)
              (transportTotal (scaleEdge hL hj a) X) =
            transportTotal (scaleEdge hL hj b) (leftDifferential f U X)) ∧
      ∀ (F : (Edge L n k a → Matrices.ComplexMatrix2) → ℝ)
        (F' : (Edge L (scaledExponent n k j) j a → Matrices.ComplexMatrix2) → ℝ),
        (∀ A ∈ fieldSpace L n k a, F' (transportTotal (scaleEdge hL hj a) A) = F A) →
        ∀ U ∈ fieldSpace L n k a, ∀ X ∈ edgeFormSpace L n k a, ∀ Y ∈ edgeFormSpace L n k a,
          leftSecondDeriv F' (transportTotal (scaleEdge hL hj a) U)
              (transportTotal (scaleEdge hL hj a) X)
              (transportTotal (scaleEdge hL hj a) Y) =
            leftSecondDeriv F U X Y
end YangMills.Construction.Tower
end
