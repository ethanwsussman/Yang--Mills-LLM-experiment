import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.DilationOfATower
import YangMills.Construction.Towers.FamiliesOfCriticalBranches
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open YangMills.Construction.Matrices (ComplexMatrix2)
namespace HessianScaling
def Statement : Prop :=
  ∀ (L n k j : ℕ) (hpos : 0 < L) (hle : j ≤ k), Conventions.IsAdmissibleBlockingFactor L → 0 < n →
    ∀ l ≤ j, ∀ (U M : Set (Edge L n k l → ComplexMatrix2)) (F : (Edge L n k l → ComplexMatrix2) → ℝ)
      (G : (Edge L (scaledExponent n k j) j l → ComplexMatrix2) → ℝ),
      IsAnalyticFieldFunction U F → IsFieldSubmanifold M → M ⊆ U →
      (∀ A ∈ M, G (transportTotal (scaleEdge hpos hle l) A) = F A) →
      ∀ x, (fieldCurveData L n k l).IsCriticalOn M F x → HasPosDefHessian M F x →
        HasPosDefHessian (transportTotal (scaleEdge hpos hle l) '' M) G
          (transportTotal (scaleEdge hpos hle l) x)
end HessianScaling
end YangMills.Construction.Tower
end
