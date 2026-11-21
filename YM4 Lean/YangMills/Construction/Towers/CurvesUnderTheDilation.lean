import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.DilationOfATower
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def ScalingPreservesTangentsAndCriticalPoints : Prop :=
  ∀ (L n k j : ℕ) (hL : 0 < L) (hj : j ≤ k), Conventions.IsAdmissibleBlockingFactor L → 0 < n →
    ∀ l ≤ j, ∀ (S : Set (Edge L n k l → Matrices.ComplexMatrix2))
      (x : Edge L n k l → Matrices.ComplexMatrix2),
      (∀ A : Edge L n k l → Matrices.ComplexMatrix2, A ∈ (fieldCurveData L n k l).tangentSpan S x ↔
        transportTotal (scaleEdge hL hj l) A ∈
          (fieldCurveData L (scaledExponent n k j) j l).tangentSpan
            (transportTotal (scaleEdge hL hj l) '' S)
            (transportTotal (scaleEdge hL hj l) x)) ∧
      ∀ (F : (Edge L n k l → Matrices.ComplexMatrix2) → ℝ)
        (F' : (Edge L (scaledExponent n k j) j l → Matrices.ComplexMatrix2) → ℝ),
        (∀ V ∈ S, F' (transportTotal (scaleEdge hL hj l) V) = F V) →
        ((fieldCurveData L n k l).IsCriticalOn S F x ↔
          (fieldCurveData L (scaledExponent n k j) j l).IsCriticalOn
            (transportTotal (scaleEdge hL hj l) '' S) F'
            (transportTotal (scaleEdge hL hj l) x))
end YangMills.Construction.Tower
end
