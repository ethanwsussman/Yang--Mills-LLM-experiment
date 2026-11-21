import YangMills.Construction.Towers.TheFunctionalInTheBackgroundGauge
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower
open Matrices
def BackgroundDeterminantEntriesAnalytic : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    ∃ 𝒰 : Set (Edge L n k 0 → ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧
      (∀ (J X : edgeFormSpace L n k 0) (μ : edgeFormSpace L n k k), IsAnalyticFieldFunction 𝒰 fun U =>
        backgroundHessianForm U J μ X) ∧
      (∀ (X : edgeFormSpace L n k 0) (C : edgeFormSpace L n k k), IsAnalyticFieldFunction 𝒰 fun U =>
        (edgeFormPairing (C : Edge L n k k → ComplexMatrix2)
          (iterCovariantDerivLinear L n k U X : Edge L n k k → ComplexMatrix2)).re) ∧
      (∀ l l' : vertexFunctionSpace L n k 0, IsAnalyticFieldFunction 𝒰 fun U =>
        (traceFinsumPairing (l : Vertex L n k 0 → ComplexMatrix2)
          (covDiffRealTranspose L n k U (covDiffLinear L n k U l') :
            Vertex L n k 0 → ComplexMatrix2)).re) ∧
      ∀ (l : vertexFunctionSpace L n k 0) (g : vertexFunctionSpace L n k k),
        IsAnalyticFieldFunction 𝒰 fun U =>
          (traceFinsumPairing (g : Vertex L n k k → ComplexMatrix2)
            (iterAverageLinear L n k U l : Vertex L n k k → ComplexMatrix2)).re
end YangMills.Construction.Tower
