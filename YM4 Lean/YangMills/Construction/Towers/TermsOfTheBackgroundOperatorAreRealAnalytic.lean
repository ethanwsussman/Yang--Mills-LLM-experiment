import YangMills.Construction.Towers.ExpansionOfTheIterateInTheLeftChart
import YangMills.Construction.Towers.TermOfTheSecondOrderAndCommutatorTerm
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower
def BackgroundTermsAnalytic : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    ∃ V : Set (Edge L n k 0 → Matrices.ComplexMatrix2), IsOpenNhdOfOne V ∧
      (∀ B B' : edgeFormSpace L n k 0, IsAnalyticFieldFunction V fun U =>
        leftSecondDeriv (plaquetteAction L n k) U B B') ∧
      (∀ (B B' : edgeFormSpace L n k 0) (c : PositiveEdge L n k k)
          (φ : Matrices.ComplexMatrix2 →ₗ[ℝ] ℝ),
        IsAnalyticFieldFunction V fun U => φ (iterQuadraticTerm U B B' c)) ∧
      (∀ (l : vertexFunctionSpace L n k 0) (B : edgeFormSpace L n k 0) (e : Edge L n k 0)
          (φ : Matrices.ComplexMatrix2 →ₗ[ℝ] ℝ),
        IsAnalyticFieldFunction V fun U =>
          φ (bracketTerm U (l : Vertex L n k 0 → Matrices.ComplexMatrix2)
            (B : Edge L n k 0 → Matrices.ComplexMatrix2) e)) ∧
      ∀ (l : vertexFunctionSpace L n k 0) (e : Edge L n k 0)
          (φ : Matrices.ComplexMatrix2 →ₗ[ℝ] ℝ),
        IsAnalyticFieldFunction V fun U =>
          φ (covDiff U (l : Vertex L n k 0 → Matrices.ComplexMatrix2) e)
end YangMills.Construction.Tower
