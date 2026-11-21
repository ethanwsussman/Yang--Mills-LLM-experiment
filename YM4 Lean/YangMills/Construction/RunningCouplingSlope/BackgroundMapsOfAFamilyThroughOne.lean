import YangMills.Construction.RunningCouplingSlope.FamiliesThroughOne
import YangMills.Construction.RunningCouplingSlope.GaussianNumbersOfTheSoftChain
import Mathlib
open Filter
open scoped Topology Matrix.Norms.L2Operator
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def GaugeMapsAnalyticAlongFamily : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (X : E → ChainPoint L n k) (p₀ : E),
      IsAnalyticFamilyThroughUnit X p₀ →
      (∀ (B : Tower.edgeFormSpace L n k 0) (x : Tower.Vertex L n k 0), AnalyticAt ℝ
        (fun p => (Tower.gaugeSliceResidual (X p).fine B : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2) x) p₀) ∧
      ∀ y : Tower.vertexFunctionSpace L n k 0 × Tower.vertexFunctionSpace L n k k,
        (∀ x : Tower.Vertex L n k 0, AnalyticAt ℝ
          (fun p => ((ghostBlockOperator (X p) y).1 : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2) x) p₀) ∧
        ∀ x : Tower.Vertex L n k k, AnalyticAt ℝ
          (fun p => ((ghostBlockOperator (X p) y).2 : Tower.Vertex L n k k → Matrices.ComplexMatrix2) x) p₀
end YangMills.Construction.RunningCouplingSlope
end
