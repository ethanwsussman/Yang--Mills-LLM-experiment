import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
def AveragesGaugeCovariant : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j ≤ k →
    ∀ U ∈ smallIterateFields L k, ∀ u ∈ gaugeGroupAt L k 0,
      gaugeAct u U ∈ smallIterateFields L k →
      (∀ f : Vertex L k 0 → Matrices.ComplexMatrix2,
        (∀ x, f x ∈ Matrices.ComplexMatrix2.traceless) →
        covDiff (gaugeAct u U) (adjointVertexFn u f) =
          adjointForm u (covDiff U f) ∧
        iterAdjointCubeAverage L k (gaugeAct u U) j (adjointVertexFn u f) =
          adjointVertexFn (restrictVertexFunction (Tower.meshAt L k j) u)
            (iterAdjointCubeAverage L k U j f)) ∧
      ∀ B ∈ complexEdgeForms (Tower.meshAt L k 0),
        complexIterDeriv L k j (gaugeAct u U) (adjointForm u B) =
          adjointForm (restrictVertexFunction (Tower.meshAt L k j) u)
            (complexIterDeriv L k j U B) ∧
        iterCovariantDeriv L k (gaugeAct u U) j (adjointForm u B) =
          adjointForm (restrictVertexFunction (Tower.meshAt L k j) u)
            (iterCovariantDeriv L k U j B) ∧
        iterContourLogDrift L k (gaugeAct u U) j (adjointForm u B) =
          adjointVertexFn (restrictVertexFunction (Tower.meshAt L k j) u)
            (iterContourLogDrift L k U j B)
end YangMills.Construction.Tower.FullSpace
end
