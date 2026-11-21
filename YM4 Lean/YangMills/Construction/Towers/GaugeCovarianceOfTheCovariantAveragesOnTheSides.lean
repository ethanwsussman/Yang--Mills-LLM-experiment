import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
def AveragesGaugeCovariant : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k j : ℕ, 0 < n → j ≤ k →
    ∀ U ∈ smallIterateFields L n k, ∀ u ∈ gaugeGroupAt L n k 0,
      PeriodicLattice.gaugeTransform u U ∈ smallIterateFields L n k →
      (∀ f : Vertex L n k 0 → Matrices.ComplexMatrix2,
        (∀ x, f x ∈ Matrices.ComplexMatrix2.traceless) →
        covDiff (PeriodicLattice.gaugeTransform u U) (adjointVertexFn u f) =
          adjointForm u (covDiff U f) ∧
        iterAdjointCubeAverage L n k (PeriodicLattice.gaugeTransform u U) j (adjointVertexFn u f) =
          adjointVertexFn (restrictVertexFunction j u) (iterAdjointCubeAverage L n k U j f)) ∧
      ∀ B ∈ complexEdgeForms L n k 0,
        complexIterDeriv L n k j (PeriodicLattice.gaugeTransform u U) (adjointForm u B) =
          adjointForm (restrictVertexFunction j u) (complexIterDeriv L n k j U B) ∧
        iterCovariantDeriv L n k (PeriodicLattice.gaugeTransform u U) j (adjointForm u B) =
          adjointForm (restrictVertexFunction j u) (iterCovariantDeriv L n k U j B) ∧
        iterContourLogDrift L n k (PeriodicLattice.gaugeTransform u U) j (adjointForm u B) =
          adjointVertexFn (restrictVertexFunction j u) (iterContourLogDrift L n k U j B)
end Tower
end YangMills.Construction
end
