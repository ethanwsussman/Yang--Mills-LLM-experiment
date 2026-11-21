import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.LinearMapsAtTheTrivialConfiguration
import YangMills.Construction.Towers.TheLeftChart
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace PeriodicCoarseningStep
structure StepProperties (L m k i : ℕ) : Prop where
  linearSmoothing_sub : ∀ A ∈ complexEdgeForms L m k i, ∀ A' ∈ complexEdgeForms L m k i,
    linearSmoothing L m k i (A - A') = linearSmoothing L m k i A - linearSmoothing L m k i A'
  linearSmoothing_mapsTo : MapsTo (linearSmoothing L m k i) (complexEdgeForms L m k i)
    (complexEdgeForms L m k (i + 1))
  crossingSmoothing_mapsTo : MapsTo (crossingSmoothing L m k i) (complexEdgeForms L m k i)
    (complexEdgeForms L m k (i + 1))
  linearSmoothing_mapsTo_real : MapsTo (linearSmoothing L m k i) (edgeFormSpace L m k i)
    (edgeFormSpace L m k (i + 1))
  crossingSmoothing_mapsTo_real : MapsTo (crossingSmoothing L m k i) (edgeFormSpace L m k i)
    (edgeFormSpace L m k (i + 1))
  cubeContourAverage_mapsTo : MapsTo (cubeContourAverage L m k i) (complexEdgeForms L m k i)
    (Matrices.GroupLieProduct.tracelessFunctions (Vertex L m k (i + 1)))
  vertexSmoothing_mapsTo : MapsTo (vertexSmoothing L m k i)
    (Matrices.GroupLieProduct.tracelessFunctions (Vertex L m k i))
    (Matrices.GroupLieProduct.tracelessFunctions (Vertex L m k (i + 1)))
  linearSmoothing_eq : ∀ A ∈ complexEdgeForms L m k i,
    linearSmoothing L m k i A =
      crossingSmoothing L m k i A - vertexCoboundary (cubeContourAverage L m k i A)
  linearSmoothing_vertexCoboundary :
    ∀ g ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L m k i),
      linearSmoothing L m k i (vertexCoboundary g) =
        vertexCoboundary (restrictVertexFunction (i + 1) g)
  crossingSmoothing_vertexCoboundary :
    ∀ g ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L m k i),
      crossingSmoothing L m k i (vertexCoboundary g) =
        vertexCoboundary (vertexSmoothing L m k i g)
  cubeContourAverage_vertexCoboundary :
    ∀ g ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L m k i),
      cubeContourAverage L m k i (vertexCoboundary g) =
        vertexSmoothing L m k i g - restrictVertexFunction (i + 1) g
  of_constant : ∀ A ∈ complexEdgeForms L m k i, ∀ c : Fin 4 → Matrices.ComplexMatrix2,
    (∀ (v : Vertex L m k i) (α : Fin 4), A (PeriodicLattice.Bond.forwardFrom v α) = c α) →
      cubeContourAverage L m k i A = 0 ∧
      linearSmoothing L m k i A = crossingSmoothing L m k i A ∧
      ∀ (v : Vertex L m k (i + 1)) (α : Fin 4),
        crossingSmoothing L m k i A (PeriodicLattice.Bond.forwardFrom v α) = (L : ℂ) • c α
  linearSmoothing_surjOn : SurjOn (linearSmoothing L m k i) (complexEdgeForms L m k i)
    (complexEdgeForms L m k (i + 1))
  crossingSmoothing_surjOn : SurjOn (crossingSmoothing L m k i) (complexEdgeForms L m k i)
    (complexEdgeForms L m k (i + 1))
  linearSmoothing_surjOn_real : SurjOn (linearSmoothing L m k i) (edgeFormSpace L m k i)
    (edgeFormSpace L m k (i + 1))
  crossingSmoothing_surjOn_real : SurjOn (crossingSmoothing L m k i) (edgeFormSpace L m k i)
    (edgeFormSpace L m k (i + 1))
  maxOperatorNorm_cubeContourAverage_le : ∀ A ∈ complexEdgeForms L m k i,
    maxOperatorNorm (cubeContourAverage L m k i A) ≤ 2 * ((L : ℝ≥0∞) - 1) * maxOperatorNorm A
def Holds : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m k i : ℕ, 0 < m → i + 1 ≤ k →
    StepProperties L m k i
end PeriodicCoarseningStep
end Tower
end YangMills.Construction
end
