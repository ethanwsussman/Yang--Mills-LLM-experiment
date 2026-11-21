import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.LinearMapsAtTheTrivialConfiguration
import YangMills.Construction.Towers.TheLeftChart
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.OneStepComplexForms
structure OneStepProperties (L k i : ℕ) : Prop where
  linearSmoothing_sub : ∀ A ∈ complexEdgeForms (meshAt L k i),
    ∀ A' ∈ complexEdgeForms (meshAt L k i),
      linearSmoothing (a := meshAt L k (i + 1)) L (A - A') =
        linearSmoothing (a := meshAt L k (i + 1)) L A -
          linearSmoothing (a := meshAt L k (i + 1)) L A'
  linearSmoothing_mapsTo : MapsTo (linearSmoothing (a := meshAt L k (i + 1)) (a' := meshAt L k i) L)
    (complexEdgeForms (meshAt L k i)) (complexEdgeForms (meshAt L k (i + 1)))
  crossingSmoothing_mapsTo : MapsTo (crossingSmoothing (a := meshAt L k (i + 1)) (a' := meshAt L k i) L)
    (complexEdgeForms (meshAt L k i)) (complexEdgeForms (meshAt L k (i + 1)))
  linearSmoothing_mapsTo_real : MapsTo (linearSmoothing (a := meshAt L k (i + 1)) (a' := meshAt L k i) L)
    (edgeFormSpace (meshAt L k i)) (edgeFormSpace (meshAt L k (i + 1)))
  crossingSmoothing_mapsTo_real : MapsTo (crossingSmoothing (a := meshAt L k (i + 1)) (a' := meshAt L k i) L)
    (edgeFormSpace (meshAt L k i)) (edgeFormSpace (meshAt L k (i + 1)))
  cubeContourAverage_mapsTo : MapsTo (cubeContourAverage (a := meshAt L k (i + 1)) (a' := meshAt L k i) L)
    (complexEdgeForms (meshAt L k i))
    (Matrices.GroupLieProduct.tracelessFunctions (Vertex L k (i + 1)))
  vertexSmoothing_mapsTo : MapsTo (vertexSmoothing (a := meshAt L k (i + 1)) (a' := meshAt L k i) L)
    (Matrices.GroupLieProduct.tracelessFunctions (Vertex L k i))
    (Matrices.GroupLieProduct.tracelessFunctions (Vertex L k (i + 1)))
  linearSmoothing_eq : ∀ A ∈ complexEdgeForms (meshAt L k i),
    linearSmoothing (a := meshAt L k (i + 1)) L A =
      crossingSmoothing (a := meshAt L k (i + 1)) L A - vertexCoboundary
        (cubeContourAverage (a := meshAt L k (i + 1)) L A)
  linearSmoothing_coboundary : ∀ g ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L k i),
    linearSmoothing (a := meshAt L k (i + 1)) L (vertexCoboundary g) =
      vertexCoboundary (restrictVertexFunction (meshAt L k (i + 1)) g)
  crossingSmoothing_coboundary : ∀ g ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L k i),
    crossingSmoothing (a := meshAt L k (i + 1)) L (vertexCoboundary g) =
      vertexCoboundary (vertexSmoothing (a := meshAt L k (i + 1)) L g)
  cubeContourAverage_coboundary : ∀ g ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L k i),
    cubeContourAverage (a := meshAt L k (i + 1)) L (vertexCoboundary g) =
      vertexSmoothing (a := meshAt L k (i + 1)) L g - restrictVertexFunction (meshAt L k (i + 1)) g
  of_constant : ∀ A ∈ complexEdgeForms (meshAt L k i), ∀ c : Fin 4 → Matrices.ComplexMatrix2,
    (∀ (x : Vertex L k i) (μ : Fin 4), A (InfiniteLattice.Link.forwardFrom x μ) = c μ) →
      cubeContourAverage (a := meshAt L k (i + 1)) L A = 0 ∧
      linearSmoothing (a := meshAt L k (i + 1)) L A =
        crossingSmoothing (a := meshAt L k (i + 1)) L A ∧
      ∀ (x : Vertex L k (i + 1)) (μ : Fin 4),
        crossingSmoothing (a := meshAt L k (i + 1)) L A (InfiniteLattice.Link.forwardFrom x μ) =
          (L : ℂ) • c μ
  linearSmoothing_surjOn : SurjOn (linearSmoothing (a := meshAt L k (i + 1)) (a' := meshAt L k i) L)
    (complexEdgeForms (meshAt L k i)) (complexEdgeForms (meshAt L k (i + 1)))
  crossingSmoothing_surjOn : SurjOn (crossingSmoothing (a := meshAt L k (i + 1)) (a' := meshAt L k i) L)
    (complexEdgeForms (meshAt L k i)) (complexEdgeForms (meshAt L k (i + 1)))
  linearSmoothing_surjOn_real : SurjOn (linearSmoothing (a := meshAt L k (i + 1)) (a' := meshAt L k i) L)
    (edgeFormSpace (meshAt L k i)) (edgeFormSpace (meshAt L k (i + 1)))
  crossingSmoothing_surjOn_real : SurjOn (crossingSmoothing (a := meshAt L k (i + 1)) (a' := meshAt L k i) L)
    (edgeFormSpace (meshAt L k i)) (edgeFormSpace (meshAt L k (i + 1)))
  maxOperatorNorm_cubeContourAverage_le : ∀ A ∈ complexEdgeForms (meshAt L k i),
    maxOperatorNorm (cubeContourAverage (a := meshAt L k (i + 1)) L A) ≤
      2 * ((L : ℝ≥0∞) - 1) * maxOperatorNorm A
def OneStepClaim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k i : ℕ, i + 1 ≤ k → OneStepProperties L k i
end YangMills.Construction.Tower.FullSpace.OneStepComplexForms
end
