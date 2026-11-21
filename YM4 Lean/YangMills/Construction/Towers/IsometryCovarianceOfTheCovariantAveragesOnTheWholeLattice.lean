import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices
namespace Tower.FullSpace
def CovariantSmoothingIsometryEquivariance : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j ≤ k →
    ∀ f : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace, IsDistancePreserving f →
      MapsSublatticeOnto (meshAt L k k) f → ∀ U ∈ smallIterateFields L k,
        (∀ l : Vertex L k 0 → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.traceless) →
          covDiff (pushField f U) (pushSiteFunction f l) =
            isometryOnTangent f U (covDiff U l) ∧
          iterAdjointCubeAverage L k (pushField f U) j (pushSiteFunction f l) =
            pushSiteFunction f (iterAdjointCubeAverage L k U j l)) ∧
        ∀ B ∈ complexEdgeForms (meshAt L k 0),
          complexIterDeriv L k j (pushField f U) (isometryOnTangent f U B) =
            isometryOnTangent f (complexIter L k j U)
              (complexIterDeriv L k j U B) ∧
          iterCovariantDeriv L k (pushField f U) j (isometryOnTangent f U B) =
            isometryOnTangent f (complexIter L k j U)
              (iterCovariantDeriv L k U j B) ∧
          iterContourLogDrift L k (pushField f U) j (isometryOnTangent f U B) =
            pushSiteFunction f (iterContourLogDrift L k U j B)
end Tower.FullSpace
end YangMills.Construction
end
