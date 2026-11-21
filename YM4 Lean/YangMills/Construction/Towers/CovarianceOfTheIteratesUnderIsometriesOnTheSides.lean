import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower
def IteratesIsometryCovariant : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k j : ℕ, 0 < n → j ≤ k →
    ∀ f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n, IsDistancePreserving f →
      MapsSublatticeOnto k k f →
      ∀ U ∈ smallIterateFields L n k,
        (∀ l : Vertex L n k 0 → Matrices.ComplexMatrix2,
          (∀ x, l x ∈ Matrices.ComplexMatrix2.traceless) →
          covDiff (pushField f U) (pushSiteFunction f l) =
            isometryOnTangent f U (covDiff U l) ∧
          iterAdjointCubeAverage L n k (pushField f U) j (pushSiteFunction f l) =
            pushSiteFunction f (iterAdjointCubeAverage L n k U j l)) ∧
        ∀ B ∈ complexEdgeForms L n k 0,
          complexIterDeriv L n k j (pushField f U) (isometryOnTangent f U B) =
            isometryOnTangent f (PeriodicLattice.complexBlockFieldAtLevel j U)
              (complexIterDeriv L n k j U B) ∧
          iterCovariantDeriv L n k (pushField f U) j (isometryOnTangent f U B) =
            isometryOnTangent f (PeriodicLattice.complexBlockFieldAtLevel j U)
              (iterCovariantDeriv L n k U j B) ∧
          iterContourLogDrift L n k (pushField f U) j (isometryOnTangent f U B) =
            pushSiteFunction f (iterContourLogDrift L n k U j B)
end YangMills.Construction.Tower
end
