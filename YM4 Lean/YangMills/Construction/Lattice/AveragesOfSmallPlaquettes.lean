import YangMills.Construction.Lattice.OneStepPlaquetteGrowth
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def smallCurvatureThreshold (L : ℕ) : ℝ :=
  min (curvatureGrowthRadius L / 2) ((L : ℝ) ^ 2 / (4 * curvatureGrowthConst L))
variable {L m K : ℕ}
def squaredLevelMesh (L k n : ℕ) : ℝ := ((L : ℝ) ^ n * finestMeshInLevelUnits L k) ^ 2
def FinestCurvatureSmallOn (k : ℕ) (a : ℝ) (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2)
    (X : Set (FourTorus L m)) : Prop :=
  ∀ p ∈ (plaquettesInside X : Set (PlaquetteAtLevel L m K 0)),
    Matrices.ComplexMatrix2.operatorNorm (plaquetteHolonomy U p - 1) ≤
      a * finestMeshInLevelUnits L k ^ 2
end YangMills.Construction.PeriodicLattice
