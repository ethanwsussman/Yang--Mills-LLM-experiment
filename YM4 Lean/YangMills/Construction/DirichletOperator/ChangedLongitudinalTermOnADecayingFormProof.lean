import YangMills.Construction.DirichletOperator.CornerBoundsOnTheToriOfTheCubesProof
import YangMills.Construction.DirichletOperator.ApproximateInverseAndLocalDefectsProof
import YangMills.Construction.DirichletOperator.ChangedLongitudinalSourceAtTheCellsOfACubeProof
import YangMills.Construction.DirichletOperator.FormDecayingFromAPointOfACube
import YangMills.Construction.DirichletOperator.PropagatorBoundsForSourcesInFormsProof
import YangMills.Construction.DirichletOperator.WeightedDistanceInACubeProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes
namespace PartitionCubes.LongChangeDecay
theorem supNorm_zero_nonpos {S : ℝ} : supNorm (0 : PeriodicTorus 4 S) ≤ 0 := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.supNorm_zero_le <;> assumption
theorem lOneNorm_sub_comm {S : ℝ} (p q : PeriodicTorus 4 S) :
    lOneNorm (p - q) = lOneNorm (q - p) := by apply _root_.YangMills.Construction.PartitionCubes.TorusTransfer.lOneNorm_sub_comm <;> assumption
theorem scaleSpacing_pos (R : NestedRegions) (n : ℤ) : 0 < scaleSpacing R.L R.ξ n := by apply _root_.YangMills.Construction.PartitionCubes.FirstTypeMaps.scaleSpacing_pos <;> assumption
theorem scale_pos (R : NestedRegions) (n : ℕ) : 0 < R.scale n := scaleSpacing_pos R n
theorem finite_fineBond (R : NestedRegions) : Finite R.FineBond := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.finite_fineBond <;> assumption
section Norms
variable {R : NestedRegions}
theorem supBond_nonneg (f : R.FineBond → ℝ) : 0 ≤ supBond f := by apply _root_.YangMills.Construction.CornerGreen.supBond_nonneg' <;> assumption
theorem norm_le_supBond (f : R.FineBond → ℝ) (b : R.FineBond) : ‖f b‖ ≤ supBond f := by apply _root_.YangMills.Construction.ApproxInverseBounds.le_supBond <;> assumption
def toEuclidean (A : R.FineBond → ℝ) : EuclideanSpace ℝ R.FineBond :=
  WithLp.toLp 2 fun b => R.ξ ^ 2 * A b
theorem toEuclidean_add [Fintype R.FineBond] (f g : R.FineBond → ℝ) :
    toEuclidean (f + g) = toEuclidean f + toEuclidean g := by
  ext b
  simp [toEuclidean, mul_add]
end Norms
variable {R : NestedRegions} {M : ℕ}
theorem lOneNorm_nonneg {S : ℝ} (p : PeriodicTorus 4 S) : 0 ≤ lOneNorm p := by apply _root_.YangMills.Construction.PartitionCubes.WeightedDistCube.lOneNorm_nonneg' <;> assumption
theorem torusDist_nonneg (Q : LevelCube R M) (o o' : Q.system.setting.Point) :
    0 ≤ Q.torusDist o o' :=
  mul_nonneg (inv_nonneg.mpr (scale_pos R _).le) (lOneNorm_nonneg _)
theorem subset_thickened (Q : LevelCube R M) (X : Set Q.system.setting.Point) :
    X ⊆ Q.thickened X := by
  intro x hx
  show supSetDist {x} X ≤ _
  refine le_trans (iInf₂_le _ (mem_singleton x)) (le_trans (iInf₂_le _ hx) ?_)
  refine ENNReal.ofReal_le_ofReal ?_
  rw [sub_self]
  exact le_trans supNorm_zero_nonpos (mul_nonneg (by norm_num) (scale_pos R _).le)
theorem thicken_mono (Q : LevelCube R M) {a b : ℝ} (hab : a ≤ b) :
    Q.thicken a ⊆ Q.thicken b := by apply _root_.YangMills.Construction.CubeAdjointDefect.LongChangeAtCells.thicken_mono' <;> assumption
theorem weightedDist_nonneg (y y' : R.Point) : 0 ≤ R.weightedDist y y' := by apply _root_.YangMills.Construction.DivSourceEstimate.weightedDist_nonneg <;> assumption
end PartitionCubes.LongChangeDecay
end YangMills.Construction
