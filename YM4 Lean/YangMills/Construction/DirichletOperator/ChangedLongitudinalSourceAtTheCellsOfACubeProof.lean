import YangMills.Construction.DirichletOperator.CornerBoundsOnTheToriOfTheCubesProof
import YangMills.Construction.RegionSequence.GaugeProjectionsProof
import YangMills.Construction.DirichletOperator.BoundsOnTheApproximateInverseProof
import YangMills.Construction.DirichletOperator.MapsOfACubeOfTheFirstKindProof
import YangMills.Construction.DirichletOperator.PropagatorBoundsForDivergenceSourcesProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes
open YangMills.Construction.RemainderEstimates
noncomputable section
namespace YangMills.Construction.CubeAdjointDefect.LongChangeAtCells
theorem supNorm_zero_le {S : ℝ} : supNorm (0 : PeriodicTorus 4 S) ≤ 0 := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.supNorm_zero_le <;> assumption
theorem scaleSpacing_pos (𝒮 : NestedRegions) (n : ℤ) : 0 < scaleSpacing 𝒮.L 𝒮.ξ n := by apply _root_.YangMills.Construction.PartitionCubes.FirstTypeMaps.scaleSpacing_pos <;> assumption
theorem scale_pos (𝒮 : NestedRegions) (n : ℕ) : 0 < 𝒮.scale n := scaleSpacing_pos 𝒮 n
theorem finite_fineBond (𝒮 : NestedRegions) : Finite 𝒮.FineBond := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.finite_fineBond <;> assumption
theorem norm_le_supBond {𝒮 : NestedRegions} (f : 𝒮.FineBond → ℝ) (b : 𝒮.FineBond) :
    ‖f b‖ ≤ supBond f := by apply _root_.YangMills.Construction.ApproxInverseBounds.le_supBond <;> assumption
variable {𝒮 : NestedRegions} {M : ℕ}
theorem thicken_mono' (Q : LevelCube 𝒮 M) {a b : ℝ} (hab : a ≤ b) : Q.thicken a ⊆ Q.thicken b := by
  intro x hx
  refine le_trans hx (ENNReal.ofReal_le_ofReal ?_)
  refine mul_le_mul_of_nonneg_right hab ?_
  have hs := (scale_pos 𝒮 Q.level).le
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hs) (by positivity)
end YangMills.Construction.CubeAdjointDefect.LongChangeAtCells
