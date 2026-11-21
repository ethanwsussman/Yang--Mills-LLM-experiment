import YangMills.Construction.DirichletOperator.DifferenceOperatorsAgreeOnTheLocalTorusProof
import YangMills.Construction.DirichletOperator.LengthsOnACubeOfTheFirstKind
import YangMills.Construction.PartitionCubes.SmoothedIndicatorDerivBoundsProof
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
namespace YangMills.Construction.PartitionCubes.FirstTypeCubeNorms
variable {S : ℝ}
theorem torusProj_sub (p p' : Fin 4 → ℝ) :
    torusProj 4 S p - torusProj 4 S p' = torusProj 4 S (p - p') := by apply _root_.YangMills.Construction.PartitionCubes.SmoothedIndicatorBounds.torusProj_sub <;> assumption
theorem addCircle_norm_coe_le (x : ℝ) : ‖(x : AddCircle S)‖ ≤ |x| := by apply _root_.YangMills.Construction.TorusMetric.addCircle_norm_coe_le_abs <;> assumption
theorem supNorm_torusProj_le (x : Fin 4 → ℝ) : supNorm (torusProj 4 S x) ≤ ‖x‖ := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.supNorm_proj_le <;> assumption
end YangMills.Construction.PartitionCubes.FirstTypeCubeNorms
