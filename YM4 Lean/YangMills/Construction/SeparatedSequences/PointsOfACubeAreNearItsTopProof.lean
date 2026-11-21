import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.SeparatedSequences.PartitionsCubesExpansionsAndTheTriangleInequalityProof
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction
open TorusMetric PeriodicLattice PeriodicLattice.DirichletOperators
namespace SeparatedClasses.ApexProximity
theorem torusSupNorm_eq_norm {S : ℝ} (x : Torus4 S) : torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
theorem continuous_torusProj (S : ℝ) : Continuous (torusProj S) := by apply _root_.YangMills.Construction.TestPairs.continuous_torusProj <;> assumption
theorem torusProj_add (S : ℝ) (u v : Fin 4 → ℝ) :
    torusProj S (u + v) = torusProj S u + torusProj S v := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_add <;> assumption
end SeparatedClasses.ApexProximity
end YangMills.Construction
end
