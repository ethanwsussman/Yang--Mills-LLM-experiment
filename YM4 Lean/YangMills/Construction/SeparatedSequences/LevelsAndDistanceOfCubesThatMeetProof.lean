import YangMills.Construction.Lattice.CubesLayersAndTopsOfADecreasingSequence
import YangMills.Construction.SeparatedSequences.BoundOfTheDifferencesOfTheExtensionKernelAtATopAndAnExpansionProof
import YangMills.Construction.SeparatedSequences.LevelsAndDistanceOfCubesThatMeet
import YangMills.Construction.Weighted.LayerCutoffConstruction
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.SeparatedClasses
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.TorusMetric
namespace MeetingBlocks
theorem torusSupNorm_zero_le {S : ℝ} : torusSupNorm (0 : Torus4 S) ≤ 0 := by apply _root_.YangMills.Construction.Weighted.LayerCutoff.torusSupNorm_zero_nonpos <;> assumption
end MeetingBlocks
end YangMills.Construction.SeparatedClasses
