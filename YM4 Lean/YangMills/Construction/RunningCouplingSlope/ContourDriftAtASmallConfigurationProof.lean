import YangMills.Construction.RunningCouplingSlope.ContourDriftAtASmallConfiguration
import YangMills.Construction.Towers.ContourDriftIsLocalWithACounterpartProof
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.LocalKernels.ContourLogDriftLocality
open Periodisation Tower
open InfiniteLattice (AmbientSpace)
variable {L n k j : ℕ}
theorem isLocal_of_stepProperties (hF : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hS : Tower.SmoothingNearIdentity)
    (hQ : Tower.EdgeProjectionProperties)
    (hC : PeriodicLattice.BlockContoursAndCombs)
    (hP : PeriodicLattice.LevelBondOrientationDichotomy)
    (hZ : Tower.BlockPathContourPivotStatement)
    (hB : FullSpace.CubesCorridorsPivotEdgesAndPaths)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    {V : Tower.Edge L n k j → Matrices.ComplexMatrix2}
    {U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2}
    (hs : Tower.AsDifferentials.StepConditions j V U)
    {U' : FullSpace.Edge L k 0 → Matrices.ComplexMatrix2}
    (hw : FullSpace.AsDifferentials.StepConditions j (liftGaugeField L n k j V) U')
    (hVw : liftGaugeField L n k j V ∈ FullSpace.smallComplexFields L k j) :
    IsLocalWithPeriodicCounterpart L n (CellClass.edgeClass k j hj.le)
      (CellClass.vertexClass k (j + 1) hj)
      (3 * Tower.meshAt L k (j + 1) / 2)
      (FullSpace.contourLogDrift (liftGaugeField L n k j V)) (Tower.contourLogDrift V) := by apply _root_.YangMills.Construction.LocalKernels.ContourDriftLocality.isLocalWithPeriodicCounterpart_of_stepProperties <;> assumption
theorem contourLogDriftIsLocal_holds (hD : Tower.AsDifferentials.CovariantMeansAreDerivatives)
    (hI : IterMeansOfLift.Claim)
    (hE : LiftIsGaugeField)
    (hF : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hS : Tower.SmoothingNearIdentity)
    (hQ : Tower.EdgeProjectionProperties)
    (hC : PeriodicLattice.BlockContoursAndCombs)
    (hP : PeriodicLattice.LevelBondOrientationDichotomy)
    (hZ : Tower.BlockPathContourPivotStatement)
    (hB : FullSpace.CubesCorridorsPivotEdgesAndPaths) : ContourLogDriftIsLocal := by
  intro L hL k n hn U hU j h V hV
  have hk : 1 ≤ k := by omega
  have hj : j < k := h
  have hVw : liftGaugeField L n k j V ∈ FullSpace.smallComplexFields L k j :=
    ⟨(hE L n k j hL hn hj.le _).2 hV.1, fun _ => hV.2 _⟩
  have hUw := (hI L hL k n hn hk U hU.1).1.1 hU
  exact isLocal_of_stepProperties hF hS hQ hC hP hZ hB hL hn hj
    (((hD L hL k hk).1 n hn).1 j hj _ hV U hU) ((hD L hL k hk).2.1 j hj _ hVw _ hUw) hVw
end YangMills.Construction.LocalKernels.ContourLogDriftLocality
end
