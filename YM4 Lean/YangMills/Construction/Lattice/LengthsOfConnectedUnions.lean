import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.DataCutSetsTestsAndLocalRadii
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ConnectedUnions
structure SegmentPiece where
  start : ℝ
  stop : ℝ
  start_nonneg : 0 ≤ start
  start_le_stop : start ≤ stop
  stop_le_one : stop ≤ 1
def SegmentPiece.support (S : ℝ) (σ : SegmentPiece) (s : TorusMetric.LiftedSegment) :
    Set (TorusMetric.Torus4 S) :=
  s.pointAt S '' Icc σ.start σ.stop
variable {L m : ℕ}
def scaledSupNorm (c : ℝ) (z : PeriodicLattice.FourTorus L m) : ℝ :=
  c * TorusMetric.torusSupNorm z
end YangMills.Construction.ConnectedUnions
