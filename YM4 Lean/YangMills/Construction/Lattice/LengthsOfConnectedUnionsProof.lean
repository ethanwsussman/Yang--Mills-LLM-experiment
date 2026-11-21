import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.CubePartitionsAndRegions
import YangMills.Construction.Lattice.LengthsOfConnectedUnions
import YangMills.Construction.Torus.SumsOverTheSitesOfASeparatedSequenceProof
import Mathlib
set_option autoImplicit false
open Set MeasureTheory YangMills.Construction.TorusMetric YangMills.Construction.PeriodicLattice
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ConnectedUnions
section Arcs
variable {ι : Type*} [DecidableEq ι]
end Arcs
section Numbers
variable {S : ℝ}
theorem torusSupNorm_neg (x : Torus4 S) : torusSupNorm (-x) = torusSupNorm x := by apply _root_.YangMills.Construction.SequenceGeometryProof.torusSupNorm_neg <;> assumption
theorem torusSupNorm_add_le (x y : Torus4 S) :
    torusSupNorm (x + y) ≤ torusSupNorm x + torusSupNorm y := by apply _root_.YangMills.Construction.SequenceGeometryProof.torusSupNorm_add_le <;> assumption
theorem torusSupNorm_zero : torusSupNorm (0 : Torus4 S) = 0 := by apply _root_.YangMills.Construction.SequenceGeometryProof.torusSupNorm_zero <;> assumption
theorem setSupDist_singleton (z : Torus4 S) (A : Set (Torus4 S)) :
    setSupDist {z} A = ⨅ b ∈ A, ENNReal.ofReal (torusSupNorm (z - b)) := by
  simp [setSupDist]
theorem setSupDist_singleton_ne_top {A : Set (Torus4 S)} (hA : A.Nonempty) (z : Torus4 S) :
    setSupDist {z} A ≠ ∞ := by apply _root_.YangMills.Construction.Weighted.SiteSumProof.setSupDist_singleton_ne_top <;> assumption
theorem l1NormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ l1NormVec v :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _
theorem continuous_pointAt (s : LiftedSegment) : Continuous (s.pointAt S) := by apply _root_.YangMills.Construction.Weighted.WeightedLengthProof.continuous_pointAt <;> assumption
end Numbers
section Chains
variable {S : ℝ}
end Chains
section Lists
end Lists
section Values
variable (L m : ℕ) {c : ℝ}
end Values
section Layers
variable {L m : ℕ}
end Layers
end YangMills.Construction.ConnectedUnions
