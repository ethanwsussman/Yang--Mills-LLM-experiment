import YangMills.Construction.Lattice.LengthsOfConnectedUnions
import YangMills.Construction.SeparatedSequences.WeightedDistanceDominatesTheLength
import YangMills.Construction.Torus.BoundsOnTheWeightedDistanceProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set MeasureTheory PeriodicLattice TorusMetric
namespace SeparatedClasses.ChainDistBound
theorem pathLengthIn_nonneg {S : ℝ} (Γ : List LiftedSegment) (B : Set (Torus4 S)) :
    0 ≤ pathLengthIn S Γ B := by apply _root_.YangMills.Construction.Weighted.DistBounds.pathLengthIn_nonneg <;> assumption
variable (C : ClassData) (Ω : ℕ → Set C.Point)
end SeparatedClasses.ChainDistBound
end YangMills.Construction
end
