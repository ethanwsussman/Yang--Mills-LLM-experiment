import YangMills.Construction.Lattice.LatticesCubesOfAStandardPartitionAndEnlargements
import YangMills.Construction.Lattice.TriplesAndTheOperatorsOfASequenceInAnAmbientRegion
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set TorusMetric PeriodicLattice SeparatedSequences SeparatedRegions SequenceTriples Matrices
open scoped ENNReal ContDiff
noncomputable section
namespace GreenInputs
variable {L m : ℕ} (S : ScaleData) (Ω : ℕ → Set (FourTorus L m))
def oneField : FineBond L m S → ComplexMatrix2 := fun _ => 1
abbrev oneFieldOnFirst : FineBond L m S → ComplexMatrix2 :=
  firstMemberRestriction S Ω (oneField S)
structure IsInputSequence (M : ℕ) (gapFloor g : ℝ) : Prop where
  m_pos : 0 < m
  levels_pos : 0 < S.levels
  unitLevel_eq_top : S.unitLevel = S.top
  block_le : M ≤ L ^ S.blockExp
  gap_le : gapFloor ≤ g
  separated : IsSeparatedWithGap S g Ω
  eq_empty_of_gt : ∀ n, S.top < n → Ω n = ∅
  sites_le : 6 * gapFloor ≤
    CubePartitions.sitesPerAxis L m (levelDepth S.levels S.top)
variable {S}
variable (S)
end GreenInputs
end
end YangMills.Construction
