import YangMills.Construction.Lattice.InverseOfTheSystemAtLayerZero
import YangMills.Construction.SeparatedSequences.RestrictedTripleConstant
import YangMills.Construction.SeparatedSequences.SystemAtASmallTriple
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SeparatedSequences.PieceChain
open YangMills.Construction.PeriodicLattice YangMills.Construction.SeparatedSequences
open YangMills.Construction.SeparatedRegions YangMills.Construction.SequenceTriples
open YangMills.Construction.Matrices
def expansionInverseConst (L : ℕ) : ℝ :=
  Real.exp 8 * max (SmallTripleSystem.inverseConstant L) (baseLayerBound L)
def expansionSmallness (L : ℕ) : ℝ :=
  min (1 / 16) (min (baseLayerSmallness L)
    (min (SmallTripleSystem.tripleRadius L / (4 * restrictedTripleConst L))
      (((L : ℝ) ^ 2)⁻¹ * classCeiling L)))
variable {L m : ℕ} (S : ScaleData) (Ω : ℕ → Set (FourTorus L m))
inductive BlockIndex
  | first
  | site
  | reduced
  | full
end YangMills.Construction.SeparatedSequences.PieceChain
end
