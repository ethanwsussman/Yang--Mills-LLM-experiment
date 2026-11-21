import YangMills.Construction.Lattice.LevelsDoubleBlocksExpansionsAndBareSteps
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.PeriodicLattice YangMills.Construction.SeparatedSequences YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.SeparatedRegions
variable {L m : ℕ} (S : ScaleData)
def leveledPairing (Ω : ℕ → Set (FourTorus L m)) (ν ν' : LeveledBond L m S → ComplexMatrix2) : ℂ :=
  ∑ᶠ (q) (_ : q ∈ leveledIndexSet S Ω),
    ((bondSpacing S q ^ 4 : ℝ) : ℂ) * ComplexMatrix2.halfTrace (ν q * ν' q)
def spacingWeight (q : LeveledBond L m S) : ℝ := (bondSpacing S q ^ 2)⁻¹
def spacingWeightSMul (ν : LeveledBond L m S → ComplexMatrix2) : LeveledBond L m S → ComplexMatrix2 :=
  fun q => ((spacingWeight S q : ℝ) : ℂ) • ν q
end YangMills.Construction.SeparatedRegions
end
