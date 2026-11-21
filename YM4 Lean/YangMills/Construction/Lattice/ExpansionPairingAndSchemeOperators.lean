import YangMills.Construction.Lattice.FlatDeterminingSetOfASeparatedSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Matrices SeparatedSequences SeparatedSequences.BondKinds
namespace PeriodicLattice
variable {L m : ℕ}
section SeriesExpansions
variable {K : ℕ}
abbrev LeveledBond (L m K : ℕ) : Type := Σ k : ℕ, BondAtLevel L m K k
def LeveledBond.flip (e : LeveledBond L m K) : LeveledBond L m K := ⟨e.1, e.2.opposite⟩
def positiveLeveledBonds (R : Set (LeveledBond L m K)) : Set (LeveledBond L m K) :=
  {e | e ∈ R ∧ e.2.IsPositivelyOriented}
def antisymmetricFields (R : Set (LeveledBond L m K)) : Set (LeveledBond L m K → ComplexMatrix2) :=
  {μ | (∀ e ∈ R, μ e ∈ complexLieAlgebra) ∧ (∀ e ∈ R, μ e.flip = -μ e) ∧ ∀ e ∉ R, μ e = 0}
end SeriesExpansions
section Pairing
variable (S : ScaleData)
def leveledMesh (e : LeveledBond L m S.levels) : ℝ := S.levelMesh L e.1
def weightedPairing (R : Set (LeveledBond L m S.levels))
    (μ μ' : LeveledBond L m S.levels → ComplexMatrix2) : ℂ :=
  ∑ᶠ e ∈ positiveLeveledBonds R,
    ((leveledMesh S e ^ 4 : ℝ) : ℂ) * ComplexMatrix2.halfTrace (μ e * μ' e)
abbrev outwardFields (Ω : ℕ → Set (FourTorus L m)) :
    Set (LeveledBond L m S.levels → ComplexMatrix2) :=
  antisymmetricFields (interiorOutwardSet S Ω)
abbrev outwardPairing (Ω : ℕ → Set (FourTorus L m))
    (μ μ' : LeveledBond L m S.levels → ComplexMatrix2) : ℂ :=
  weightedPairing S (interiorOutwardSet S Ω) μ μ'
end Pairing
end PeriodicLattice
end YangMills.Construction
