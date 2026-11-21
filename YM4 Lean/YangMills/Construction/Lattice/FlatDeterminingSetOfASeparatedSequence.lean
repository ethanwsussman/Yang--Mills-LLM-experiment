import YangMills.Construction.Lattice.KindsOfBondsOfASeparatedSequence
import Mathlib
set_option autoImplicit false
open YangMills.Construction.PeriodicLattice YangMills.Construction.SeparatedSequences
noncomputable section
namespace YangMills.Construction.SeparatedSequences.BondKinds
variable {L m : ℕ}
abbrev interiorOutwardSet (S : ScaleData) (Ω : ℕ → Set (FourTorus L m)) :
    Set (Σ j : ℕ, BondAtLevel L m S.levels j) :=
  flatBondSet S Ω
end YangMills.Construction.SeparatedSequences.BondKinds
