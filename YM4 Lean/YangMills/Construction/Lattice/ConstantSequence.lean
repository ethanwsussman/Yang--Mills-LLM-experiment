import YangMills.Construction.Lattice.TowersAndMinimalConfigurations
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
variable {L m : ℕ}
def constantWholeTorus : ℕ → Set (FourTorus L m) := fun _ => univ
def constantDeterminingBondSet (K k : ℕ) : Set (Σ j : ℕ, BondAtLevel L m K j) :=
  determiningBondSet K k constantWholeTorus
def IsConstantCritical (ω : ℝ) (K k : ℕ) (V : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2)
    (U : BondAtLevel L m K 0 → ComplexMatrix2) : Prop :=
  IsCriticalForAction ω K k constantWholeTorus V U
end YangMills.Construction.PeriodicLattice
