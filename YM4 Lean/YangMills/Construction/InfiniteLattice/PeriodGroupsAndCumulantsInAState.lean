import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def IsPeriodSubgroup {a : ℝ} (ν : Measure (GaugeField a)) (P : AddSubgroup (LatticePoint a)) : Prop :=
  P.FiniteIndex ∧ ∀ v ∈ P, IsSymmetricUnder ν (shift v)
theorem liftField_apply (L m : ℕ) (j : ℤ) {U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2}
    (hU : U ∈ PeriodicLattice.compactGaugeFields L m j) (b : Link (PeriodicLattice.meshSize L j)) :
    ((liftField L m j U b : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) =
      U (projectLink L m j b) := by apply _root_.YangMills.Construction.InfiniteLattice.liftField_apply_of_mem <;> assumption
end YangMills.Construction.InfiniteLattice
