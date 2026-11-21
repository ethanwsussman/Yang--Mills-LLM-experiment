import YangMills.Construction.InfiniteLattice.FaceEnergyUnderProbability
import YangMills.Construction.InfiniteLattice.FactsOfOneLatticeAtOneSpacingProof
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice.FaceEnergyBounds
variable {a : ℝ}
theorem continuous_faceEnergy (p : ElementaryPlaquette a) :
    Continuous fun U : GaugeField a => faceEnergy U p := by apply _root_.YangMills.Construction.LatticeConventions.SymmetryGeneration.continuous_faceEnergy <;> assumption
theorem faceEnergy_nonneg_and_le_two (hlog : Matrices.ComplexMatrix2.UnitaryLogarithmProperties)
    (U : Link a → Matrices.ComplexMatrix2.specialUnitary) (p : ElementaryPlaquette a) :
    0 ≤ faceEnergy U p ∧ faceEnergy U p ≤ 2 := by apply _root_.YangMills.Construction.FixedSpacing.BasicFactsProof.faceEnergy_mem_Icc <;> assumption
theorem finite_setOf_center_mem (ha : 0 < a) {S : Set AmbientSpace}
    (hS : Bornology.IsBounded S) :
    {p : ElementaryPlaquette a | p.center ∈ S}.Finite := by apply _root_.YangMills.Construction.ReflectionPositivity.RepresentativeCovariance.finite_center_mem_of_isBounded <;> assumption
theorem faceEnergyBoundedAndFacesLocallyFinite_holds
    (hlog : Matrices.ComplexMatrix2.UnitaryLogarithmProperties) :
    FaceEnergyBoundedAndFacesLocallyFinite := by
  intro s ν hν
  have ha : 0 < PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ) := by
    have hL : (0 : ℝ) < s.L := by
      have := s.isAdmissible.2
      exact_mod_cast (by omega : 0 < s.L)
    exact zpow_pos hL _
  refine ⟨⟨hν, fun p => ⟨⟨(continuous_faceEnergy p).measurable, 2, fun U => ?_⟩,
    fun U => faceEnergy_nonneg_and_le_two hlog U p⟩⟩, fun S hS => finite_setOf_center_mem ha hS⟩
  obtain ⟨h0, h2⟩ := faceEnergy_nonneg_and_le_two hlog U p
  exact abs_le.mpr ⟨by linarith, h2⟩
end YangMills.Construction.InfiniteLattice.FaceEnergyBounds
