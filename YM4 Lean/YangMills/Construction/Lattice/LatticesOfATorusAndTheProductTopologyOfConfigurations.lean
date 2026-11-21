import YangMills.Construction.Lattice.SignAndGaugeInvarianceOfTheActionProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j : ℤ}
theorem Bond.opposite_opposite (b : Bond L m j) : b.opposite.opposite = b := by apply _root_.YangMills.SharedProofs.p1012 <;> assumption
theorem Bond.positive_or_opposite_positive (b : Bond L m j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p7155 <;> assumption
theorem fullTrace_im_eq_zero {A : Matrices.ComplexMatrix2} (hA : A ∈ compactGaugeGroup) :
    (Matrices.ComplexMatrix2.fullTrace A).im = 0 := by apply _root_.YangMills.Construction.PeriodicLattice.ActionSign.fullTrace_im_eq_zero <;> assumption
theorem plaquetteHolonomy_mem_compactGaugeGroup (U : CompactGaugeField L m j) (p : Plaquette L m j) :
    plaquetteHolonomy U.1 p ∈ compactGaugeGroup := by
  refine Submonoid.list_prod_mem _ fun A hA => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hA
  exact (U.linkValue b).2
theorem complexPlaquetteEnergy_eq (U : CompactGaugeField L m j) (p : Plaquette L m j) :
    plaquetteEnergy U.1 p = (plaquetteCost U.1 p : ℝ) := by
  have him := fullTrace_im_eq_zero (plaquetteHolonomy_mem_compactGaugeGroup U p)
  apply Complex.ext <;> simp [plaquetteEnergy, plaquetteCost, him]
end YangMills.Construction.PeriodicLattice
