import YangMills.Construction.Lattice.WeightsAsFunctionsOfTheConfigurationAndSourcedIntegrals
import YangMills.Construction.Towers.SumOfThePlaquetteTermsOnASide
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LeftChartAlgebra.FaceSum
theorem plaquetteEnergy_complex_eq_real {L m : ℕ} {j : ℤ}
    {U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2}
    (hU : U ∈ PeriodicLattice.compactGaugeFields L m j) (p : PeriodicLattice.Plaquette L m j) :
    PeriodicLattice.plaquetteEnergy U p = ((PeriodicLattice.plaquetteCost U p : ℝ) : ℂ) := by apply _root_.YangMills.Construction.PeriodicLattice.complexEnergy_eq_realEnergy <;> assumption
theorem complexAction_eq_real_sum {L n k j : ℕ} {U : Tower.Edge L n k j → Matrices.ComplexMatrix2}
    (hU : U ∈ Tower.fieldSpace L n k j) :
    Tower.complexAction U =
      ((∑ᶠ p : Tower.Face L n k j, PeriodicLattice.plaquetteCost U p : ℝ) : ℂ) := by
  have hpush := AddMonoidHom.map_finsum_of_injective (Complex.ofRealHom.toAddMonoidHom)
    Complex.ofReal_injective (fun p : Tower.Face L n k j => PeriodicLattice.plaquetteCost U p)
  have hpush' : ((∑ᶠ p : Tower.Face L n k j, PeriodicLattice.plaquetteCost U p : ℝ) : ℂ) =
      ∑ᶠ p : Tower.Face L n k j, ((PeriodicLattice.plaquetteCost U p : ℝ) : ℂ) := hpush
  rw [hpush']
  exact finsum_congr fun p => plaquetteEnergy_complex_eq_real hU p
theorem faceSumFiniteSide_holds : Tower.LeftChartAlgebra.FaceSumFiniteSide := by
  intro L n k j _ _ _
  refine ⟨fun U hU => complexAction_eq_real_sum hU, fun U hU => ?_⟩
  exact complexAction_eq_real_sum hU
end YangMills.Construction.Tower.LeftChartAlgebra.FaceSum
end
