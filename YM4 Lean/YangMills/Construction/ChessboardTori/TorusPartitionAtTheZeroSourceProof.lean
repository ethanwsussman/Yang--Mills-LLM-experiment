import YangMills.Construction.ChessboardTori.TorusPartitionAtTheZeroSource
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import YangMills.Construction.Lattice.LatticeSymmetriesRectangularToriAndInducedSymmetries
import YangMills.Construction.Lattice.ThePlainActionIsAnActionByStructureMaps
import YangMills.Construction.Lattice.WeightsAsFunctionsOfTheConfigurationAndSourcedIntegrals
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori
theorem ZeroSourcePartition.holds : ZeroSourcePartition.Statement := by
  intro S
  have hFin := GaugeAction.StructuralAction.instFinitePlaquette S.toStandingParameters ((S.K : ℕ) : ℤ)
  let _ := Fintype.ofFinite (PeriodicLattice.Plaquette S.L S.m ((S.K : ℕ) : ℤ))
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have : SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hMeas : MeasurableSet (PeriodicLattice.compactGaugeFields S.L S.m ((S.K : ℕ) : ℤ)) :=
    (PeriodicLattice.isClosed_compactGaugeFields S.L S.m ((S.K : ℕ) : ℤ)).measurableSet
  have hAe : ∀ᵐ U ∂(PeriodicLattice.productHaarMeasure S.L S.m ((S.K : ℕ) : ℤ)),
      U ∈ PeriodicLattice.compactGaugeFields S.L S.m ((S.K : ℕ) : ℤ) := by
    unfold PeriodicLattice.productHaarMeasure
    refine (ae_map_iff (p := fun U => U ∈ PeriodicLattice.compactGaugeFields S.L S.m ((S.K : ℕ) : ℤ))
      (TorusShape.continuous_gaugeFieldOfPositive (s := S.toStandingParameters) S.m).measurable.aemeasurable
      hMeas).2 (ae_of_all _ fun v => ?_)
    exact TorusShape.gaugeFieldOfPositive_mem (s := S.toStandingParameters) S.m S.m.pos v
  change ∫ U, PeriodicLattice.sourcedBoltzmannWeight S.β 0 U
      ∂(PeriodicLattice.productHaarMeasure S.L S.m ((S.K : ℕ) : ℤ)) = ∫ U, 1 * _ ∂_
  refine integral_congr_ae (hAe.mono fun U hU => ?_)
  simp only [one_mul]
  unfold PeriodicLattice.sourcedBoltzmannWeight PeriodicLattice.boltzmannWeight
    PeriodicLattice.barycenterWeightedEnergy PeriodicLattice.plaquetteWeightedEnergy
    PeriodicLattice.wilsonAction
  simp only [finsum_eq_sum_of_fintype, PeriodicLattice.complexEnergy_eq_realEnergy hU,
    Pi.zero_apply, sub_zero]
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  simp only [← Finset.mul_sum]
  ring
end YangMills.Construction.ChessboardTori
end
