import YangMills.Construction.InfiniteLattice.ExtendedMeasureIsTheWilsonMeasureOnConfigurations
import YangMills.Construction.InfiniteLattice.PullBackOfAConfigurationByAnInducedIsometryProof
import YangMills.Construction.PeriodicLattice.WilsonMeasureIsometryInvarianceProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
open PeriodicLattice Matrices
namespace FixedSpacing
namespace LiftedGibbs
variable {L m : ℕ} {j : ℤ}
theorem gaugeFieldOfPositive_restrictToPositiveBonds
    (hx : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (U : CompactGaugeField L m j) :
    gaugeFieldOfPositive (restrictToPositiveBonds U) = U.1 := by apply _root_.YangMills.Construction.InducedPullback.gaugeFieldOfPositive_restrict <;> assumption
theorem measurable_gaugeFieldOfPositive :
    Measurable (gaugeFieldOfPositive :
      (PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) → Bond L m j → ComplexMatrix2) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.measurable_gaugeFieldOfPositive <;> assumption
theorem measurable_restrictToPositiveBonds :
    Measurable (restrictToPositiveBonds : CompactGaugeField L m j → _) :=
  measurable_pi_lambda _ fun b =>
    (continuous_iInf_dom (i := b.1) continuous_induced_dom :
      Continuous (fun U : CompactGaugeField L m j => CompactGaugeField.linkValue U b.1)).measurable
theorem measurableEmbedding_val [CompactSpace (CompactGaugeField L m j)] :
    MeasurableEmbedding (fun U : CompactGaugeField L m j => U.1) := by apply _root_.YangMills.Construction.FixedSpacing.CurvatureObservable.measurableEmbedding_linkValues <;> assumption
theorem map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {f : α → β}
    (hf : MeasurableEmbedding f) (μ : Measure α) (g : β → ENNReal) :
    (μ.withDensity (g ∘ f)).map f = (μ.map f).withDensity g := by
  ext s hs
  rw [Measure.map_apply hf.measurable hs, withDensity_apply _ (hf.measurable hs),
    withDensity_apply _ hs, hf.restrict_map, hf.lintegral_map]
  rfl
end LiftedGibbs
open LiftedGibbs in
theorem liftedGibbs_eq_liftedWilsonMeasure
    (hproduct : GaugeFieldProduct.Statement) :
    LiftedGibbsIsLiftedWilsonMeasure := by
  intro D
  obtain ⟨hsp, -, hc, -⟩ := hproduct.1 D.L D.m (D.level : ℤ) D.admissible D.m.pos
    (Int.natCast_nonneg _)
  have hx : ∀ b : Bond D.L D.m (D.level : ℤ),
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    hsp.2.2.2.2.2
  obtain ⟨-, -, hcompact, -, -, hspec, -⟩ := hc
  have := hcompact
  have hE := measurableEmbedding_val (L := D.L) (m := D.m) (j := (D.level : ℤ))
  set ι : CompactGaugeField D.L D.m (D.level : ℤ) → Bond D.L D.m (D.level : ℤ) → ComplexMatrix2 :=
    fun U => U.1 with hι
  have hs : (gaugeFieldMeasure D.L D.m (D.level : ℤ)).map restrictToPositiveBonds =
      ComplexMatrix2.haarPi (PositivelyOrientedBond D.L D.m (D.level : ℤ)) := hspec
  have hhaar : (gaugeFieldMeasure D.L D.m (D.level : ℤ)).map ι =
      productHaarMeasure D.L D.m (D.level : ℤ) := by
    unfold productHaarMeasure gaugeFieldHaar
    rw [← hs, Measure.map_map measurable_gaugeFieldOfPositive measurable_restrictToPositiveBonds]
    congr 1
    funext U
    exact (gaugeFieldOfPositive_restrictToPositiveBonds hx U).symm
  have hZ : D.partitionFunction = PeriodicLattice.partitionFunction D.L D.m D.level D.β := by
    unfold PeriodicLattice.partitionFunction
    rw [← hhaar, hE.integral_map]
    rfl
  have hmeas : D.gibbs.map ι = PeriodicLattice.wilsonGibbsMeasure D.L D.m D.level D.β := by
    unfold PeriodicLattice.wilsonGibbsMeasure
    rw [← hZ, ← hhaar, ← map_withDensity_comp hE]
    unfold Setup.gibbs
    rw [Measure.map_smul]
    rfl
  unfold Setup.liftedGibbs InfiniteLattice.liftedWilsonMeasure
  rw [← hmeas, Measure.map_map (InfiniteLattice.measurable_liftField _ _ _) hE.measurable]
  rfl
end FixedSpacing
end YangMills.Construction
