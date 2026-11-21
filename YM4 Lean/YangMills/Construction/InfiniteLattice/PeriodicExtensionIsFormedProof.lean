import YangMills.Construction.InfiniteLattice.InvarianceOfTheTorusMeasuresUnderLatticeIsometriesProof
import YangMills.Construction.InfiniteLattice.PeriodicExtensionIsFormed
import YangMills.Construction.Lattice.CompactGaugeFieldSpaceAndPartitionBounds
import YangMills.Construction.Lattice.SiteAndPlaquetteCounts
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LiftFormation
open YangMills.Construction.InfiniteLattice YangMills.Construction.CutoffLattice
theorem measurableEmbedding_subtypeVal_compactGaugeField (L m : ℕ) (j : ℤ) :
    MeasurableEmbedding (fun W : PeriodicLattice.CompactGaugeField L m j => W.1) := by apply _root_.YangMills.Construction.TorusMeasureSymmetry.measurableEmbedding_coe <;> assumption
theorem wilsonGibbsMeasure_univ (L m K : ℕ) (β : ℝ)
    (hint : Integrable (PeriodicLattice.boltzmannWeight β)
      (PeriodicLattice.productHaarMeasure L m (K : ℤ)))
    (hZ : 0 < PeriodicLattice.partitionFunction L m K β) :
    PeriodicLattice.wilsonGibbsMeasure L m K β univ = 1 := by
  have hlin : ENNReal.ofReal (PeriodicLattice.partitionFunction L m K β) =
      ∫⁻ W, ENNReal.ofReal (PeriodicLattice.boltzmannWeight β W)
        ∂PeriodicLattice.productHaarMeasure L m (K : ℤ) :=
    ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun W => (Real.exp_pos _).le)
  simp only [PeriodicLattice.wilsonGibbsMeasure, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← hlin]
  exact ENNReal.inv_mul_cancel (by simpa using hZ) ENNReal.ofReal_ne_top
theorem productHaarMeasure_compl_eq_zero (L m : ℕ) (j : ℤ)
    (hc : Continuous (PeriodicLattice.gaugeFieldOfPositive :
      (PeriodicLattice.PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary) → _))
    (hr : range (PeriodicLattice.gaugeFieldOfPositive :
      (PeriodicLattice.PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary) → _) =
        PeriodicLattice.compactGaugeFields L m j) :
    PeriodicLattice.productHaarMeasure L m j (PeriodicLattice.compactGaugeFields L m j)ᶜ = 0 := by
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have : SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hclosed := PeriodicLattice.isClosed_compactGaugeFields L m j
  have hempty : (PeriodicLattice.gaugeFieldOfPositive :
      (PeriodicLattice.PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary) → _) ⁻¹'
        (PeriodicLattice.compactGaugeFields L m j)ᶜ = ∅ := by
    rw [← hr]
    ext v
    simp
  rw [PeriodicLattice.productHaarMeasure,
    Measure.map_apply hc.measurable hclosed.measurableSet.compl, hempty, measure_empty]
theorem pushforwardIntegral_of_map (L m K : ℕ) (β : ℝ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (hpull : Measurable (liftMap L m K))
    (himage : (torusWilson L m K β).map (liftMap L m K) = periodizedMeasure L m K β) :
    PushforwardIntegral L m K E β := by
  rintro F hF ⟨C, hC⟩
  refine ⟨hF.comp hpull, ⟨C, fun W => hC _⟩, ?_⟩
  rw [integralAgainst, ← himage, integral_map hpull.aemeasurable hF.aestronglyMeasurable]
  rfl
theorem measuresAndPushforward_of_mass (L m K : ℕ) (β : ℝ)
    (hone : PeriodicLattice.wilsonGibbsMeasure L m K β univ = 1)
    (hnull : PeriodicLattice.wilsonGibbsMeasure L m K β
      (PeriodicLattice.compactGaugeFields L m (K : ℤ))ᶜ = 0) :
    MeasuresAndPushforward L m K β := by
  have hemb := measurableEmbedding_subtypeVal_compactGaugeField L m (K : ℤ)
  have hrange : range (fun W : TorusGaugeFields L m K => W.1) =
      PeriodicLattice.compactGaugeFields L m (K : ℤ) :=
    Subtype.range_coe
  have hmap : (torusWilson L m K β).map (fun W : TorusGaugeFields L m K => W.1) =
      PeriodicLattice.wilsonGibbsMeasure L m K β := by
    rw [torusWilson, hemb.map_comap, hrange]
    exact Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hnull)
  have hprob : IsProbabilityMeasure (torusWilson L m K β) := ⟨by
    have h := congrArg (fun μ => μ univ) hmap
    simp only [Measure.map_apply hemb.measurable MeasurableSet.univ, preimage_univ] at h
    rw [h, hone]⟩
  have hpull : Measurable (liftMap L m K) :=
    (measurable_liftField L m (K : ℤ)).comp hemb.measurable
  have himage : (torusWilson L m K β).map (liftMap L m K) = periodizedMeasure L m K β := by
    have hcomp : liftMap L m K =
        liftField L m (K : ℤ) ∘ fun W : TorusGaugeFields L m K => W.1 := rfl
    rw [hcomp, ← Measure.map_map (measurable_liftField L m (K : ℤ)) hemb.measurable, hmap]
    rfl
  refine ⟨hprob, hmap, himage, ?_, pushforwardIntegral_of_map L m K β ℝ hpull himage,
    pushforwardIntegral_of_map L m K β ℂ hpull himage⟩
  rw [← himage]
  exact Measure.isProbabilityMeasure_map hpull.aemeasurable
theorem linkImages_holds (L m K : ℕ) : LinkImages L m K :=
  ⟨fun _ => ⟨rfl, rfl, rfl⟩, fun W e => liftField_apply_of_mem W.2 e⟩
theorem statement_holds
    (hdensity : PeriodicLattice.GaugeFieldSpace.FieldSpaceAndPartitionBounds)
    (hcounts : PeriodicLattice.SiteAndPlaquetteCounts) : Statement := by
  intro s β hβ
  obtain ⟨hint, hlow, -⟩ := ((hdensity s).2.1 β hβ).2
  have hZ : 0 < PeriodicLattice.partitionFunction s.L s.m s.K β :=
    lt_of_lt_of_le (Real.exp_pos _) hlow
  have hL : 13 ≤ s.L := s.isAdmissible.2
  have hm : 0 < (s.m : ℕ) := s.m.pos
  have hK : 0 < (s.K : ℕ) := s.K.pos
  obtain ⟨-, hembedding, hrange, -, -⟩ :=
    (hcounts s.L s.m ((s.K : ℕ) : ℤ) (by omega) (by omega)).2.2.2.2.2 (by omega) (by omega)
  have hHaar := productHaarMeasure_compl_eq_zero s.L s.m ((s.K : ℕ) : ℤ)
    hembedding.continuous hrange
  have hnull : PeriodicLattice.wilsonGibbsMeasure s.L s.m s.K β
      (PeriodicLattice.compactGaugeFields s.L s.m ((s.K : ℕ) : ℤ))ᶜ = 0 := by
    have hac : PeriodicLattice.wilsonGibbsMeasure s.L s.m s.K β ≪
        PeriodicLattice.productHaarMeasure s.L s.m ((s.K : ℕ) : ℤ) :=
      (withDensity_absolutelyContinuous _ _).smul_left _
    exact hac hHaar
  exact ⟨linkImages_holds s.L s.m s.K, continuous_liftCompactField,
    measuresAndPushforward_of_mass s.L s.m s.K β (wilsonGibbsMeasure_univ s.L s.m s.K β hint hZ)
      hnull⟩
end YangMills.Construction.LiftFormation
