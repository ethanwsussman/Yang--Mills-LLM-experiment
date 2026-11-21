import YangMills.Construction.InfiniteLattice.PeriodicExtensionOfATorusIsFaithful
import YangMills.Construction.InfiniteLattice.TorusOfAPeriodLatticeIsFaithful
import YangMills.Construction.InfiniteLattice.WilsonMeasuresOfATorusAreProbabilities
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice.QuotientGibbsMeasuresProbability
variable {a : ℝ}
instance : SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
  haveI : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  Topology.IsInducing.secondCountableTopology (f := Subtype.val) ⟨rfl⟩
instance quotientHaar_isProbabilityMeasure (Γ : PeriodSublattice a) :
    IsProbabilityMeasure Γ.quotientHaar := by
  unfold PeriodSublattice.quotientHaar Matrices.ComplexMatrix2.haarPi
  infer_instance
theorem boltzmannWeight_continuous_and_bounds (Γ : PeriodSublattice a)
    (hfin : Finite Γ.QuotientPlaquette)
    (hcont : ∀ p : Γ.QuotientPlaquette, Continuous fun U => Γ.quotientFaceEnergy U p)
    (hmem : ∀ (U : Γ.QuotientField) (p : Γ.QuotientPlaquette),
      Γ.quotientFaceEnergy U p ∈ Set.Icc (0 : ℝ) 2)
    {β : ℝ} (hβ : 0 < β) :
    Continuous (Γ.boltzmannWeight β) ∧
      ∀ U, Real.exp (-2 * β * (Nat.card Γ.QuotientPlaquette : ℝ)) ≤ Γ.boltzmannWeight β U ∧
        Γ.boltzmannWeight β U ≤ 1 := by
  have := Fintype.ofFinite Γ.QuotientPlaquette
  have hsum : ∀ U, ∑ᶠ p : Γ.QuotientPlaquette, Γ.quotientFaceEnergy U p =
      ∑ p : Γ.QuotientPlaquette, Γ.quotientFaceEnergy U p := fun U =>
    finsum_eq_sum_of_fintype _
  have hform : Γ.boltzmannWeight β =
      fun U => Real.exp (-β * ∑ p : Γ.QuotientPlaquette, Γ.quotientFaceEnergy U p) := by
    funext U
    rw [PeriodSublattice.boltzmannWeight, hsum]
  rw [hform]
  refine ⟨Real.continuous_exp.comp
    (continuous_const.mul (continuous_finsetSum _ fun p _ => hcont p)), fun U => ?_⟩
  have h0 : 0 ≤ ∑ p : Γ.QuotientPlaquette, Γ.quotientFaceEnergy U p :=
    Finset.sum_nonneg fun p _ => (hmem U p).1
  have h2 : ∑ p : Γ.QuotientPlaquette, Γ.quotientFaceEnergy U p ≤
      2 * (Nat.card Γ.QuotientPlaquette : ℝ) := by
    calc ∑ p : Γ.QuotientPlaquette, Γ.quotientFaceEnergy U p
        ≤ ∑ _p : Γ.QuotientPlaquette, (2 : ℝ) := Finset.sum_le_sum fun p _ => (hmem U p).2
      _ = 2 * (Nat.card Γ.QuotientPlaquette : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, nsmul_eq_mul,
            mul_comm]
  refine ⟨Real.exp_le_exp.mpr ?_, Real.exp_le_one_iff.mpr ?_⟩
  · linarith [mul_le_mul_of_nonneg_left h2 hβ.le]
  · linarith [mul_nonneg hβ.le h0]
theorem statement_holds (hLift : PeriodicLiftIsFaithful)
    (hQuot : QuotientTorusFaithful.Statement) : Statement := by
  intro β hβ a ha Γ
  have hE := hLift a ha Γ
  have hT := hQuot a ha Γ
  obtain ⟨hcont, hb⟩ := boltzmannWeight_continuous_and_bounds Γ hT.finite_quotientPlaquette
    hE.continuous_quotientFaceEnergy hE.quotientFaceEnergy_mem_Icc hβ
  have hint : Integrable (Γ.boltzmannWeight β) Γ.quotientHaar := by
    refine Integrable.of_bound hcont.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun U => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg ((Real.exp_pos _).le.trans (hb U).1)]
    exact (hb U).2
  have hlow : Real.exp (-2 * β * (Nat.card Γ.QuotientPlaquette : ℝ)) ≤ Γ.partitionFunction β := by
    have h := integral_mono (integrable_const (μ := Γ.quotientHaar)
      (Real.exp (-2 * β * (Nat.card Γ.QuotientPlaquette : ℝ)))) hint fun U => (hb U).1
    rw [integral_const, probReal_univ, one_smul] at h
    exact h
  have hup : Γ.partitionFunction β ≤ 1 := by
    have h := integral_mono hint (integrable_const (μ := Γ.quotientHaar) (1 : ℝ)) fun U => (hb U).2
    rw [integral_const, probReal_univ, one_smul] at h
    exact h
  have hpos : 0 < Γ.partitionFunction β := (Real.exp_pos _).trans_le hlow
  have hprob : IsProbabilityMeasure (Γ.gibbsMeasure β) := by
    constructor
    rw [PeriodSublattice.gibbsMeasure, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ, smul_eq_mul,
      ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun U =>
        (Real.exp_pos _).le.trans (hb U).1)]
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hpos).ne' ENNReal.ofReal_ne_top
  have hlift : Continuous Γ.lift := hE.isEmbedding_lift.continuous
  refine ⟨hlow, hup, hprob, ?_, fun F hF => ?_⟩
  · exact Measure.isProbabilityMeasure_map hlift.measurable.aemeasurable
  · rw [PeriodSublattice.liftedGibbsMeasure,
      integral_map hlift.measurable.aemeasurable hF.1.1.aestronglyMeasurable]
    rfl
end YangMills.Construction.InfiniteLattice.QuotientGibbsMeasuresProbability
