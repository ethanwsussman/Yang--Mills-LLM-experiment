import YangMills.Construction.InfiniteLattice.ActionOfTheLatticeIsometriesOnConfigurationsAndFunctions
import YangMills.Construction.InfiniteLattice.InvarianceOfStatesUnderIsometriesOfACutoffLatticeProof
import YangMills.Construction.InfiniteLattice.PlateauVarianceIsTheVarianceOfTheInvariantExpectation
import YangMills.Construction.InfiniteLattice.ReflectionPositivityInTheFullFormFromContinuousLocalFunctions
import YangMills.Construction.InfiniteLattice.TheSpaceOfConfigurationsAndTheSpaceOfMeasures
import YangMills.Construction.InfiniteLattice.WeakLimitsInvariantFunctionsAndACriterionForErgodicity
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ComplexOrder
namespace YangMills.Construction.GibbsAtFixedSpacing.LimitsAndErgodicity
open InfiniteLattice (GaugeField IsSymmetricUnder IsBoundedObservable IsShiftInvariant
  LatticeSymmetry LatticePoint condExpShiftInvariant shiftInvariantSigma observableSupNorm
  plateauVariance shift)
variable {a : ℝ}
theorem isBoundedObservable_of_continuous [CompactSpace (GaugeField a)] {F : GaugeField a → ℂ}
    (hF : Continuous F) : IsBoundedObservable F := by apply _root_.YangMills.Construction.CutoffLatticeStates.MotionInvariance.isBoundedObservable_of_continuous <;> assumption
theorem symmetryClosedUnderWeakLimits (hAct : LatticeSymmetryActionOnFields)
    (hTop : SpacesOfFieldsAndMeasures.FieldAndMeasureSpaceProperties) (ha : 0 < a) :
    SymmetryClosedUnderWeakLimits a := by
  intro ν μ s hconv hinv
  obtain ⟨⟨-, hcomp, -⟩, -, -, hdet, -⟩ := hTop a ha
  have := hcomp
  obtain ⟨⟨-, -, t, -, h, hh, -⟩, -, -, -⟩ := hAct a ha s s
  have hcont : Continuous s.pullbackField := by
    rw [← hh]
    exact h.continuous
  have : IsProbabilityMeasure μ.1 := μ.2
  have hmap : IsProbabilityMeasure (μ.1.map s.pullbackField) :=
    Measure.isProbabilityMeasure_map hcont.aemeasurable
  have hint : ∀ F : GaugeField a → ℂ, Measurable F →
      ∫ U, F U ∂(μ.1.map s.pullbackField) = ∫ U, s.actOn F U ∂μ.1 :=
    fun F hF => integral_map hcont.aemeasurable hF.aestronglyMeasurable
  have heq : (⟨μ.1.map s.pullbackField, hmap⟩ : BorelProb a) = μ := by
    refine hdet _ _ fun F hF => ?_
    have hrF : Continuous (s.actOn F) := hF.1.comp hcont
    have h1 := hconv _ hrF
    have h2 : (fun i => (ν i).integral (s.actOn F)) = fun i => (ν i).integral F :=
      funext fun i => hinv i F (isBoundedObservable_of_continuous hF.1)
    rw [h2] at h1
    have h3 := tendsto_nhds_unique h1 (hconv F hF.1)
    exact (hint F hF.1.measurable).trans h3
  intro A hA
  have hμ : μ.1.map s.pullbackField = μ.1 := congrArg Subtype.val heq
  rw [← hint A hA.1, hμ]
theorem reflectionPositivityFromContinuous
    (hFull : FullReflectionPositivityFromContinuousLocal.Statement)
    (ha : 0 < a) : ReflectionPositivityFromContinuous a := by
  intro Q hQ ν hinv hpos F hF
  simp only [locallyMeasurableIn, mem_iUnion] at hF
  obtain ⟨S, -, hS⟩ := hF
  refine (hFull a ha Q hQ ν hinv hpos).1 F ⟨hS.1.mono ?_ le_rfl, hS.2⟩
  exact iSup₂_le fun b hb => le_iSup₂_of_le b ⟨hb.1.1, hb.2.1⟩ le_rfl
theorem invariantMeasurable_pointwiseInvariant :
    InvariantMeasurableIsPointwiseInvariant a := by
  intro J hJ v U
  have hI : MeasurableSet[shiftInvariantSigma a] (J ⁻¹' {J U}) := hJ (measurableSet_singleton _)
  have h := congrFun (hI.2 v) U
  have hU : U ∈ J ⁻¹' {J U} := rfl
  exact show (shift v).pullbackField U ∈ J ⁻¹' {J U} from by
    by_contra hn
    simp only [LatticeSymmetry.actOn] at h
    rw [indicator_of_notMem hn, indicator_of_mem hU] at h
    simp at h
theorem shiftInvariantSigma_le :
    shiftInvariantSigma a ≤ (inferInstance : MeasurableSpace (GaugeField a)) :=
  fun _ h => h.1
theorem condExpShiftInvariant_ae_eq_const
    (hVar : InfiniteLattice.PlateauVarianceFormula)
    (ha : 0 < a) (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν]
    (hν : IsShiftInvariant ν) {A : GaugeField a → ℂ} (hA : IsBoundedObservable A)
    (h0 : plateauVariance ν A = 0) :
    condExpShiftInvariant ν A =ᵐ[ν] fun _ => ∫ U, A U ∂ν := by
  obtain ⟨-, h2, -, -⟩ := hVar a ha ν hν A hA
  rw [h0] at h2
  have hzero : ∫ U, ‖condExpShiftInvariant ν A U - ∫ V, A V ∂ν‖ ^ 2 ∂ν = 0 := by
    exact_mod_cast h2.symm
  obtain ⟨C, hC⟩ := hA.2
  have hAint : Integrable A ν :=
    Integrable.of_bound hA.1.aestronglyMeasurable C (Eventually.of_forall hC)
  have hbound : ∀ᵐ U ∂ν, ‖condExpShiftInvariant ν A U‖ ≤ C := by
    have h1 : (fun U => ‖condExpShiftInvariant ν A U‖) ≤ᵐ[ν]
        ν[(fun U => ‖A U‖) | shiftInvariantSigma a] := norm_condExp_le A
    have h2 : ν[(fun U => ‖A U‖) | shiftInvariantSigma a] ≤ᵐ[ν]
        ν[(fun _ => C) | shiftInvariantSigma a] :=
      condExp_mono hAint.norm (integrable_const C) (Eventually.of_forall hC)
    rw [condExp_const shiftInvariantSigma_le C] at h2
    filter_upwards [h1, h2] with U h1 h2 using h1.trans h2
  have hmeas : AEStronglyMeasurable (condExpShiftInvariant ν A) ν :=
    (stronglyMeasurable_condExp.mono shiftInvariantSigma_le).aestronglyMeasurable
  have hsq : Integrable (fun U => ‖condExpShiftInvariant ν A U - ∫ V, A V ∂ν‖ ^ 2) ν := by
    refine Integrable.of_bound ((hmeas.sub aestronglyMeasurable_const).norm.pow 2)
      ((C + ‖∫ V, A V ∂ν‖) ^ 2) ?_
    filter_upwards [hbound] with U hU
    have h3 : ‖condExpShiftInvariant ν A U - ∫ V, A V ∂ν‖ ≤ C + ‖∫ V, A V ∂ν‖ :=
      (norm_sub_le _ _).trans (by linarith)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) h3 2
  have hae := (integral_eq_zero_iff_of_nonneg (fun U => by positivity) hsq).mp hzero
  filter_upwards [hae] with U hU
  have h4 : ‖condExpShiftInvariant ν A U - ∫ V, A V ∂ν‖ ^ 2 = 0 := hU
  exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero)|>.mp h4))
theorem setIntegral_eq_integral_mul_measureReal
    (hVar : InfiniteLattice.PlateauVarianceFormula)
    (ha : 0 < a) (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν]
    (hν : IsShiftInvariant ν) {A : GaugeField a → ℂ} (hA : IsBoundedObservable A)
    (h0 : plateauVariance ν A = 0) {I : Set (GaugeField a)}
    (hI : MeasurableSet[shiftInvariantSigma a] I) :
    ∫ U in I, A U ∂ν = (∫ U, A U ∂ν) * ((ν.real I : ℝ) : ℂ) := by
  obtain ⟨C, hC⟩ := hA.2
  have hAint : Integrable A ν :=
    Integrable.of_bound hA.1.aestronglyMeasurable C (Eventually.of_forall hC)
  have h1 : ∫ U in I, condExpShiftInvariant ν A U ∂ν = ∫ U in I, A U ∂ν :=
    setIntegral_condExp shiftInvariantSigma_le hAint hI
  have h2 : ∫ U in I, condExpShiftInvariant ν A U ∂ν = ∫ _ in I, (∫ V, A V ∂ν) ∂ν :=
    integral_congr_ae
      (ae_restrict_of_ae (condExpShiftInvariant_ae_eq_const hVar ha ν hν hA h0))
  rw [← h1, h2, setIntegral_const, Complex.real_smul, mul_comm]
theorem exists_mem_integral_norm_sub_indicator_le [CompactSpace (GaugeField a)]
    [TopologicalSpace.MetrizableSpace (GaugeField a)]
    (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν] {𝒟 : Set (GaugeField a → ℂ)}
    (hsub : 𝒟 ⊆ continuousFns a) (hdense : IsSupNormDense 𝒟)
    {I : Set (GaugeField a)} (hI : MeasurableSet I) {ε : ℝ} (hε : 0 < ε) :
    ∃ A ∈ 𝒟, ∫ U, ‖A U - I.indicator (1 : GaugeField a → ℂ) U‖ ∂ν ≤ 2 * ε := by
  have hf : Integrable (I.indicator (1 : GaugeField a → ℂ)) ν :=
    (integrable_const (1 : ℂ)).indicator hI
  obtain ⟨g, hg, hgi⟩ := hf.exists_boundedContinuous_integral_sub_le hε
  obtain ⟨A, hA, hlt⟩ := hdense g g.continuous ε hε
  have hAc : Continuous A := hsub hA
  have hdiff : Continuous ((g : GaugeField a → ℂ) - A) := g.continuous.sub hAc
  have hpt : ∀ U, ‖A U - g U‖ ≤ ε := fun U => by
    have hb : BddAbove (range fun U => ‖((g : GaugeField a → ℂ) - A) U‖) :=
      (isCompact_range hdiff.norm).bddAbove
    have h1 : ‖((g : GaugeField a → ℂ) - A) U‖ ≤ observableSupNorm ((g : GaugeField a → ℂ) - A) :=
      le_ciSup hb U
    rw [norm_sub_rev]
    exact h1.trans hlt.le
  refine ⟨A, hA, ?_⟩
  have hAint : Integrable A ν :=
    (isBoundedObservable_of_continuous hAc).2.elim fun C hC =>
      Integrable.of_bound hAc.aestronglyMeasurable C (Eventually.of_forall hC)
  have hint1 : Integrable (fun U => ‖A U - I.indicator (1 : GaugeField a → ℂ) U‖) ν :=
    (hAint.sub hf).norm
  have hint2 : Integrable (fun U => ‖I.indicator (1 : GaugeField a → ℂ) U - g U‖ + ε) ν :=
    (hf.sub hgi).norm.add (integrable_const ε)
  calc ∫ U, ‖A U - I.indicator (1 : GaugeField a → ℂ) U‖ ∂ν
      ≤ ∫ U, (‖I.indicator (1 : GaugeField a → ℂ) U - g U‖ + ε) ∂ν := by
        refine integral_mono hint1 hint2 fun U => ?_
        have h1 := norm_sub_le_norm_sub_add_norm_sub (A U) (g U)
          (I.indicator (1 : GaugeField a → ℂ) U)
        have h2 := hpt U
        have h3 : ‖g U - I.indicator (1 : GaugeField a → ℂ) U‖ =
            ‖I.indicator (1 : GaugeField a → ℂ) U - g U‖ := norm_sub_rev _ _
        simp only
        linarith
    _ = (∫ U, ‖I.indicator (1 : GaugeField a → ℂ) U - g U‖ ∂ν) + ε := by
        have hn : Integrable (fun U => ‖I.indicator (1 : GaugeField a → ℂ) U - g U‖) ν :=
          (hf.sub hgi).norm
        rw [integral_add hn (integrable_const ε)]
        simp
    _ ≤ 2 * ε := by linarith
theorem ergodicOfVanishingPlateauVariance
    (hTop : SpacesOfFieldsAndMeasures.FieldAndMeasureSpaceProperties)
    (hVar : InfiniteLattice.PlateauVarianceFormula)
    (ha : 0 < a) : ErgodicOfVanishingPlateauVariance a := by
  intro ρ 𝒟 hTI hsub hdense hzero
  obtain ⟨⟨-, hcomp, hmet⟩, -⟩ := hTop a ha
  have := hcomp
  have := hmet
  have : IsProbabilityMeasure ρ.1 := ρ.2
  refine ⟨ρ.2, hTI, fun I hI => ?_⟩
  have hIm : MeasurableSet I := hI.1
  obtain ⟨hp0, hp1⟩ : 0 ≤ ρ.1.real I ∧ ρ.1.real I ≤ 1 := ⟨measureReal_nonneg, measureReal_le_one⟩
  have hf : Integrable (I.indicator (1 : GaugeField a → ℂ)) ρ.1 :=
    (integrable_const (1 : ℂ)).indicator hIm
  have hfint : ∫ U, I.indicator (1 : GaugeField a → ℂ) U ∂ρ.1 = ((ρ.1.real I : ℝ) : ℂ) := by
    rw [integral_indicator hIm]
    simp
  have hsmall : ∀ ε : ℝ, 0 < ε → |ρ.1.real I * ρ.1.real I - ρ.1.real I| ≤ 4 * ε := by
    intro ε hε
    obtain ⟨A, hA, hnear⟩ := exists_mem_integral_norm_sub_indicator_le ρ.1 hsub hdense hIm hε
    have hAc : Continuous A := hsub hA
    have hAo : IsBoundedObservable A := isBoundedObservable_of_continuous hAc
    have hAint : Integrable A ρ.1 :=
      hAo.2.elim fun C hC =>
        Integrable.of_bound hAc.aestronglyMeasurable C (Eventually.of_forall hC)
    have hprod := setIntegral_eq_integral_mul_measureReal hVar ha ρ.1 hTI hAo (hzero A hA) hI
    have hdint : Integrable (fun U => ‖A U - I.indicator (1 : GaugeField a → ℂ) U‖) ρ.1 :=
      (hAint.sub hf).norm
    have h1 : ‖(∫ U, A U ∂ρ.1) - ((ρ.1.real I : ℝ) : ℂ)‖ ≤ 2 * ε := by
      rw [← hfint, ← integral_sub hAint hf]
      exact (norm_integral_le_integral_norm _).trans hnear
    have h2 : ‖(∫ U in I, A U ∂ρ.1) - ((ρ.1.real I : ℝ) : ℂ)‖ ≤ 2 * ε := by
      have he : ((ρ.1.real I : ℝ) : ℂ) = ∫ U in I, I.indicator (1 : GaugeField a → ℂ) U ∂ρ.1 := by
        rw [← hfint, integral_indicator hIm, setIntegral_indicator hIm]
        simp
      rw [he, ← integral_sub hAint.integrableOn hf.integrableOn]
      refine (norm_integral_le_integral_norm _).trans (le_trans ?_ hnear)
      exact setIntegral_le_integral hdint (Eventually.of_forall fun U => norm_nonneg _)
    rw [hprod] at h2
    have h4 : ‖((ρ.1.real I : ℝ) : ℂ) * ((ρ.1.real I : ℝ) : ℂ) - ((ρ.1.real I : ℝ) : ℂ)‖ ≤ 4 * ε := by
      have h5 : ((ρ.1.real I : ℝ) : ℂ) * ((ρ.1.real I : ℝ) : ℂ) - ((ρ.1.real I : ℝ) : ℂ) =
          ((∫ U, A U ∂ρ.1) * ((ρ.1.real I : ℝ) : ℂ) - ((ρ.1.real I : ℝ) : ℂ)) -
            ((∫ U, A U ∂ρ.1) - ((ρ.1.real I : ℝ) : ℂ)) * ((ρ.1.real I : ℝ) : ℂ) := by ring
      rw [h5]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hp0]
      nlinarith [norm_nonneg ((∫ U, A U ∂ρ.1) - ((ρ.1.real I : ℝ) : ℂ))]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h4
    exact h4
  have hfix : ρ.1.real I * ρ.1.real I - ρ.1.real I = 0 := by
    by_contra hne
    have hpos := abs_pos.mpr hne
    have := hsmall (|ρ.1.real I * ρ.1.real I - ρ.1.real I| / 8) (by positivity)
    linarith
  have hcases : ρ.1.real I = 0 ∨ ρ.1.real I = 1 := by
    have : ρ.1.real I * (ρ.1.real I - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases hcases with h | h
  · left
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp h
  · right
    have h' : (ρ.1 I).toReal = 1 := h
    exact (ENNReal.toReal_eq_one_iff _).mp h'
theorem statement_holds (hAct : LatticeSymmetryActionOnFields)
    (hTop : SpacesOfFieldsAndMeasures.FieldAndMeasureSpaceProperties)
    (hFull : FullReflectionPositivityFromContinuousLocal.Statement)
    (hVar : InfiniteLattice.PlateauVarianceFormula) :
    Statement := fun _ ha =>
  ⟨symmetryClosedUnderWeakLimits hAct hTop ha, reflectionPositivityFromContinuous hFull ha,
    invariantMeasurable_pointwiseInvariant, ergodicOfVanishingPlateauVariance hTop hVar ha⟩
end YangMills.Construction.GibbsAtFixedSpacing.LimitsAndErgodicity
