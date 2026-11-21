import YangMills.Construction.InfiniteLattice.ConditionalExpectationGivenTheInvariantField
import YangMills.Construction.InfiniteLattice.ReflectionFormAndTransferOperatorOfAPeriodicGibbsStateProof
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.LatticePhases.CondExpInvariant
variable {a : ℝ} {ρ : Measure (GaugeField a)} [IsProbabilityMeasure ρ]
  {A B Y Y' J : GaugeField a → ℂ}
theorem shiftInvariantSigma_le_borel :
    shiftInvariantSigma a ≤ (inferInstance : MeasurableSpace (GaugeField a)) :=
  fun I hI => (show IsShiftInvariantSet I from hI).1
omit [IsProbabilityMeasure ρ] in
theorem zero_le_supNorm (A : GaugeField a → ℂ) : 0 ≤ observableSupNorm A :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem norm_apply_le_supNorm (hA : IsBoundedObservable A) (U : GaugeField a) :
    ‖A U‖ ≤ observableSupNorm A := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.norm_le_supNorm <;> assumption
theorem integrable_of_isBoundedObservable (hA : IsBoundedObservable A) : Integrable A ρ := by apply _root_.YangMills.Construction.InfiniteLattice.ReflectionPairingProof.integrable_of_isBoundedObservable <;> assumption
omit [IsProbabilityMeasure ρ] in
theorem integrable_of_isCondExpVersion (hY : IsIntegrableCondExpRepresentative ρ A Y) :
    Integrable Y ρ :=
  ⟨(hY.1.mono shiftInvariantSigma_le_borel le_rfl).aestronglyMeasurable, hY.2.1⟩
omit [IsProbabilityMeasure ρ] in
theorem integrable_mul_of_bounded_measurable {C : ℝ} (hJ : Measurable[shiftInvariantSigma a] J)
    (hC : ∀ U, ‖J U‖ ≤ C) (hY : Integrable Y ρ) : Integrable (fun U => J U * Y U) ρ := by
  refine (hY.norm.const_mul C).mono'
    ((hJ.mono shiftInvariantSigma_le_borel le_rfl).aestronglyMeasurable.mul hY.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun U => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC U) (norm_nonneg _)
theorem condExpShiftInvariant_isRepresentative (hA : Integrable A ρ) :
    IsIntegrableCondExpRepresentative ρ A (condExpShiftInvariant ρ A) := by
  refine ⟨(stronglyMeasurable_condExp (m := shiftInvariantSigma a)).measurable,
    (integrable_condExp (m := shiftInvariantSigma a)).2, ?_⟩
  rintro J hJ ⟨C, hC⟩
  have hJA : Integrable (fun U => J U * A U) ρ := integrable_mul_of_bounded_measurable hJ hC hA
  have hpull := condExp_bilin_of_stronglyMeasurable_left (μ := ρ) (m := shiftInvariantSigma a)
    (ContinuousLinearMap.mul ℝ ℂ) hJ.stronglyMeasurable hJA hA
  have hint := integral_condExp (μ := ρ) (f := fun U => J U * A U) shiftInvariantSigma_le_borel
  calc ∫ U, J U * condExpShiftInvariant ρ A U ∂ρ
      = ∫ U, (ρ[fun U => J U * A U | shiftInvariantSigma a]) U ∂ρ :=
        (integral_congr_ae hpull).symm
    _ = ∫ U, J U * A U ∂ρ := hint
theorem representative_ae_eq_condExp (hA : Integrable A ρ)
    (hY : IsIntegrableCondExpRepresentative ρ A Y) :
    Y =ᵐ[ρ] condExpShiftInvariant ρ A := by
  refine ae_eq_condExp_of_forall_setIntegral_eq shiftInvariantSigma_le_borel hA
    (fun s _ _ => (integrable_of_isCondExpVersion hY).integrableOn) (fun s hs _ => ?_)
    hY.1.stronglyMeasurable.aestronglyMeasurable
  have hind : ∀ f : GaugeField a → ℂ,
      ∫ U, s.indicator (fun _ => (1 : ℂ)) U * f U ∂ρ = ∫ U in s, f U ∂ρ := by
    intro f
    rw [← integral_indicator (shiftInvariantSigma_le_borel s hs)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    by_cases h : U ∈ s <;> simp [h]
  have hJ : Measurable[shiftInvariantSigma a] (s.indicator fun _ => (1 : ℂ)) :=
    measurable_const.indicator hs
  have hb : ∀ U, ‖s.indicator (fun _ => (1 : ℂ)) U‖ ≤ 1 := by
    intro U
    by_cases h : U ∈ s <;> simp [h]
  have := hY.2.2 _ hJ ⟨1, hb⟩
  rwa [hind, hind] at this
theorem representative_ae_eq_representative (hA : Integrable A ρ)
    (hY : IsIntegrableCondExpRepresentative ρ A Y)
    (hY' : IsIntegrableCondExpRepresentative ρ A Y') : Y =ᵐ[ρ] Y' :=
  (representative_ae_eq_condExp hA hY).trans (representative_ae_eq_condExp hA hY').symm
omit [IsProbabilityMeasure ρ] in
theorem isCondExp_congr_ae (hY : IsIntegrableCondExpRepresentative ρ A Y)
    (hm : Measurable[shiftInvariantSigma a] Y') (h : Y =ᵐ[ρ] Y') :
    IsIntegrableCondExpRepresentative ρ A Y' := by
  refine ⟨hm, hY.2.1.congr h, fun J hJ hb => ?_⟩
  rw [← hY.2.2 J hJ hb]
  exact integral_congr_ae (h.mono fun U hU => by simp [hU])
theorem ae_norm_representative_le (hA : IsBoundedObservable A)
    (hY : IsIntegrableCondExpRepresentative ρ A Y) :
    ∀ᵐ U ∂ρ, ‖Y U‖ ≤ observableSupNorm A := by
  have hAi : Integrable A ρ := integrable_of_isBoundedObservable hA
  have h1 := representative_ae_eq_condExp hAi hY
  have h2 : (fun U => ‖condExpShiftInvariant ρ A U‖) ≤ᵐ[ρ]
      ρ[(fun U => ‖A U‖) | shiftInvariantSigma a] := norm_condExp_le A
  have h3 : ρ[(fun U => ‖A U‖) | shiftInvariantSigma a] ≤ᵐ[ρ]
      ρ[(fun _ => observableSupNorm A) | shiftInvariantSigma a] :=
    condExp_mono hAi.norm (integrable_const _)
      (Filter.Eventually.of_forall (norm_apply_le_supNorm hA))
  rw [condExp_const shiftInvariantSigma_le_borel] at h3
  filter_upwards [h1, h2, h3] with U e1 e2 e3
  rw [e1]
  exact e2.trans e3
theorem integral_norm_version_le (hA : Integrable A ρ)
    (hY : IsIntegrableCondExpRepresentative ρ A Y) :
    ∫ U, ‖Y U‖ ∂ρ ≤ ∫ U, ‖A U‖ ∂ρ := by
  have h1 := representative_ae_eq_condExp hA hY
  have h2 : (fun U => ‖condExpShiftInvariant ρ A U‖) ≤ᵐ[ρ]
      ρ[(fun U => ‖A U‖) | shiftInvariantSigma a] := norm_condExp_le A
  calc ∫ U, ‖Y U‖ ∂ρ ≤ ∫ U, (ρ[(fun U => ‖A U‖) | shiftInvariantSigma a]) U ∂ρ := by
        refine integral_mono_ae (integrable_of_isCondExpVersion hY).norm integrable_condExp ?_
        filter_upwards [h1, h2] with U e1 e2
        rw [e1]
        exact e2
    _ = ∫ U, ‖A U‖ ∂ρ := integral_condExp shiftInvariantSigma_le_borel
theorem exists_representative_norm_le (hA : IsBoundedObservable A) :
    ∃ Y, IsIntegrableCondExpRepresentative ρ A Y ∧ ∀ U, ‖Y U‖ ≤ observableSupNorm A := by
  have hE := condExpShiftInvariant_isRepresentative (ρ := ρ) (integrable_of_isBoundedObservable hA)
  set S : Set (GaugeField a) := {U | ‖condExpShiftInvariant ρ A U‖ ≤ observableSupNorm A}
    with hSdef
  have hmem : ∀ U, U ∈ S ↔ ‖condExpShiftInvariant ρ A U‖ ≤ observableSupNorm A :=
    fun _ => Iff.rfl
  have hS : MeasurableSet[shiftInvariantSigma a] S :=
    measurableSet_le (continuous_norm.measurable.comp hE.1) measurable_const
  refine ⟨S.indicator (condExpShiftInvariant ρ A),
    isCondExp_congr_ae hE (hE.1.indicator hS) ?_, fun U => ?_⟩
  · filter_upwards [ae_norm_representative_le hA hE] with U hU
    rw [Set.indicator_of_mem ((hmem U).2 hU)]
  · by_cases h : U ∈ S
    · rw [Set.indicator_of_mem h]
      exact (hmem U).1 h
    · rw [Set.indicator_of_notMem h, norm_zero]
      exact zero_le_supNorm A
omit [IsProbabilityMeasure ρ] in
theorem conj_representative
    (hY : IsIntegrableCondExpRepresentative ρ A Y) :
    IsIntegrableCondExpRepresentative ρ (fun U => conj (A U)) (fun U => conj (Y U)) := by
  refine ⟨Complex.continuous_conj.measurable.comp hY.1,
    (Complex.conjCLE.toContinuousLinearMap.integrable_comp
      (integrable_of_isCondExpVersion hY)).2, ?_⟩
  rintro J hJ ⟨C, hC⟩
  have h := hY.2.2 (fun U => conj (J U)) (Complex.continuous_conj.measurable.comp hJ)
    ⟨C, fun U => by simpa using hC U⟩
  calc ∫ U, J U * conj (Y U) ∂ρ = ∫ U, conj (conj (J U) * Y U) ∂ρ := by simp
    _ = conj (∫ U, conj (J U) * Y U ∂ρ) := integral_conj
    _ = conj (∫ U, conj (J U) * A U ∂ρ) := by rw [h]
    _ = ∫ U, conj (conj (J U) * A U) ∂ρ := integral_conj.symm
    _ = ∫ U, J U * conj (A U) ∂ρ := by simp
omit [IsProbabilityMeasure ρ] in
theorem add_smul_representative (hA : Integrable A ρ) (hB : Integrable B ρ)
    (hY : IsIntegrableCondExpRepresentative ρ A Y)
    (hY' : IsIntegrableCondExpRepresentative ρ B Y') (z : ℂ) :
    IsIntegrableCondExpRepresentative ρ (fun U => A U + z * B U)
      (fun U => Y U + z * Y' U) := by
  have iY := integrable_of_isCondExpVersion hY
  have iY' := integrable_of_isCondExpVersion hY'
  refine ⟨hY.1.add (hY'.1.const_mul z), (iY.add (iY'.const_mul z)).2, ?_⟩
  rintro J hJ ⟨C, hC⟩
  have hsplit : ∀ f g : GaugeField a → ℂ, Integrable f ρ → Integrable g ρ →
      ∫ U, J U * (f U + z * g U) ∂ρ = ∫ U, J U * f U ∂ρ + z * ∫ U, J U * g U ∂ρ := by
    intro f g hf hg
    have hfun : (fun U => J U * (f U + z * g U)) = fun U => J U * f U + z * (J U * g U) := by
      funext U
      ring
    rw [hfun, integral_add (integrable_mul_of_bounded_measurable hJ hC hf)
      ((integrable_mul_of_bounded_measurable hJ hC hg).const_mul z), integral_const_mul]
  rw [hsplit Y Y' iY iY', hsplit A B hA hB, hY.2.2 J hJ ⟨C, hC⟩, hY'.2.2 J hJ ⟨C, hC⟩]
theorem exists_real_representative_norm_le (hA : IsBoundedObservable A) (hreal : IsRealValued A) :
    ∃ Y, IsIntegrableCondExpRepresentative ρ A Y ∧ (∀ U, ‖Y U‖ ≤ observableSupNorm A) ∧
      IsRealValued Y := by
  have hAi : Integrable A ρ := integrable_of_isBoundedObservable hA
  obtain ⟨Y, hY, hb⟩ := exists_representative_norm_le (ρ := ρ) hA
  have hconjA : (fun U => conj (A U)) = A := by
    funext U
    exact Complex.conj_eq_iff_im.mpr (hreal U)
  have hc := conj_representative hY
  rw [hconjA] at hc
  have hae := representative_ae_eq_representative hAi hY hc
  refine ⟨fun U => ((Y U).re : ℂ), isCondExp_congr_ae hY
    (Complex.measurable_ofReal.comp (Complex.measurable_re.comp hY.1)) ?_, fun U => ?_,
    fun U => Complex.ofReal_im _⟩
  · filter_upwards [hae] with U hU
    have him : (Y U).im = 0 := Complex.conj_eq_iff_im.mp hU.symm
    exact Complex.ext (by simp) (by simp [him])
  · rw [Complex.norm_real, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (hb U)
theorem integrable_mul_of_ae_norm_le {F G : GaugeField a → ℂ} {C C' : ℝ}
    (hF : AEStronglyMeasurable F ρ) (hG : AEStronglyMeasurable G ρ)
    (hFC : ∀ᵐ U ∂ρ, ‖F U‖ ≤ C) (hGC : ∀ᵐ U ∂ρ, ‖G U‖ ≤ C') (hC : 0 ≤ C) :
    Integrable (fun U => F U * G U) ρ := by
  refine Integrable.of_bound (hF.mul hG) (C * C') ?_
  filter_upwards [hFC, hGC] with U h1 h2
  rw [norm_mul]
  exact mul_le_mul h1 h2 (norm_nonneg _) hC
theorem plateauRepresentativeIndependent_holds (hA : IsBoundedObservable A)
    (hB : IsBoundedObservable B) : PlateauIndependentOfRepresentative ρ A B := by
  have hAi : Integrable A ρ := integrable_of_isBoundedObservable hA
  have hBi : Integrable B ρ := integrable_of_isBoundedObservable hB
  have hEA := condExpShiftInvariant_isRepresentative hAi
  have hEB := condExpShiftInvariant_isRepresentative hBi
  have hnA := zero_le_supNorm A
  have hconjmeas : ∀ {F : GaugeField a → ℂ}, AEStronglyMeasurable F ρ →
      AEStronglyMeasurable (fun U => conj (F U)) ρ := fun hF =>
    Complex.continuous_conj.comp_aestronglyMeasurable hF
  refine ⟨hAi, fun Y Y' hY hY' => ⟨?_, ?_⟩, ?_, fun Y' hY' => ⟨?_, ?_⟩⟩
  · exact integrable_mul_of_ae_norm_le (hconjmeas (integrable_of_isCondExpVersion hY).1)
      (integrable_of_isCondExpVersion hY').1
      ((ae_norm_representative_le hA hY).mono fun U hU => by simpa using hU)
      (ae_norm_representative_le hB hY') hnA
  · refine integral_congr_ae ?_
    filter_upwards [representative_ae_eq_condExp hAi hY, representative_ae_eq_condExp hBi hY']
      with U e1 e2
    rw [e1, e2]
  · have hb : ∀ᵐ U ∂ρ, ‖conj (condExpShiftInvariant ρ A U) * condExpShiftInvariant ρ B U‖ ≤
        observableSupNorm A * observableSupNorm B := by
      filter_upwards [ae_norm_representative_le hA hEA, ae_norm_representative_le hB hEB] with U h1 h2
      rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul h1 h2 (norm_nonneg _) hnA
    have := norm_integral_le_of_norm_le_const hb
    simpa [plateauPairing] using this
  · exact integrable_mul_of_ae_norm_le (hconjmeas hAi.1) (integrable_of_isCondExpVersion hY').1
      (Filter.Eventually.of_forall fun U => by simpa using norm_apply_le_supNorm hA U)
      (ae_norm_representative_le hB hY') hnA
  · obtain ⟨W, hW, hWb⟩ := exists_representative_norm_le (ρ := ρ) hB
    have htest := (conj_representative hEA).2.2 W hW.1 ⟨_, hWb⟩
    have hWE := representative_ae_eq_condExp hBi hW
    have hWY := representative_ae_eq_representative hBi hW hY'
    calc plateauPairing ρ A B = ∫ U, W U * conj (condExpShiftInvariant ρ A U) ∂ρ := by
          refine integral_congr_ae ?_
          filter_upwards [hWE] with U e
          rw [e, mul_comm]
      _ = ∫ U, W U * conj (A U) ∂ρ := htest
      _ = ∫ U, conj (A U) * Y' U ∂ρ := by
          refine integral_congr_ae ?_
          filter_upwards [hWY] with U e
          rw [e, mul_comm]
theorem claim_holds : Claim := by
  intro D ρ _ _ A B hA hB
  have hAi : Integrable A ρ := integrable_of_isBoundedObservable hA
  have hBi : Integrable B ρ := integrable_of_isBoundedObservable hB
  have hE := condExpShiftInvariant_isRepresentative hAi
  refine ⟨⟨⟨_, hE⟩, hE, fun Y Y' hY hY' => representative_ae_eq_representative hAi hY hY',
    fun Y hY => ae_norm_representative_le hA hY, exists_representative_norm_le hA,
    exists_real_representative_norm_le hA⟩,
    fun Y Y' hY hY' => ⟨add_smul_representative hAi hBi hY hY', conj_representative hY⟩,
    fun Y hY => ⟨?_, integral_norm_version_le hAi hY⟩, ?_, plateauRepresentativeIndependent_holds hA hB⟩
  · obtain ⟨hm, -, htest⟩ := hY
    simpa using htest (fun _ => 1) measurable_const ⟨1, by simp⟩
  · rintro J hJ ⟨C, hC⟩
    refine ⟨hJ, (Integrable.of_bound
      (hJ.mono shiftInvariantSigma_le_borel le_rfl).aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)).2, fun _ _ _ => rfl⟩
end YangMills.Construction.LatticePhases.CondExpInvariant
end
