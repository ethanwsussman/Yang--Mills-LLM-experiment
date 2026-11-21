import YangMills.Construction.ReflectionPositivity.OneSideAndOneTranslationProof
import YangMills.Construction.InfiniteLattice.ContinuousObservablesAndTheWilsonKernelOfACutoff
import YangMills.Construction.InfiniteLattice.FromADenseFamilyToAllBoundedBorelFunctions
import YangMills.Construction.InfiniteLattice.ReflectionFormAndTransferOperatorOfAPeriodicGibbsStateProof
import YangMills.Construction.InfiniteLattice.RegularConditionalProbabilitiesExistAndAreMeasurable
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter ProbabilityTheory
open YangMills.Construction.InfiniteLattice YangMills.Construction.GibbsAtFixedSpacing
open YangMills.Construction.PeriodicGibbsStateSpace.DenseLocalFamily
open YangMills.Construction.PeriodicGibbsStateSpace.DenseToBorel
open scoped Topology ComplexConjugate
noncomputable section
namespace YangMills.Construction.PeriodicGibbsStateSpace.ConditionalMeasurability
variable {a : ℝ}
theorem integrable_of_isBoundedObservable {ν : Measure (GaugeField a)} [IsProbabilityMeasure ν]
    {A : GaugeField a → ℂ} (hA : IsBoundedObservable A) : Integrable A ν := by apply _root_.YangMills.Construction.InfiniteLattice.ReflectionPairingProof.integrable_of_isBoundedObservable <;> assumption
theorem norm_integral_le_of_bound (ρ : BorelProb a) {A : GaugeField a → ℂ} {C : ℝ}
    (hC : ∀ U, ‖A U‖ ≤ C) : ‖ρ.integral A‖ ≤ C := by apply _root_.YangMills.DeltaSharedProofs.p501847 <;> assumption
theorem integral_add_of_bounded (ρ : BorelProb a) {A B : GaugeField a → ℂ}
    (hA : IsBoundedObservable A) (hB : IsBoundedObservable B) :
    ρ.integral (fun U => A U + B U) = ρ.integral A + ρ.integral B := by
  have := ρ.2
  exact integral_add (integrable_of_isBoundedObservable hA) (integrable_of_isBoundedObservable hB)
theorem integral_const_mul_fn (ρ : BorelProb a) (c : ℂ) (A : GaugeField a → ℂ) :
    ρ.integral (fun U => c * A U) = c * ρ.integral A :=
  integral_const_mul c A
def realPartFn (A : GaugeField a → ℂ) : GaugeField a → ℂ := fun U => ((A U).re : ℂ)
def imagPartFn (A : GaugeField a → ℂ) : GaugeField a → ℂ := fun U => ((A U).im : ℂ)
theorem isRealValued_realPartFn (A : GaugeField a → ℂ) : IsRealValued (realPartFn A) :=
  fun U => by simp [realPartFn]
theorem isRealValued_imagPartFn (A : GaugeField a → ℂ) :
    IsRealValued (imagPartFn A) :=
  fun U => by simp [imagPartFn]
theorem isBoundedObservable_realPartFn {A : GaugeField a → ℂ} (hA : IsBoundedObservable A) :
    IsBoundedObservable (realPartFn A) := by
  obtain ⟨C, hC⟩ := hA.2
  refine ⟨Complex.measurable_ofReal.comp (Complex.measurable_re.comp hA.1), C, fun U => ?_⟩
  simpa [realPartFn] using (Complex.abs_re_le_norm (A U)).trans (hC U)
theorem isBoundedObservable_imagPartFn {A : GaugeField a → ℂ} (hA : IsBoundedObservable A) :
    IsBoundedObservable (imagPartFn A) := by
  obtain ⟨C, hC⟩ := hA.2
  refine ⟨Complex.measurable_ofReal.comp (Complex.measurable_im.comp hA.1), C, fun U => ?_⟩
  simpa [imagPartFn] using (Complex.abs_im_le_norm (A U)).trans (hC U)
theorem integral_eq_re_add_I_mul_im (ρ : BorelProb a) {A : GaugeField a → ℂ}
    (hA : IsBoundedObservable A) :
    ρ.integral A = ρ.integral (realPartFn A) + Complex.I * ρ.integral (imagPartFn A) := by
  have hI : IsBoundedObservable (fun U => Complex.I * imagPartFn A U) := by
    obtain ⟨C, hC⟩ := (isBoundedObservable_imagPartFn hA).2
    exact ⟨measurable_const.mul (isBoundedObservable_imagPartFn hA).1, C,
      fun U => by simpa using hC U⟩
  rw [← integral_const_mul_fn,
    ← integral_add_of_bounded ρ (isBoundedObservable_realPartFn hA) hI]
  congr 1
  funext U
  simp only [realPartFn, imagPartFn]
  rw [mul_comm]
  exact (Complex.re_add_im (A U)).symm
theorem continuous_integral_of_isRealValued {𝒟 : Set (GaugeField a → ℂ)} (ha : 0 < a)
    (h𝒟 : IsCountableRealDense 𝒟) (T : TopologicalSpace (BorelProb a))
    (hT : ∀ H ∈ 𝒟, Continuous fun ρ : BorelProb a => ρ.integral H)
    {F : GaugeField a → ℂ} (hF : Continuous F) (hr : IsRealValued F) :
    Continuous fun ρ : BorelProb a => ρ.integral F := by
  obtain ⟨H, hH, hu⟩ := h𝒟.2.2.2.2.2 F hF hr
  have hobs : IsBoundedObservable F :=
    ((CutoffStates.isContinuousBoundedObservable_iff_continuous ha F).2 hF).1
  have hunif : TendstoUniformly (fun n (ρ : BorelProb a) => ρ.integral (H n))
      (fun ρ : BorelProb a => ρ.integral F) atTop := by
    rw [Metric.tendstoUniformly_iff] at hu ⊢
    intro ε hε
    filter_upwards [hu (ε / 2) (half_pos hε)] with n hn ρ
    have hHn : IsBoundedObservable (H n) := (h𝒟.2.1 (hH n)).2.1
    have hneg : IsBoundedObservable (fun U => (-1 : ℂ) * H n U) := by
      obtain ⟨C, hC⟩ := hHn.2
      exact ⟨measurable_const.mul hHn.1, C, fun U => by simpa using hC U⟩
    have hsub : ρ.integral F - ρ.integral (H n) =
        ρ.integral (fun U => F U + (-1 : ℂ) * H n U) := by
      rw [integral_add_of_bounded ρ hobs hneg, integral_const_mul_fn]
      ring
    have hb : ‖ρ.integral (fun U => F U + (-1 : ℂ) * H n U)‖ ≤ ε / 2 := by
      refine norm_integral_le_of_bound ρ fun U => ?_
      have := (hn U).le
      rw [dist_eq_norm] at this
      simpa [sub_eq_add_neg] using this
    rw [dist_eq_norm, hsub]
    linarith
  exact hunif.continuous (Frequently.of_forall fun n => hT _ (hH n))
theorem continuous_integral_of_dense {𝒟 : Set (GaugeField a → ℂ)} (ha : 0 < a)
    (h𝒟 : IsCountableRealDense 𝒟) (T : TopologicalSpace (BorelProb a))
    (hT : ∀ H ∈ 𝒟, Continuous fun ρ : BorelProb a => ρ.integral H)
    {F : GaugeField a → ℂ} (hF : Continuous F) :
    Continuous fun ρ : BorelProb a => ρ.integral F := by
  have hobs : IsBoundedObservable F :=
    ((CutoffStates.isContinuousBoundedObservable_iff_continuous ha F).2 hF).1
  have hre : Continuous (realPartFn F) :=
    Complex.continuous_ofReal.comp (Complex.continuous_re.comp hF)
  have him : Continuous (imagPartFn F) :=
    Complex.continuous_ofReal.comp (Complex.continuous_im.comp hF)
  have h1 := continuous_integral_of_isRealValued ha h𝒟 T hT hre (isRealValued_realPartFn F)
  have h2 := continuous_integral_of_isRealValued ha h𝒟 T hT him (isRealValued_imagPartFn F)
  have : (fun ρ : BorelProb a => ρ.integral F) = fun ρ : BorelProb a =>
      ρ.integral (realPartFn F) + Complex.I * ρ.integral (imagPartFn F) :=
    funext fun ρ => integral_eq_re_add_I_mul_im ρ hobs
  rw [this]
  exact h1.add (continuous_const.mul h2)
def expectationsOn (𝒟 : Set (GaugeField a → ℂ)) (ρ : BorelProb a) : 𝒟 → ℂ :=
  fun F => ρ.integral F.1
theorem continuous_integral_weak {F : GaugeField a → ℂ} (hF : Continuous F) :
    Continuous fun ρ : BorelProb a => ρ.integral F :=
  continuous_iff_le_induced.2 (iInf_le_of_le ⟨F, hF⟩ le_rfl)
theorem weakTopology_eq_induced_expectationsOn {𝒟 : Set (GaugeField a → ℂ)} (ha : 0 < a)
    (h𝒟 : IsCountableRealDense 𝒟) :
    (BorelProb.instTopologicalSpace : TopologicalSpace (BorelProb a)) =
      TopologicalSpace.induced (expectationsOn 𝒟) inferInstance := by
  apply le_antisymm
  · have h : Continuous (expectationsOn 𝒟) :=
      continuous_pi fun F => continuous_integral_weak (h𝒟.2.1 F.2).1
    exact continuous_iff_le_induced.1 h
  · refine le_iInf fun F => ?_
    refine continuous_iff_le_induced.1 ?_
    refine continuous_integral_of_dense ha h𝒟
      (TopologicalSpace.induced (expectationsOn 𝒟) inferInstance) (fun H hH => ?_) F.2
    have h : Continuous fun f : 𝒟 → ℂ => f ⟨H, hH⟩ := continuous_apply _
    exact continuous_def.2 fun s hs => ⟨_, h.isOpen_preimage s hs, rfl⟩
theorem secondCountableTopology_borelProb {𝒟 : Set (GaugeField a → ℂ)} (ha : 0 < a)
    (h𝒟 : IsCountableRealDense 𝒟) : SecondCountableTopology (BorelProb a) := by
  have : Countable 𝒟 := h𝒟.1.to_subtype
  rw [weakTopology_eq_induced_expectationsOn ha h𝒟]
  exact TopologicalSpace.secondCountableTopology_induced _ _ _
theorem borelGeneratedByIntegrals_of_dense {𝒟 : Set (GaugeField a → ℂ)} (ha : 0 < a)
    (h𝒟 : IsCountableRealDense 𝒟) : BorelGeneratedByIntegrals 𝒟 := by
  have : Countable 𝒟 := h𝒟.1.to_subtype
  unfold BorelGeneratedByIntegrals
  have hpi : borel (𝒟 → ℂ) = MeasurableSpace.pi := (BorelSpace.measurable_eq (α := 𝒟 → ℂ)).symm
  have hC : (inferInstance : MeasurableSpace ℂ) = borel ℂ := BorelSpace.measurable_eq
  rw [weakTopology_eq_induced_expectationsOn ha h𝒟, borel_comap, hpi]
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  rw [iSup_subtype]
  simp only [hC]
  rfl
def realBorelWithMeasurableIntegral (a : ℝ) : Set (GaugeField a → ℂ) :=
  {A | A ∈ boundedRealBorel a ∧
    Measurable[borel (BorelProb a)] fun ρ : BorelProb a => ρ.integral A}
theorem isRealSubspace_realBorelWithMeasurableIntegral (a : ℝ) :
    IsRealSubspace (realBorelWithMeasurableIntegral a) := by
  refine ⟨{ carrier := realBorelWithMeasurableIntegral a, add_mem' := ?_, zero_mem' := ?_,
            smul_mem' := ?_ }, rfl⟩
  · rintro A B ⟨⟨hA, hAr⟩, hAm⟩ ⟨⟨hB, hBr⟩, hBm⟩
    obtain ⟨C, hC⟩ := hA.2
    obtain ⟨C', hC'⟩ := hB.2
    have hAB : IsBoundedObservable (A + B) :=
      ⟨hA.1.add hB.1, C + C', fun U => (norm_add_le _ _).trans (add_le_add (hC U) (hC' U))⟩
    refine ⟨⟨hAB, fun U => by simp [hAr U, hBr U]⟩, ?_⟩
    have : (fun ρ : BorelProb a => ρ.integral (A + B)) =
        fun ρ : BorelProb a => ρ.integral A + ρ.integral B :=
      funext fun ρ => integral_add_of_bounded ρ hA hB
    rw [this]
    exact hAm.add hBm
  · have h0 : (fun ρ : BorelProb a => ρ.integral (0 : GaugeField a → ℂ)) = fun _ => 0 := by
      funext ρ
      simp [BorelProb.integral, GaugeFieldProbability.expect]
    refine ⟨⟨⟨measurable_const, 0, fun U => by simp⟩, fun U => by simp⟩, ?_⟩
    rw [h0]
    exact measurable_const
  · rintro c A ⟨⟨hA, hAr⟩, hAm⟩
    obtain ⟨C, hC⟩ := hA.2
    have hcA : IsBoundedObservable (c • A) := by
      refine ⟨hA.1.const_smul c, ‖c‖ * C, fun U => ?_⟩
      rw [Pi.smul_apply, norm_smul]
      exact mul_le_mul_of_nonneg_left (hC U) (norm_nonneg _)
    refine ⟨⟨hcA, fun U => by simp [hAr U]⟩, ?_⟩
    have : (fun ρ : BorelProb a => ρ.integral (c • A)) =
        fun ρ : BorelProb a => (c : ℂ) * ρ.integral A := by
      funext ρ
      rw [← integral_const_mul_fn]
      congr 1
    rw [this]
    exact hAm.const_mul _
theorem isClosedUnderBoundedPointwiseLimits_realBorelWithMeasurableIntegral (a : ℝ) :
    IsClosedUnderBoundedPointwiseLimits (realBorelWithMeasurableIntegral a) := by
  intro F G hF ⟨c, hc⟩ hlim
  have hGm : Measurable G :=
    measurable_of_tendsto_metrizable (fun k => (hF k).1.1.1) (tendsto_pi_nhds.2 hlim)
  have hGb : ∀ U, ‖G U‖ ≤ c := fun U =>
    le_of_tendsto (hlim U).norm (Eventually.of_forall fun k => hc k U)
  have hGo : IsBoundedObservable G := ⟨hGm, c, hGb⟩
  have hGr : IsRealValued G := fun U => by
    have h := (Complex.continuous_im.tendsto _).comp (hlim U)
    exact tendsto_nhds_unique h (by
      have : (Complex.im ∘ fun k => F k U) = fun _ => (0 : ℝ) := funext fun k => (hF k).1.2 U
      rw [this]
      exact tendsto_const_nhds)
  refine ⟨⟨hGo, hGr⟩, ?_⟩
  let : MeasurableSpace (BorelProb a) := borel (BorelProb a)
  have : BorelSpace (BorelProb a) := ⟨rfl⟩
  refine measurable_of_tendsto_metrizable (f := fun k (ρ : BorelProb a) => ρ.integral (F k))
    (fun k => (hF k).2) (tendsto_pi_nhds.2 fun ρ => ?_)
  have := ρ.2
  exact tendsto_integral_of_dominated_convergence (fun _ => c)
    (fun k => (hF k).1.1.1.aestronglyMeasurable) (integrable_const c)
    (fun k => ae_of_all _ (hc k)) (ae_of_all _ hlim)
theorem observableIntegralsMeasurable_of_dense (h : DenseFamilyDeterminesBorel)
    (D : Params) {𝒟 : Set (GaugeField D.mesh → ℂ)} (h𝒟 : IsCountableRealDense 𝒟) :
    ObservableIntegralsMeasurable D.mesh := by
  have hM : realBorelWithMeasurableIntegral D.mesh = boundedRealBorel D.mesh := by
    refine (h D 𝒟 h𝒟).1 _ (fun A hA => hA.1) (fun F hF => ?_)
      (isRealSubspace_realBorelWithMeasurableIntegral D.mesh)
      (isClosedUnderBoundedPointwiseLimits_realBorelWithMeasurableIntegral D.mesh)
    refine ⟨⟨(h𝒟.2.1 hF).2.1, h𝒟.2.2.1 F hF⟩, ?_⟩
    let : MeasurableSpace (BorelProb D.mesh) := borel (BorelProb D.mesh)
    have : BorelSpace (BorelProb D.mesh) := ⟨rfl⟩
    exact (continuous_integral_weak (h𝒟.2.1 hF).1).measurable
  intro A hA
  have hre : realPartFn A ∈ realBorelWithMeasurableIntegral D.mesh := by
    rw [hM]
    exact ⟨isBoundedObservable_realPartFn hA, isRealValued_realPartFn A⟩
  have him : imagPartFn A ∈ realBorelWithMeasurableIntegral D.mesh := by
    rw [hM]
    exact ⟨isBoundedObservable_imagPartFn hA, isRealValued_imagPartFn A⟩
  have : (fun ρ : BorelProb D.mesh => ρ.integral A) = fun ρ : BorelProb D.mesh =>
      ρ.integral (realPartFn A) + Complex.I * ρ.integral (imagPartFn A) :=
    funext fun ρ => integral_eq_re_add_I_mul_im ρ hA
  rw [this]
  exact hre.2.add (him.2.const_mul _)
theorem preimagesShiftInvariant_of_dense {𝒟 : Set (GaugeField a → ℂ)} (ha : 0 < a)
    (h𝒟 : IsCountableRealDense 𝒟) {κ : GaugeField a → GaugeFieldProbability a}
    (hκ : ∀ F ∈ 𝒟, Measurable[shiftInvariantSigma a] fun U => (κ U).expect F) :
    PreimagesShiftInvariant κ := by
  intro E hE
  have hB : borel (BorelProb a) =
      ⨆ F ∈ 𝒟, MeasurableSpace.comap (fun ρ : BorelProb a => ρ.integral F) (borel ℂ) :=
    borelGeneratedByIntegrals_of_dense ha h𝒟
  rw [hB] at hE
  have hle : (⨆ F ∈ 𝒟, MeasurableSpace.comap (fun ρ : BorelProb a => ρ.integral F) (borel ℂ)) ≤
      MeasurableSpace.map (fun U => (κ U : BorelProb a)) (shiftInvariantSigma a) := by
    refine iSup₂_le fun F hF s hs => ?_
    obtain ⟨t, ht, rfl⟩ := hs
    exact hκ F hF ht
  exact hle E hE
theorem norm_expect_family_le {κ : GaugeField a → GaugeFieldProbability a}
    {F : GaugeField a → ℂ} {C : ℝ} (hC : ∀ U, ‖F U‖ ≤ C) (U : GaugeField a) :
    ‖(κ U).expect F‖ ≤ C :=
  norm_integral_le_of_bound (κ U : BorelProb a) hC
theorem ae_expect_eq_of_isInvariantDisintegration {ν : Measure (GaugeField a)}
    [IsProbabilityMeasure ν] {κ κ' : GaugeField a → GaugeFieldProbability a}
    (hκ : IsRegularConditionalByIntegrals ν κ)
    (hκ' : IsRegularConditionalByIntegrals ν κ')
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    ∀ᵐ U ∂ν, (κ U).expect F = (κ' U).expect F := by
  obtain ⟨C, hC⟩ := hF.2
  obtain ⟨hm, hi⟩ := hκ F hF
  obtain ⟨hm', hi'⟩ := hκ' F hF
  set d : GaugeField a → ℂ := fun U => (κ U).expect F - (κ' U).expect F with hd
  have hdm : Measurable[shiftInvariantSigma a] d := hm.sub hm'
  have hdb : ∀ U, ‖d U‖ ≤ C + C := fun U =>
    (norm_sub_le _ _).trans
      (add_le_add (norm_expect_family_le hC U) (norm_expect_family_le hC U))
  have hle : shiftInvariantSigma a ≤ (inferInstance : MeasurableSpace (GaugeField a)) :=
    fun _ h => h.1
  have hJm : Measurable[shiftInvariantSigma a] fun U => conj (d U) :=
    Complex.continuous_conj.measurable.comp hdm
  have hJb : ∃ C' : ℝ, ∀ U, ‖conj (d U)‖ ≤ C' := ⟨C + C, fun U => by simpa using hdb U⟩
  have hgo : IsBoundedObservable fun U => (κ U).expect F :=
    ⟨hm.mono hle le_rfl, C, norm_expect_family_le hC⟩
  have hgo' : IsBoundedObservable fun U => (κ' U).expect F :=
    ⟨hm'.mono hle le_rfl, C, norm_expect_family_le hC⟩
  have hJo : IsBoundedObservable fun U => conj (d U) :=
    ⟨hJm.mono hle le_rfl, hJb⟩
  have hprod : ∀ {g : GaugeField a → ℂ}, IsBoundedObservable g →
      Integrable (fun U => conj (d U) * g U) ν := fun {g} hg => by
    obtain ⟨Cg, hCg⟩ := hg.2
    obtain ⟨CJ, hCJ⟩ := hJb
    refine Integrable.of_bound (hJo.1.mul hg.1).aestronglyMeasurable (CJ * Cg)
      (ae_of_all _ fun U => ?_)
    rw [norm_mul]
    exact mul_le_mul (hCJ U) (hCg U) (norm_nonneg _) ((norm_nonneg _).trans (hCJ U))
  have h0 : ∫ U, conj (d U) * d U ∂ν = 0 := by
    have : (fun U => conj (d U) * d U) = fun U =>
        conj (d U) * (κ U).expect F - conj (d U) * (κ' U).expect F := by
      funext U
      simp only [hd]
      ring
    rw [this, integral_sub (hprod hgo) (hprod hgo'), hi _ hJm hJb, hi' _ hJm hJb, sub_self]
  have hreal : ∫ U, ‖d U‖ ^ 2 ∂ν = 0 := by
    have h1 : (fun U => conj (d U) * d U) = fun U => (((‖d U‖ ^ 2 : ℝ)) : ℂ) := by
      funext U
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [h1, integral_complex_ofReal] at h0
    exact_mod_cast h0
  have hint : Integrable (fun U => ‖d U‖ ^ 2) ν := by
    refine Integrable.of_bound
      ((hgo.1.sub hgo'.1).norm.pow_const 2).aestronglyMeasurable ((C + C) ^ 2)
      (ae_of_all _ fun U => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hdb U) 2
  have hae := (integral_eq_zero_iff_of_nonneg (fun U => by positivity) hint).1 hreal
  filter_upwards [hae] with U hU
  have : ‖d U‖ = 0 := by simpa using hU
  exact sub_eq_zero.1 (norm_eq_zero.1 this)
theorem exists_isInvariantDisintegration (ha : 0 < a) (ν : Measure (GaugeField a))
    [IsProbabilityMeasure ν] : ∃ κ, IsRegularConditionalByIntegrals ν κ := by
  have hcm := CutoffStates.compactSpace_and_metrizableSpace_gaugeField ha
  have := hcm.1
  have := hcm.2
  let := TopologicalSpace.metrizableSpaceMetric (GaugeField a)
  have : PolishSpace (GaugeField a) := inferInstance
  have : StandardBorelSpace (GaugeField a) := inferInstance
  have hle : shiftInvariantSigma a ≤ (inferInstance : MeasurableSpace (GaugeField a)) :=
    fun _ h => h.1
  refine ⟨fun U => ⟨condExpKernel ν (shiftInvariantSigma a) U, inferInstance⟩,
    fun F hF => ⟨?_, ?_⟩⟩
  · exact (hF.1.stronglyMeasurable.integral_condExpKernel (μ := ν)
      (m := shiftInvariantSigma a)).measurable
  · intro J hJ ⟨C, hC⟩
    have hFi : Integrable F ν := integrable_of_isBoundedObservable hF
    have hJo : IsBoundedObservable J := ⟨hJ.mono hle le_rfl, C, hC⟩
    have hJF : Integrable (fun U => J U * F U) ν := by
      obtain ⟨C', hC'⟩ := hF.2
      refine Integrable.of_bound (hJo.1.mul hF.1).aestronglyMeasurable (C * C')
        (ae_of_all _ fun U => ?_)
      rw [norm_mul]
      exact mul_le_mul (hC U) (hC' U) (norm_nonneg _) ((norm_nonneg _).trans (hC U))
    have hce := condExp_ae_eq_integral_condExpKernel (μ := ν) hle hFi
    have hpull : ν[fun U => J U * F U | shiftInvariantSigma a] =ᵐ[ν]
        fun U => J U * (ν[F | shiftInvariantSigma a]) U :=
      condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ)
        hJ.stronglyMeasurable hJF hFi
    calc ∫ U, J U * ∫ y, F y ∂(condExpKernel ν (shiftInvariantSigma a) U) ∂ν
        = ∫ U, (ν[fun U => J U * F U | shiftInvariantSigma a]) U ∂ν := by
          refine integral_congr_ae ?_
          filter_upwards [hce, hpull] with U h1 h2
          rw [h2, h1]
      _ = ∫ U, J U * F U ∂ν := integral_condExp hle
theorem existenceAndMeasurability_holds (h₁ : denseFamilyStatement)
    (h₂ : DenseFamilyDeterminesBorel) : ExistenceAndMeasurability := by
  intro D ν hν 𝒟 h𝒟
  have : IsProbabilityMeasure ν := hν.1.1
  have ha : 0 < D.mesh := D.mesh_pos
  refine ⟨exists_isInvariantDisintegration ha ν,
    ⟨secondCountableTopology_borelProb ha h𝒟, borelGeneratedByIntegrals_of_dense ha h𝒟,
      observableIntegralsMeasurable_of_dense h₂ D h𝒟, fun κ hκ =>
        preimagesShiftInvariant_of_dense ha h𝒟
          fun F hF => (hκ F (h𝒟.2.1 hF).2.1).1⟩, fun κ κ' hκ hκ' => ?_⟩
  have hall : ∀ᵐ U ∂ν, ∀ F ∈ 𝒟, (κ U).expect F = (κ' U).expect F :=
    (ae_ball_iff h𝒟.1).2 fun F hF => ae_expect_eq_of_isInvariantDisintegration hκ hκ' (h𝒟.2.1 hF).2.1
  have heq : ∀ᵐ U ∂ν, κ U = κ' U := by
    filter_upwards [hall] with U hU
    exact ((h₁ D).2 𝒟 h𝒟).2.2.2 (κ U) (κ' U) hU
  exact ⟨heq, Measure.map_congr heq⟩
end YangMills.Construction.PeriodicGibbsStateSpace.ConditionalMeasurability
