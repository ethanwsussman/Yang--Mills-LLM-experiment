import YangMills.Construction.InfiniteLattice.OrientedBondsLiftsAndPreservedMeasuresOfATorus
import YangMills.Construction.InfiniteLattice.ReconstructionAtALatticeMirrorProof
import YangMills.Construction.InfiniteLattice.ReflectionPositivityAndOneTranslationProof
import YangMills.Construction.InfiniteLattice.WeakLimitsInvariantFunctionsAndACriterionForErgodicityProof
import YangMills.Construction.InfiniteLattice.InvariantFunctionsDensitiesAndACriterion
import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAtEverySpacingAndEveryCoupling
import YangMills.Construction.InfiniteLattice.PropertiesOfTheWilsonKernelOnObservables
import YangMills.Construction.InfiniteLattice.RationalPolynomialsAndTheBorelSetsOfTheStates
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ComplexConjugate ComplexOrder Topology ENNReal
noncomputable section
namespace YangMills.Construction.InfiniteLattice.ShiftInvariance
variable {a : ℝ}
theorem shift_pointMap (v x : LatticePoint a) : (shift v).pointMap x = x + v :=
  Subtype.ext rfl
theorem shift_zero_linkMap (b : Link a) : (shift (0 : LatticePoint a)).linkMap b = b := by apply _root_.YangMills.Construction.InfiniteLattice.Link.shiftBy_zero <;> assumption
theorem shift_linkMap_shift (v w : LatticePoint a) (b : Link a) :
    (shift w).linkMap ((shift v).linkMap b) = (shift (v + w)).linkMap b :=
  Link.ext (by simp [LatticeSymmetry.linkMap, shift_pointMap, add_assoc])
    (by simp [LatticeSymmetry.linkMap, shift_pointMap, add_assoc])
theorem shiftsComposeOnFields_holds (a : ℝ) : ShiftsComposeOnFields a := by
  refine ⟨?_, fun v w => ?_⟩
  · funext U
    refine Subtype.ext (funext fun b => ?_)
    change U ((shift (0 : LatticePoint a)).linkMap b) = U b
    rw [shift_zero_linkMap]
  · funext U
    refine Subtype.ext (funext fun b => ?_)
    change U ((shift w).linkMap ((shift v).linkMap b)) =
      U ((shift (v + w)).linkMap b)
    rw [shift_linkMap_shift]
theorem continuous_pullbackField (s : LatticeSymmetry a) : Continuous s.pullbackField := by
  exact show Continuous (fun U : {U : Link a → Matrices.ComplexMatrix2.specialUnitary //
        ∀ b, U b.opposite = (U b)⁻¹} =>
      (⟨fun b => U.1 (s.linkMap b), fun b => U.2 (s.linkMap b)⟩ :
        {U : Link a → Matrices.ComplexMatrix2.specialUnitary // ∀ b, U b.opposite = (U b)⁻¹})) from
    Continuous.subtype_mk
      (f := fun U : {U : Link a → Matrices.ComplexMatrix2.specialUnitary //
          ∀ b, U b.opposite = (U b)⁻¹} =>
        fun b => U.1 (s.linkMap b))
      (continuous_pi fun b => (continuous_apply (s.linkMap b)).comp continuous_subtype_val) _
theorem measurable_pullbackField (s : LatticeSymmetry a) : Measurable s.pullbackField :=
  (continuous_pullbackField s).measurable
theorem countable_latticePoint (a : ℝ) : Countable (LatticePoint a) := by
  refine Function.Surjective.countable (f := latticePointOfInt a) fun x => ?_
  obtain ⟨n, hn⟩ := x.2
  exact ⟨n, Subtype.ext (funext fun μ => (hn μ).symm)⟩
theorem shiftInvariantSigma_le (a : ℝ) :
    shiftInvariantSigma a ≤ (inferInstance : MeasurableSpace (GaugeField a)) :=
  fun _ h => h.1
theorem preimage_pullbackField_eq {I : Set (GaugeField a)}
    (hI : MeasurableSet[shiftInvariantSigma a] I) (v : LatticePoint a) :
    (shift v).pullbackField ⁻¹' I = I :=
  ((shift v).actOn_indicator_eq_iff I).mp (hI.2 v)
theorem measurableSet_shiftInvariantSigma_iff {I : Set (GaugeField a)} :
    MeasurableSet[shiftInvariantSigma a] I ↔
      MeasurableSet I ∧ ∀ v : LatticePoint a, (shift v).pullbackField ⁻¹' I = I :=
  ⟨fun h => ⟨h.1, preimage_pullbackField_eq h⟩, fun h => ⟨h.1, fun v =>
    ((shift v).actOn_indicator_eq_iff I).mpr (h.2 v)⟩⟩
theorem invariantSetsFormSigmaAlgebra_holds (a : ℝ) : InvariantSetsFormSigmaAlgebra a :=
  ⟨@MeasurableSet.univ _ (shiftInvariantSigma a),
    fun I h => (shiftInvariantSigma a).measurableSet_compl I h,
    fun f h => (shiftInvariantSigma a).measurableSet_iUnion f h⟩
theorem invariantMeasurableIffFixed_holds (a : ℝ) : InvariantMeasurableIffFixed a := by
  intro J hJ
  constructor
  · intro h v
    funext U
    have hz : MeasurableSet[shiftInvariantSigma a] (J ⁻¹' {J U}) := h (measurableSet_singleton _)
    exact show U ∈ (shift v).pullbackField ⁻¹' (J ⁻¹' {J U}) from by
      rw [preimage_pullbackField_eq hz v]
      rfl
  · intro h A hA
    refine measurableSet_shiftInvariantSigma_iff.mpr ⟨hJ hA, fun v => ?_⟩
    rw [← preimage_comp, h v]
theorem apply_shift_eq_of_measurable {J : GaugeField a → ℂ}
    (hJ : Measurable[shiftInvariantSigma a] J)
    (v : LatticePoint a) (U : GaugeField a) : J ((shift v).pullbackField U) = J U := by apply _root_.YangMills.Construction.GibbsAtFixedSpacing.LimitsAndErgodicity.invariantMeasurable_pointwiseInvariant <;> assumption
theorem isBoundedObservable_indicator {E : Set (GaugeField a)} (hE : MeasurableSet E) :
    IsBoundedObservable (E.indicator (1 : GaugeField a → ℂ)) := by
  refine ⟨measurable_one.indicator hE, 1, fun U => ?_⟩
  by_cases h : U ∈ E <;> simp [h]
theorem measurePreserving_pullbackField {ν : Measure (GaugeField a)} [IsProbabilityMeasure ν]
    {s : LatticeSymmetry a} (h : IsSymmetricUnder ν s) :
    MeasurePreserving s.pullbackField ν ν := by
  refine ⟨measurable_pullbackField s, Measure.ext fun E hE => ?_⟩
  rw [Measure.map_apply (measurable_pullbackField s) hE]
  have h1 := h _ (isBoundedObservable_indicator hE)
  have hE' : MeasurableSet (s.pullbackField ⁻¹' E) := measurable_pullbackField s hE
  have h2 : s.actOn (E.indicator (1 : GaugeField a → ℂ)) =
      (s.pullbackField ⁻¹' E).indicator (fun _ => (1 : ℂ)) := by
    funext U
    by_cases hU : s.pullbackField U ∈ E
    · simp [LatticeSymmetry.actOn, Set.indicator, hU]
    · simp [LatticeSymmetry.actOn, Set.indicator, hU]
  have h3 : E.indicator (1 : GaugeField a → ℂ) = E.indicator (fun _ => (1 : ℂ)) := rfl
  rw [h2, h3, integral_indicator_const _ hE', integral_indicator_const _ hE] at h1
  simp only [Complex.real_smul, mul_one, Complex.ofReal_inj] at h1
  have := (measureReal_eq_measureReal_iff (μ := ν) (ν := ν)).mp h1
  exact this
theorem integral_comp_pullbackField {ν : Measure (GaugeField a)} [IsProbabilityMeasure ν]
    {s : LatticeSymmetry a} (h : IsSymmetricUnder ν s) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : GaugeField a → E} (hg : AEStronglyMeasurable g ν) :
    ∫ U, g (s.pullbackField U) ∂ν = ∫ U, g U ∂ν := by
  have hp := measurePreserving_pullbackField h
  rw [← integral_map hp.measurable.aemeasurable (by rwa [hp.map_eq]), hp.map_eq]
theorem aeInvariantAgreesOnInvariantSet_holds (a : ℝ) : AEInvariantAgreesOnInvariantSet a := by
  intro ν hν φ hφ hae
  have := ν.2
  have := countable_latticePoint a
  set N : Set (GaugeField a) :=
    ⋃ v : LatticePoint a, {U | φ ((shift v).pullbackField U) ≠ φ U} with hN
  have hNm : MeasurableSet N := MeasurableSet.iUnion fun v =>
    (measurableSet_eq_fun (hφ.comp (measurable_pullbackField _)) hφ).compl
  have hN0 : ν.1 N = 0 := by
    refine measure_iUnion_null fun v => ?_
    exact hae v
  set V : Set (GaugeField a) :=
    ⋂ w : LatticePoint a, (shift w).pullbackField ⁻¹' Nᶜ with hV
  have hVm : MeasurableSet V := MeasurableSet.iInter fun w =>
    measurable_pullbackField _ hNm.compl
  have hVc : ν.1 Vᶜ = 0 := by
    rw [hV, compl_iInter]
    refine measure_iUnion_null fun w => ?_
    have hp := measurePreserving_pullbackField (hν w)
    rw [← preimage_compl, compl_compl, hp.measure_preimage hNm.nullMeasurableSet]
    exact hN0
  have hVshift : ∀ v : LatticePoint a, (shift v).pullbackField ⁻¹' V = V := by
    intro v
    ext U
    simp only [hV, mem_preimage, mem_iInter]
    have hc : ∀ w (X : GaugeField a), (shift w).pullbackField
        ((shift v).pullbackField X) = (shift (w + v)).pullbackField X :=
      fun w X => congrFun ((shiftsComposeOnFields_holds a).2 w v) X
    constructor
    · intro h w
      have := h (w - v)
      rwa [hc, sub_add_cancel] at this
    · intro h w
      rw [hc]
      exact h _
  have hVI : MeasurableSet[shiftInvariantSigma a] V :=
    measurableSet_shiftInvariantSigma_iff.mpr ⟨hVm, hVshift⟩
  refine ⟨V, hVI, ?_, ?_⟩
  · have := prob_compl_eq_zero_iff (μ := ν.1) hVm
    exact this.mp hVc
  · have hm : Measurable fun U => φ U * V.indicator (1 : GaugeField a → ℂ) U :=
      hφ.mul (measurable_one.indicator hVm)
    refine (invariantMeasurableIffFixed_holds a _ hm).mpr fun v => ?_
    funext U
    have hUV : (shift v).pullbackField U ∈ V ↔ U ∈ V := by
      conv_rhs => rw [← hVshift v]
      rfl
    by_cases hU : U ∈ V
    · have hU0 : U ∉ N := by
        have := mem_iInter.mp hU 0
        have h0 : (shift (0 : LatticePoint a)).pullbackField U = U :=
          congrFun (shiftsComposeOnFields_holds a).1 U
        rw [mem_preimage, h0] at this
        exact this
      have hv : φ ((shift v).pullbackField U) = φ U := by
        by_contra hne
        exact hU0 (mem_iUnion.mpr ⟨v, hne⟩)
      simp [hU, hUV.mpr hU, hv]
    · have : (shift v).pullbackField U ∉ V := fun h => hU (hUV.mp h)
      simp [hU, this]
theorem integrable_of_isBoundedObservable {A : GaugeField a → ℂ} (hA : IsBoundedObservable A)
    (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν] : Integrable A ν := by
  obtain ⟨hm, C, hC⟩ := hA
  exact Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ hC)
theorem isBoundedObservable_mul {A B : GaugeField a → ℂ} (hA : IsBoundedObservable A)
    (hB : IsBoundedObservable B) : IsBoundedObservable (fun U => A U * B U) := by
  obtain ⟨hm, C, hC⟩ := hA
  obtain ⟨hm', C', hC'⟩ := hB
  refine ⟨hm.mul hm', C * C', fun U => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hC U) (hC' U) (norm_nonneg _) ((norm_nonneg _).trans (hC U))
theorem isBoundedObservable_conj {A : GaugeField a → ℂ} (hA : IsBoundedObservable A) :
    IsBoundedObservable (fun U => conj (A U)) := by apply _root_.YangMills.Construction.LatticeConventions.MirrorReconstructionProof.isBoundedObservable_conjFun <;> assumption
theorem isBoundedObservable_actOn {A : GaugeField a → ℂ} (hA : IsBoundedObservable A)
    (s : LatticeSymmetry a) : IsBoundedObservable (s.actOn A) := by
  obtain ⟨hm, C, hC⟩ := hA
  exact ⟨hm.comp (measurable_pullbackField s), C, fun U => hC _⟩
theorem norm_le_supNorm {A : GaugeField a → ℂ} (hA : IsBoundedObservable A)
    (U : GaugeField a) : ‖A U‖ ≤ observableSupNorm A := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.norm_le_supNorm <;> assumption
theorem supNorm_nonneg {A : GaugeField a → ℂ} (hA : IsBoundedObservable A) :
    0 ≤ observableSupNorm A :=
  (norm_nonneg _).trans (norm_le_supNorm hA (trivialField a))
theorem indicator_one_mul_eq_indicator (I : Set (GaugeField a)) (J : GaugeField a → ℂ)
    (U : GaugeField a) : I.indicator (1 : GaugeField a → ℂ) U * J U = I.indicator J U := by
  by_cases h : U ∈ I <;> simp [h]
theorem integral_indicator_one_mul_eq_setIntegral {ν : Measure (GaugeField a)}
    {I : Set (GaugeField a)} (hI : MeasurableSet I) (J : GaugeField a → ℂ) :
    ∫ U, I.indicator (1 : GaugeField a → ℂ) U * J U ∂ν = ∫ U in I, J U ∂ν := by
  simp_rw [indicator_one_mul_eq_indicator]
  exact integral_indicator hI
section CondExpVersions
variable {ν : Measure (GaugeField a)} [IsProbabilityMeasure ν]
theorem isCondExpRepresentative_condExp {F : GaugeField a → ℂ} (hF : Integrable F ν) :
    IsCondExpRepresentative ν F (condExp (shiftInvariantSigma a) ν F) := by
  refine ⟨stronglyMeasurable_condExp.measurable, integrable_condExp, fun I hI => ?_⟩
  rw [integral_indicator_one_mul_eq_setIntegral (shiftInvariantSigma_le a _ hI),
    integral_indicator_one_mul_eq_setIntegral (shiftInvariantSigma_le a _ hI)]
  exact setIntegral_condExp (shiftInvariantSigma_le a) hF hI
theorem IsCondExpRepresentative.ae_eq_condExp {F J : GaugeField a → ℂ} (hF : Integrable F ν)
    (hJ : IsCondExpRepresentative ν F J) : J =ᵐ[ν] condExp (shiftInvariantSigma a) ν F := by
  refine ae_eq_condExp_of_forall_setIntegral_eq (shiftInvariantSigma_le a) hF
    (fun s _ _ => hJ.2.1.integrableOn) (fun s hs _ => ?_)
    hJ.1.stronglyMeasurable.aestronglyMeasurable
  have := hJ.2.2 s hs
  rwa [integral_indicator_one_mul_eq_setIntegral (shiftInvariantSigma_le a _ hs),
    integral_indicator_one_mul_eq_setIntegral (shiftInvariantSigma_le a _ hs)] at this
omit [IsProbabilityMeasure ν] in
theorem IsCondExpRepresentative.congr {F J J' : GaugeField a → ℂ} (hJ : IsCondExpRepresentative ν F J)
    (hm : Measurable[shiftInvariantSigma a] J') (he : J' =ᵐ[ν] J) :
    IsCondExpRepresentative ν F J' := by
  refine ⟨hm, hJ.2.1.congr he.symm, fun I hI => ?_⟩
  rw [← hJ.2.2 I hI]
  refine integral_congr_ae ?_
  filter_upwards [he] with U hU
  rw [hU]
theorem IsCondExpRepresentative.integral_mul {F J χ : GaugeField a → ℂ} (hF : Integrable F ν)
    (hJ : IsCondExpRepresentative ν F J) (hχ : Measurable[shiftInvariantSigma a] χ) {C : ℝ}
    (hC : ∀ U, ‖χ U‖ ≤ C) :
    ∫ U, χ U * F U ∂ν = ∫ U, χ U * J U ∂ν := by
  have hχb : Measurable χ := hχ.mono (shiftInvariantSigma_le a) le_rfl
  have hχF : Integrable (fun U => χ U * F U) ν :=
    hF.bdd_mul hχb.aestronglyMeasurable (ae_of_all _ hC)
  have hχF' : Integrable (fun U => ContinuousLinearMap.mul ℝ ℂ (χ U) (F U)) ν := hχF
  have hpull := condExp_bilin_of_stronglyMeasurable_left (m := shiftInvariantSigma a) (μ := ν)
    (ContinuousLinearMap.mul ℝ ℂ) hχ.stronglyMeasurable (g := F) hχF' hF
  calc ∫ U, χ U * F U ∂ν = ∫ U, condExp (shiftInvariantSigma a) ν (fun U => χ U * F U) U ∂ν :=
        (integral_condExp (shiftInvariantSigma_le a)).symm
    _ = ∫ U, χ U * J U ∂ν := by
        refine integral_congr_ae ?_
        filter_upwards [hpull, hJ.ae_eq_condExp hF] with U h1 h2
        simpa [h2] using h1
theorem IsCondExpRepresentative.measure_gt_supNorm {F J : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (hJ : IsCondExpRepresentative ν F J) : ν {U | observableSupNorm F < ‖J U‖} = 0 := by
  set N := observableSupNorm F with hNdef
  have hN0 : 0 ≤ N := supNorm_nonneg hF
  set I₀ : Set (GaugeField a) := {U | N < ‖J U‖} with hI₀
  have hI : MeasurableSet[shiftInvariantSigma a] I₀ :=
    (measurable_norm.comp hJ.1) measurableSet_Ioi
  have hIb : MeasurableSet I₀ := shiftInvariantSigma_le a _ hI
  set χ : GaugeField a → ℂ := I₀.indicator fun U => conj (J U) / (‖J U‖ : ℂ) with hχdef
  have hχm : Measurable[shiftInvariantSigma a] χ :=
    Measurable.indicator ((Complex.continuous_conj.measurable.comp hJ.1).div
      (Complex.measurable_ofReal.comp (measurable_norm.comp hJ.1))) hI
  have hχ1 : ∀ U, ‖χ U‖ ≤ 1 := fun U => by
    by_cases h : U ∈ I₀
    · have hp : 0 < ‖J U‖ := hN0.trans_lt h
      simp only [hχdef, Set.indicator_of_mem h, norm_div, RCLike.norm_conj, Complex.norm_real,
        norm_norm]
      rw [div_self hp.ne']
    · simp [hχdef, Set.indicator_of_notMem h]
  have hχJ : ∀ U, χ U * J U = ((I₀.indicator (fun U => ‖J U‖) U : ℝ) : ℂ) := fun U => by
    by_cases h : U ∈ I₀
    · have hp : 0 < ‖J U‖ := hN0.trans_lt h
      have hne : ((‖J U‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
      simp only [hχdef, Set.indicator_of_mem h]
      rw [div_mul_eq_mul_div, Complex.conj_mul', pow_two, mul_div_assoc, div_self hne, mul_one]
    · simp [hχdef, Set.indicator_of_notMem h]
  have hFi := integrable_of_isBoundedObservable hF ν
  have key := hJ.integral_mul hFi hχm hχ1
  have hR : ∫ U, χ U * J U ∂ν = ((∫ U, I₀.indicator (fun U => ‖J U‖) U ∂ν : ℝ) : ℂ) := by
    simp_rw [hχJ]
    exact integral_complex_ofReal
  have hle : ∫ U, I₀.indicator (fun U => ‖J U‖) U ∂ν ≤ N * ν.real I₀ := by
    have h1 : ‖∫ U, χ U * F U ∂ν‖ ≤ ∫ U, I₀.indicator (fun _ => N) U ∂ν := by
      refine norm_integral_le_of_norm_le ((integrable_const N).indicator hIb)
        (ae_of_all _ fun U => ?_)
      by_cases h : U ∈ I₀
      · rw [Set.indicator_of_mem h, norm_mul]
        calc ‖χ U‖ * ‖F U‖ ≤ 1 * N :=
              mul_le_mul (hχ1 U) (norm_le_supNorm hF U) (norm_nonneg _) zero_le_one
          _ = N := one_mul N
      · simp [hχdef, Set.indicator_of_notMem h]
    rw [integral_indicator_const _ hIb] at h1
    rw [key, hR, Complex.norm_real] at h1
    have h2 := (le_abs_self _).trans h1
    simpa [mul_comm] using h2
  have hg : Integrable (I₀.indicator fun U => ‖J U‖ - N) ν :=
    (hJ.2.1.norm.sub (integrable_const N)).indicator hIb
  have hg0 : 0 ≤ᵐ[ν] I₀.indicator fun U => ‖J U‖ - N :=
    ae_of_all _ fun U => Set.indicator_nonneg (fun U hU => sub_nonneg.mpr (le_of_lt hU)) U
  have hint : ∫ U, I₀.indicator (fun U => ‖J U‖ - N) U ∂ν = 0 := by
    refine le_antisymm ?_ (integral_nonneg_of_ae hg0)
    have : (I₀.indicator fun U => ‖J U‖ - N) =
        fun U => I₀.indicator (fun U => ‖J U‖) U - I₀.indicator (fun _ => N) U := by
      funext U
      by_cases h : U ∈ I₀ <;> simp [h]
    rw [this, integral_sub (hJ.2.1.norm.indicator hIb) ((integrable_const N).indicator hIb),
      integral_indicator_const _ hIb]
    simp only [smul_eq_mul]
    linarith
  have hz := (integral_eq_zero_iff_of_nonneg_ae hg0 hg).mp hint
  have : I₀ ⊆ {U | (I₀.indicator fun U => ‖J U‖ - N) U ≠ 0} := fun U hU => by
    change (I₀.indicator (fun U => ‖J U‖ - N) U) ≠ 0
    rw [Set.indicator_of_mem hU]
    exact (sub_pos.mpr hU).ne'
  exact measure_mono_null this hz
theorem exists_bounded_condExpRepresentative {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    ∃ J, IsCondExpRepresentative ν F J ∧ IsBoundedObservable J ∧
      observableSupNorm J ≤ observableSupNorm F := by
  have hFi := integrable_of_isBoundedObservable hF ν
  have hJ := isCondExpRepresentative_condExp hFi
  set J₀ := condExp (shiftInvariantSigma a) ν F with hJ₀
  have hnull := hJ.measure_gt_supNorm hF
  set N := observableSupNorm F
  have hN0 : 0 ≤ N := supNorm_nonneg hF
  set I₀ : Set (GaugeField a) := {U | N < ‖J₀ U‖} with hI₀
  have hI : MeasurableSet[shiftInvariantSigma a] I₀ :=
    (measurable_norm.comp hJ.1) measurableSet_Ioi
  have hJm : Measurable[shiftInvariantSigma a] (I₀ᶜ.indicator J₀) :=
    Measurable.indicator hJ.1 ((shiftInvariantSigma a).measurableSet_compl _ hI)
  have hae : I₀ᶜ.indicator J₀ =ᵐ[ν] J₀ := by
    have : ∀ᵐ U ∂ν, U ∉ I₀ := measure_eq_zero_iff_ae_notMem.mp hnull
    filter_upwards [this] with U hU
    simp [hU]
  have hb : ∀ U, ‖I₀ᶜ.indicator J₀ U‖ ≤ N := fun U => by
    by_cases h : U ∈ I₀
    · simpa [h] using hN0
    · have : ‖J₀ U‖ ≤ N := not_lt.mp h
      simpa [h] using this
  refine ⟨I₀ᶜ.indicator J₀, hJ.congr hJm hae,
    ⟨hJm.mono (shiftInvariantSigma_le a) le_rfl, N, hb⟩, ?_⟩
  have := (⟨trivialField a⟩ : Nonempty (GaugeField a))
  exact ciSup_le hb
omit [IsProbabilityMeasure ν] in
theorem IsCondExpRepresentative.conjugate {F J : GaugeField a → ℂ} (hJ : IsCondExpRepresentative ν F J) :
    IsCondExpRepresentative ν (fun U => conj (F U)) (fun U => conj (J U)) := by
  refine ⟨Complex.continuous_conj.measurable.comp hJ.1, ?_, fun I hI => ?_⟩
  · exact Complex.conjCLE.toContinuousLinearMap.integrable_comp hJ.2.1
  · have hc : ∀ (G : GaugeField a → ℂ) (U : GaugeField a),
        I.indicator (1 : GaugeField a → ℂ) U * conj (G U) =
          conj (I.indicator (1 : GaugeField a → ℂ) U * G U) := fun G U => by
      by_cases h : U ∈ I <;> simp [h]
    simp_rw [hc]
    rw [integral_conj, integral_conj, hJ.2.2 I hI]
omit [IsProbabilityMeasure ν] in
theorem IsCondExpRepresentative.of_shifted {F J : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (hν : IsShiftInvariant ν) (hJ : IsCondExpRepresentative ν F J) (v : LatticePoint a) :
    IsCondExpRepresentative ν ((shift v).actOn F) J := by
  refine ⟨hJ.1, hJ.2.1, fun I hI => ?_⟩
  rw [hJ.2.2 I hI]
  have hO : IsBoundedObservable (fun U => I.indicator (1 : GaugeField a → ℂ) U * F U) :=
    isBoundedObservable_mul (isBoundedObservable_indicator (shiftInvariantSigma_le a _ hI)) hF
  rw [← hν v _ hO]
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  have h1 := congrFun (hI.2 v) U
  simp only [LatticeSymmetry.actOn] at h1 ⊢
  rw [h1]
end CondExpVersions
theorem condExpVersionsOfObservable_holds (ν : GaugeFieldProbability a) (hν : IsShiftInvariant ν.1)
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) : CondExpVersionsOfObservable ν F := by
  have := ν.2
  refine ⟨exists_bounded_condExpRepresentative hF, fun J hJ =>
    ⟨fun χ hχ hχo => ?_, hJ.conjugate, hJ.of_shifted hF hν⟩⟩
  obtain ⟨_, C, hC⟩ := hχo
  exact hJ.integral_mul (integrable_of_isBoundedObservable hF ν.1) hχ hC
theorem plateauAsIntegralAndSquare_holds (ν : GaugeFieldProbability a)
    {A B : GaugeField a → ℂ} (hA : IsBoundedObservable A) (hB : IsBoundedObservable B) :
    PlateauAsIntegralAndSquare ν A B := by
  have := ν.2
  have hAi := integrable_of_isBoundedObservable hA ν.1
  have hBi := integrable_of_isBoundedObservable hB ν.1
  have hEA := isCondExpRepresentative_condExp (ν := ν.1) hAi
  constructor
  · intro Y hY
    obtain ⟨J, hJ, hJo, -⟩ := exists_bounded_condExpRepresentative (ν := ν.1) hB
    obtain ⟨_, C, hC⟩ := hJo
    have hJE := hJ.ae_eq_condExp hBi
    have hYE := hY.ae_eq_condExp hBi
    have hcA : Integrable (fun U => conj (A U)) ν.1 :=
      integrable_of_isBoundedObservable (isBoundedObservable_conj hA) ν.1
    have key := hEA.conjugate.integral_mul hcA hJ.1 hC
    change ∫ U, conj (condExp (shiftInvariantSigma a) ν.1 A U) *
        condExp (shiftInvariantSigma a) ν.1 B U ∂ν.1 = ∫ U, conj (A U) * Y U ∂ν.1
    calc ∫ U, conj (condExp (shiftInvariantSigma a) ν.1 A U) *
          condExp (shiftInvariantSigma a) ν.1 B U ∂ν.1
        = ∫ U, J U * conj (condExp (shiftInvariantSigma a) ν.1 A U) ∂ν.1 := by
          refine integral_congr_ae ?_
          filter_upwards [hJE] with U h
          rw [h, mul_comm]
      _ = ∫ U, J U * conj (A U) ∂ν.1 := key.symm
      _ = ∫ U, conj (A U) * Y U ∂ν.1 := by
          refine integral_congr_ae ?_
          filter_upwards [hJE, hYE] with U h h'
          rw [h, h', mul_comm]
  · intro Y hY
    obtain ⟨J, hJ, hJo, -⟩ := exists_bounded_condExpRepresentative (ν := ν.1) hA
    have hJE := hJ.ae_eq_condExp hAi
    have hYE := hY.ae_eq_condExp hAi
    set c : ℂ := ν.expect A with hc
    have hJint : ∫ U, J U ∂ν.1 = c := by
      have := hJ.2.2 univ (@MeasurableSet.univ _ (shiftInvariantSigma a))
      simpa [hc, GaugeFieldProbability.expect] using this
    have hJi : Integrable J ν.1 := hJ.2.1
    have hJJ : Integrable (fun U => conj (J U) * J U) ν.1 :=
      integrable_of_isBoundedObservable
        (isBoundedObservable_mul (isBoundedObservable_conj hJo) hJo) ν.1
    have hcJ : Integrable (fun U => conj (J U)) ν.1 :=
      integrable_of_isBoundedObservable (isBoundedObservable_conj hJo) ν.1
    have hpl : plateauForm ν.1 A A = ∫ U, conj (J U) * J U ∂ν.1 := by
      change ∫ U, conj (condExp (shiftInvariantSigma a) ν.1 A U) *
        condExp (shiftInvariantSigma a) ν.1 A U ∂ν.1 = _
      refine integral_congr_ae ?_
      filter_upwards [hJE] with U h
      rw [h]
    have hnorm : ∫ U, ‖Y U - c‖ ^ 2 ∂ν.1 = ∫ U, ‖J U - c‖ ^ 2 ∂ν.1 := by
      refine integral_congr_ae ?_
      filter_upwards [hJE, hYE] with U h h'
      rw [h, h']
    have hnn : 0 ≤ ∫ U, ‖Y U - c‖ ^ 2 ∂ν.1 := integral_nonneg fun U => by positivity
    have hsq : stateL2Norm ν (fun U => Y U - c) ^ 2 = ∫ U, ‖Y U - c‖ ^ 2 ∂ν.1 := by
      rw [stateL2Norm, ← Real.sqrt_eq_rpow, Real.sq_sqrt hnn]
    have hexp : ((∫ U, ‖J U - c‖ ^ 2 ∂ν.1 : ℝ) : ℂ) =
        ∫ U, (conj (J U) * J U - c * conj (J U) - conj c * J U + conj c * c) ∂ν.1 := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (ae_of_all _ fun U => ?_)
      have h := Complex.conj_mul' (J U - c)
      rw [map_sub] at h
      change ((‖J U - c‖ ^ 2 : ℝ) : ℂ) = _
      push_cast
      rw [← h]
      ring
    have hsum : ∫ U, (conj (J U) * J U - c * conj (J U) - conj c * J U + conj c * c) ∂ν.1 =
        (∫ U, conj (J U) * J U ∂ν.1) - c * conj c - conj c * c + conj c * c := by
      have i1 : Integrable (fun U => conj (J U) * J U - c * conj (J U)) ν.1 :=
        hJJ.sub (hcJ.const_mul c)
      have i2 : Integrable (fun U => conj (J U) * J U - c * conj (J U) - conj c * J U) ν.1 :=
        i1.sub (hJi.const_mul (conj c))
      rw [integral_add i2 (integrable_const _), integral_sub i1 (hJi.const_mul (conj c)),
        integral_sub hJJ (hcJ.const_mul c), integral_const_mul, integral_const_mul, integral_conj,
        hJint, integral_const]
      simp
    have hcc : ((‖c‖ ^ 2 : ℝ) : ℂ) = conj c * c := by
      rw [Complex.conj_mul']
      push_cast
      rfl
    rw [hsq, hnorm, hexp, hsum, hpl, hcc]
    ring
theorem condExpAndPlateau_holds (a : ℝ) : CondExpAndPlateau a := fun ν hν =>
  ⟨fun _ hF => condExpVersionsOfObservable_holds ν hν hF,
    fun _ _ hA hB => plateauAsIntegralAndSquare_holds ν hA hB⟩
theorem dependsOnlyOnLinks_mono {E : Type*} {S T : Set (Link a)} (h : S ⊆ T)
    {F : GaugeField a → E} (hF : DependsOnlyOnLinks S F) : DependsOnlyOnLinks T F :=
  fun U U' hU => hF U U' (by
    funext b
    exact congrFun hU ⟨b.1, h b.2⟩)
theorem dependsOnlyOnLinks_actOn_shift {E : Type*} {W : Set (Link a)} {F : GaugeField a → E}
    (hF : DependsOnlyOnLinks W F) (v : LatticePoint a) :
    DependsOnlyOnLinks ((shift v).linkMap '' W) ((shift v).actOn F) :=
  fun U U' hU => hF _ _ (by
    funext b
    exact congrFun hU ⟨_, mem_image_of_mem _ b.2⟩)
theorem exists_shift_avoiding (ha : 0 < a) (W : Set (Link a)) (hW : W.Finite)
    (𝓛 : Finset (Link a)) :
    ∃ v : LatticePoint a, (shift v).linkMap '' W ⊆
      {b | b ∉ (𝓛 : Set (Link a)) ∧ b.opposite ∉ (𝓛 : Set (Link a))} := by
  classical
  set M : ℝ := ∑ b ∈ 𝓛, |((b.initial : LatticePoint a) : AmbientSpace) 0| with hM
  set m : ℝ := ∑ b ∈ hW.toFinset,
    (|((b.initial : LatticePoint a) : AmbientSpace) 0| +
      |((b.terminal : LatticePoint a) : AmbientSpace) 0|) with hm
  obtain ⟨t, ht⟩ := exists_nat_gt ((M + m) / a)
  have hta : M + m < (t : ℝ) * a := by rwa [div_lt_iff₀ ha] at ht
  obtain ⟨v, hv0⟩ : ∃ v : LatticePoint a, ((v : LatticePoint a) : AmbientSpace) 0 = (t : ℝ) * a :=
    ⟨latticePointOfInt a (Pi.single 0 (t : ℤ)), by simp [latticePointOfInt]⟩
  have hM' : ∀ b ∈ 𝓛, ((b.initial : LatticePoint a) : AmbientSpace) 0 ≤ M := fun b hb =>
    (le_abs_self _).trans (Finset.single_le_sum
      (f := fun b : Link a => |((b.initial : LatticePoint a) : AmbientSpace) 0|)
      (fun _ _ => abs_nonneg _) hb)
  have hm' : ∀ b ∈ W, |((b.initial : LatticePoint a) : AmbientSpace) 0| +
      |((b.terminal : LatticePoint a) : AmbientSpace) 0| ≤ m :=
    fun b hb => Finset.single_le_sum
      (f := fun b : Link a => |((b.initial : LatticePoint a) : AmbientSpace) 0| +
        |((b.terminal : LatticePoint a) : AmbientSpace) 0|)
      (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (hW.mem_toFinset.mpr hb)
  refine ⟨v, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  have h1 := hm' b hb
  have bt := neg_abs_le (((b.initial : LatticePoint a) : AmbientSpace) 0)
  have bh := neg_abs_le (((b.terminal : LatticePoint a) : AmbientSpace) 0)
  have at0 := abs_nonneg (((b.initial : LatticePoint a) : AmbientSpace) 0)
  have ah0 := abs_nonneg (((b.terminal : LatticePoint a) : AmbientSpace) 0)
  constructor
  · intro hmem
    have h2 := hM' _ (Finset.mem_coe.mp hmem)
    have e : ((((shift v).linkMap b).initial : LatticePoint a) : AmbientSpace) 0 =
        ((b.initial : LatticePoint a) : AmbientSpace) 0 +
          ((v : LatticePoint a) : AmbientSpace) 0 := rfl
    rw [e, hv0] at h2
    linarith
  · intro hmem
    have h2 := hM' _ (Finset.mem_coe.mp hmem)
    have e : ((((shift v).linkMap b).opposite.initial : LatticePoint a) : AmbientSpace) 0 =
        ((b.terminal : LatticePoint a) : AmbientSpace) 0 +
          ((v : LatticePoint a) : AmbientSpace) 0 := rfl
    rw [e, hv0] at h2
    linarith
theorem isBoundedObservable_of_continuous (ha : 0 < a) {A : GaugeField a → ℂ}
    (hA : Continuous A) : IsBoundedObservable A := by
  have : CompactSpace (GaugeField a) :=
    (WilsonOperator.gaugeFieldHomeomorph ha).symm.compactSpace
  obtain ⟨C, hC⟩ := (isCompact_range hA).isBounded.exists_norm_le
  exact ⟨hA.measurable, C, fun U => hC _ (mem_range_self U)⟩
theorem continuous_and_cylinder_of_mem_complexRatPoly (hd : RatPolyDense a)
    {ψ : GaugeField a → ℂ} (hψ : ψ ∈ complexRatPolyObservables a) :
    Continuous ψ ∧ ∃ W : Set (Link a), W.Finite ∧ DependsOnlyOnLinks W ψ := by
  obtain ⟨F₁, h₁, F₂, h₂, h⟩ := hψ
  obtain ⟨c₁, W₁, f₁, -, r₁⟩ : Continuous (fun U => (F₁ U : ℂ)) ∧
      IsCylinderFunction (fun U => (F₁ U : ℂ)) := hd.2.1 F₁ h₁
  obtain ⟨c₂, W₂, f₂, -, r₂⟩ : Continuous (fun U => (F₂ U : ℂ)) ∧
      IsCylinderFunction (fun U => (F₂ U : ℂ)) := hd.2.1 F₂ h₂
  have hψ' : ψ = fun U => (F₁ U : ℂ) + Complex.I * (F₂ U : ℂ) := funext h
  refine ⟨?_, W₁ ∪ W₂, f₁.union f₂, fun U U' hU => ?_⟩
  · rw [hψ']
    exact c₁.add (continuous_const.mul c₂)
  · have e₁ : (F₁ U : ℂ) = F₁ U' := dependsOnlyOnLinks_mono subset_union_left r₁ U U' hU
    have e₂ : (F₂ U : ℂ) = F₂ U' := dependsOnlyOnLinks_mono subset_union_right r₂ U U' hU
    rw [h U, h U', e₁, e₂]
theorem isGibbs_iff_kernel_expect {L K : ℕ} {ha : 0 < PeriodicLattice.meshSize L (K : ℤ)} {β : ℝ}
    {ν : GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ))}
    (h : WilsonOperator.GibbsPropertyEquivalences ha β ν) :
    IsGibbs β ν.1 ↔ ∀ (𝓛 : Finset (Link (PeriodicLattice.meshSize L (K : ℤ))))
      (h𝓛 : (𝓛 : Set (Link (PeriodicLattice.meshSize L (K : ℤ)))) ⊆
        positiveLinkSet (PeriodicLattice.meshSize L (K : ℤ)))
      (F : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) → ℂ), IsBoundedObservable F →
        ν.expect (WilsonOperator.kernelOperator ha β h𝓛 F) = ν.expect F := by
  unfold WilsonOperator.GibbsPropertyEquivalences at h
  exact h.out 0 1
theorem invariantDensitiesPreserveGibbs_holds (hdense : RatPolyAndStateBorelSets)
    (hforms : WilsonOperatorProperties)
    (hsym : PeriodicStatesAllScales.AllScalesAllCouplings)
    (L K : ℕ) (hL : Odd L) (hL13 : 13 ≤ L) (hK : 0 < K)
    (ha : 0 < PeriodicLattice.meshSize L (K : ℤ)) :
    InvariantDensitiesPreserveGibbs L K ha := by
  intro β hβ ν hν h hI hO
  have := ν.2
  have hd := hdense L K hL hL13 hK
  have hf := hforms L K hL hL13 hK ha β hβ
  have hs := hsym L K hL hL13 hK β hβ
  have hinv : IsShiftInvariant ν.1 := (hs.1 ν hν).1
  have hmem : PeriodicStatesAllScales.IsShiftInvariantGibbs β ν := by
    have h' := hν
    rw [hs.2.1.1] at h'
    exact h'
  have hνγ := (isGibbs_iff_kernel_expect (hf.2.2 ν)).mp hmem.1
  have hfix := apply_shift_eq_of_measurable hI
  have main : ∀ (𝓛 : Finset (Link (PeriodicLattice.meshSize L (K : ℤ))))
      (h𝓛 : (𝓛 : Set (Link (PeriodicLattice.meshSize L (K : ℤ)))) ⊆
        WilsonOperator.cutoffLinks L K)
      (F : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) → ℂ), IsBoundedObservable F →
      ν.expect (fun U => h U * WilsonOperator.kernelOperator ha β h𝓛 F U) =
        ν.expect (fun U => h U * F U) := by
    intro 𝓛 h𝓛 F hF
    have hwo := (hf.1 𝓛 h𝓛).1
    have hγo : IsBoundedObservable (WilsonOperator.kernelOperator ha β h𝓛 F) :=
      hwo.kernel_isBoundedObservable F hF
    have hC0 : 0 ≤ observableSupNorm F := supNorm_nonneg hF
    have hγC : ∀ U, ‖WilsonOperator.kernelOperator ha β h𝓛 F U‖ ≤ observableSupNorm F :=
      fun U => (norm_le_supNorm hγo U).trans (hwo.supNorm_kernel_le F hF)
    have hFC : ∀ U, ‖F U‖ ≤ observableSupNorm F := norm_le_supNorm hF
    have hε : ∀ ε : ℝ, 0 < ε →
        ‖ν.expect (fun U => h U * WilsonOperator.kernelOperator ha β h𝓛 F U) -
          ν.expect (fun U => h U * F U)‖ ≤
            ε * observableSupNorm F + ε * observableSupNorm F := by
      intro ε hε
      obtain ⟨ψ, hψ, -, hψ1⟩ := hd.2.1 ν h hO ε hε
      obtain ⟨hψc, W, hWf, hψW⟩ := continuous_and_cylinder_of_mem_complexRatPoly hd.1 hψ
      obtain ⟨v, hv⟩ := exists_shift_avoiding ha W hWf 𝓛
      obtain ⟨G, hG⟩ : ∃ G, G = (shift v).actOn ψ := ⟨_, rfl⟩
      have hψo : IsBoundedObservable ψ := isBoundedObservable_of_continuous ha hψc
      have hGo : IsBoundedObservable G := hG ▸ isBoundedObservable_actOn hψo _
      have hGr : WilsonOperator.IgnoresLinksOf (𝓛 : Set (Link _)) G :=
        hG ▸ dependsOnlyOnLinks_mono hv (dependsOnlyOnLinks_actOn_shift hψW v)
      have hmul := ((hf.1 𝓛 h𝓛).2.1).kernel_mul_left G hGo hGr F hF
      have hGF : ν.expect (fun U => G U * WilsonOperator.kernelOperator ha β h𝓛 F U) =
          ν.expect (fun U => G U * F U) := by
        have h1 := hνγ 𝓛 h𝓛 (G * F) (isBoundedObservable_mul hGo hF)
        rw [hmul] at h1
        exact h1
      have hdiff : ∫ U, ‖h U - G U‖ ∂ν.1 ≤ ε := by
        have hg : AEStronglyMeasurable (fun U => ‖h U - ψ U‖) ν.1 :=
          ((hO.1.sub hψo.1).norm).aestronglyMeasurable
        have e : ∫ U, ‖h U - G U‖ ∂ν.1 = ∫ U, ‖h U - ψ U‖ ∂ν.1 := by
          refine (integral_congr_ae (ae_of_all _ fun U => ?_)).trans
            (integral_comp_pullbackField (hinv v) hg)
          rw [hfix v U, hG]
          rfl
        rw [e]
        exact hψ1
      have hint : ∀ X : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) → ℂ,
          IsBoundedObservable X → (∀ U, ‖X U‖ ≤ observableSupNorm F) →
          ‖ν.expect (fun U => h U * X U) - ν.expect (fun U => G U * X U)‖ ≤
            ε * observableSupNorm F := by
        intro X hX hXC
        have i1 := integrable_of_isBoundedObservable (isBoundedObservable_mul hO hX) ν.1
        have i2 := integrable_of_isBoundedObservable (isBoundedObservable_mul hGo hX) ν.1
        change ‖(∫ U, h U * X U ∂ν.1) - ∫ U, G U * X U ∂ν.1‖ ≤ ε * observableSupNorm F
        rw [← integral_sub i1 i2]
        have hb : ∀ U, ‖h U * X U - G U * X U‖ ≤ ‖h U - G U‖ * observableSupNorm F :=
          fun U => by
            rw [← sub_mul, norm_mul]
            exact mul_le_mul_of_nonneg_left (hXC U) (norm_nonneg _)
        have hnI : Integrable (fun U => ‖h U - G U‖ * observableSupNorm F) ν.1 :=
          (((integrable_of_isBoundedObservable hO ν.1).sub
            (integrable_of_isBoundedObservable hGo ν.1)).norm).mul_const _
        calc ‖∫ U, h U * X U - G U * X U ∂ν.1‖
            ≤ ∫ U, ‖h U - G U‖ * observableSupNorm F ∂ν.1 :=
              norm_integral_le_of_norm_le hnI (ae_of_all _ hb)
          _ = (∫ U, ‖h U - G U‖ ∂ν.1) * observableSupNorm F := integral_mul_const _ _
          _ ≤ ε * observableSupNorm F := mul_le_mul_of_nonneg_right hdiff hC0
      have e1 := hint _ hγo hγC
      have e2 := hint F hF hFC
      calc ‖ν.expect (fun U => h U * WilsonOperator.kernelOperator ha β h𝓛 F U) -
            ν.expect (fun U => h U * F U)‖
          = ‖(ν.expect (fun U => h U * WilsonOperator.kernelOperator ha β h𝓛 F U) -
              ν.expect (fun U => G U * WilsonOperator.kernelOperator ha β h𝓛 F U)) -
            (ν.expect (fun U => h U * F U) - ν.expect (fun U => G U * F U))‖ := by
            rw [hGF]
            congr 1
            ring
        _ ≤ ε * observableSupNorm F + ε * observableSupNorm F :=
            (norm_sub_le _ _).trans (add_le_add e1 e2)
    refine sub_eq_zero.mp (norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε' hε' => ?_))
    have hden : 0 < 2 * observableSupNorm F + 1 := by linarith
    have hpos : 0 < ε' / (2 * observableSupNorm F + 1) := div_pos hε' hden
    have h1 := hε _ hpos
    have h2 : ε' / (2 * observableSupNorm F + 1) * (2 * observableSupNorm F + 1) = ε' :=
      div_mul_cancel₀ _ hden.ne'
    nlinarith
  refine ⟨main, fun hnn h1 => ?_⟩
  have him : ∀ U, (h U).im = 0 := fun U => (Complex.le_def.mp (hnn U)).2.symm
  have hre : ∀ U, h U = (((h U).re : ℝ) : ℂ) := fun U =>
    Complex.ext (by simp) (by simp [him U])
  have hw0 : ∀ U, 0 ≤ (h U).re := fun U => (Complex.le_def.mp (hnn U)).1
  have hwm : Measurable fun U => (h U).re := Complex.measurable_re.comp hO.1
  have hfm : Measurable fun U => ENNReal.ofReal (h U).re := hwm.ennreal_ofReal
  have hwi : Integrable (fun U => (h U).re) ν.1 := (integrable_of_isBoundedObservable hO ν.1).re
  have hw1 : ∫ U, (h U).re ∂ν.1 = 1 := by
    have e : ν.expect h = ((∫ U, (h U).re ∂ν.1 : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      exact integral_congr_ae (ae_of_all _ hre)
    rw [e] at h1
    exact_mod_cast h1
  obtain ⟨νw, hνw⟩ : ∃ νw, νw = ν.1.withDensity fun U => ENNReal.ofReal (h U).re := ⟨_, rfl⟩
  have hint : ∀ g : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) → ℂ,
      ∫ U, g U ∂νw = ν.expect (fun U => h U * g U) := by
    intro g
    rw [hνw, integral_withDensity_eq_integral_toReal_smul hfm
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun U => ?_)
    change (ENNReal.ofReal (h U).re).toReal • g U = h U * g U
    rw [ENNReal.toReal_ofReal (hw0 U), Complex.real_smul, ← hre U]
  have hprob : IsProbabilityMeasure νw := ⟨by
    rw [hνw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hwi (ae_of_all _ hw0), hw1]
    simp⟩
  refine ⟨⟨νw, hprob⟩, fun E hE => ?_, fun F _ => hint F, ?_⟩
  · have h3 : ∫ U, E.indicator (1 : GaugeField _ → ℂ) U ∂νw = (((νw E).toReal : ℝ) : ℂ) := by
      have h4 : E.indicator (1 : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) → ℂ) =
          E.indicator (fun _ => (1 : ℂ)) := rfl
      rw [h4, integral_indicator_const _ hE]
      simp [Measure.real]
    exact h3.symm.trans (hint _)
  · have hG : IsGibbs β νw :=
      (isGibbs_iff_kernel_expect (ν := ⟨νw, hprob⟩) (hf.2.2 ⟨νw, hprob⟩)).mpr
        fun 𝓛 h𝓛 F hF => (hint _).trans ((main 𝓛 h𝓛 F hF).trans (hint F).symm)
    have hT : ∀ v, IsSymmetricUnder νw (shift v) := fun v A hA => by
      have hO2 := isBoundedObservable_mul hO hA
      have E : ν.expect (fun U => h U * (shift v).actOn A U) =
          ν.expect (fun U => h U * A U) := by
        refine Eq.trans ?_ (hinv v _ hO2)
        refine integral_congr_ae (ae_of_all _ fun U => ?_)
        change h U * A ((shift v).pullbackField U) =
          h ((shift v).pullbackField U) * A ((shift v).pullbackField U)
        rw [hfix v U]
      exact (hint _).trans (E.trans (hint A).symm)
    change (⟨νw, hprob⟩ : GaugeFieldProbability _) ∈ periodicGibbsStates L K β
    rw [hs.2.1.1]
    exact ⟨hG, hT⟩
theorem ergodicInvariantFunctionsConstant_holds (a : ℝ) : ErgodicInvariantFunctionsConstant a := by
  intro ρ hρ herg
  have := ρ.2
  have hconst : ∀ J : GaugeField a → ℂ, Measurable[shiftInvariantSigma a] J →
      ∃ c : ℂ, J =ᵐ[ρ.1] fun _ => c := by
    intro J hJ
    refine exists_eventuallyEq_const_of_forall_separating MeasurableSet fun S hS => ?_
    rcases herg.2.2 _ (hJ hS) with h0 | h1
    · right
      exact measure_eq_zero_iff_ae_notMem.mp h0
    · left
      have hm : MeasurableSet (J ⁻¹' S) := shiftInvariantSigma_le a _ (hJ hS)
      exact mem_ae_iff.mpr ((prob_compl_eq_zero_iff hm).mpr h1)
  refine ⟨hconst, fun F hF J hJ => ?_⟩
  obtain ⟨c, hc⟩ := hconst J hJ.1
  have e1 : ∫ U, J U ∂ρ.1 = ρ.expect F := by
    have := hJ.2.2 univ (@MeasurableSet.univ _ (shiftInvariantSigma a))
    simpa [GaugeFieldProbability.expect] using this
  have e2 : ∫ U, J U ∂ρ.1 = c := by
    rw [integral_congr_ae hc]
    simp
  have e3 : ρ.expect F = c := e1.symm.trans e2
  rw [e3]
  exact hc
theorem factorizationImpliesErgodic_holds (hdense : RatPolyAndStateBorelSets)
    (L K : ℕ) (hL : Odd L) (hL13 : 13 ≤ L) (hK : 0 < K)
    (ha : 0 < PeriodicLattice.meshSize L (K : ℤ)) : FactorizationImpliesErgodic L K := by
  intro ρ hρ hfac
  have := ρ.2
  have hd := hdense L K hL hL13 hK
  refine ⟨ρ.2, hρ, fun I hI => ?_⟩
  have hIb : MeasurableSet I := shiftInvariantSigma_le _ _ hI
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (ρ.1 I).toReal := ⟨_, rfl⟩
  have hind := isBoundedObservable_indicator hIb
  have hp0 : 0 ≤ p := hp ▸ ENNReal.toReal_nonneg
  have hp1 : p ≤ 1 := hp ▸ ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have hfacC : ∀ ψ ∈ complexRatPolyObservables (PeriodicLattice.meshSize L (K : ℤ)),
      ρ.expect (fun U => I.indicator (1 : GaugeField _ → ℂ) U * ψ U) =
        (p : ℂ) * ρ.expect ψ := by
    rintro ψ ⟨F₁, h₁, F₂, h₂, hψ⟩
    have o₁ : IsBoundedObservable (fun U => (F₁ U : ℂ)) :=
      isBoundedObservable_of_continuous ha
        (show Continuous (fun U => (F₁ U : ℂ)) ∧ _ from hd.1.2.1 F₁ h₁).1
    have o₂ : IsBoundedObservable (fun U => (F₂ U : ℂ)) :=
      isBoundedObservable_of_continuous ha
        (show Continuous (fun U => (F₂ U : ℂ)) ∧ _ from hd.1.2.1 F₂ h₂).1
    have lin : ∀ χ : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) → ℂ,
        IsBoundedObservable χ →
        ∫ U, χ U * ψ U ∂ρ.1 = (∫ U, χ U * (F₁ U : ℂ) ∂ρ.1) +
          Complex.I * ∫ U, χ U * (F₂ U : ℂ) ∂ρ.1 := by
      intro χ hχ
      have i₁ := integrable_of_isBoundedObservable (isBoundedObservable_mul hχ o₁) ρ.1
      have i₂ := integrable_of_isBoundedObservable (isBoundedObservable_mul hχ o₂) ρ.1
      rw [← integral_const_mul, ← integral_add i₁ (i₂.const_mul _)]
      refine integral_congr_ae (ae_of_all _ fun U => ?_)
      change χ U * ψ U = χ U * (F₁ U : ℂ) + Complex.I * (χ U * (F₂ U : ℂ))
      rw [hψ U]
      ring
    have hone : IsBoundedObservable
        (fun _ : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) => (1 : ℂ)) :=
      ⟨measurable_const, 1, fun _ => by simp⟩
    have l1 := lin _ hind
    have l2 := lin _ hone
    simp only [one_mul] at l2
    have a₁ := hfac I hI F₁ h₁
    have a₂ := hfac I hI F₂ h₂
    change ∫ U, I.indicator (1 : GaugeField _ → ℂ) U * ψ U ∂ρ.1 = (p : ℂ) * ∫ U, ψ U ∂ρ.1
    rw [l1, l2]
    change (∫ U, I.indicator (1 : GaugeField _ → ℂ) U * (F₁ U : ℂ) ∂ρ.1) =
      _ * (∫ U, (F₁ U : ℂ) ∂ρ.1) at a₁
    change (∫ U, I.indicator (1 : GaugeField _ → ℂ) U * (F₂ U : ℂ) ∂ρ.1) =
      _ * (∫ U, (F₂ U : ℂ) ∂ρ.1) at a₂
    rw [a₁, a₂, ← hp]
    ring
  have hpI : ∫ U, I.indicator (1 : GaugeField _ → ℂ) U ∂ρ.1 = (p : ℂ) := by
    have h4 : I.indicator (1 : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) → ℂ) =
        I.indicator (fun _ => (1 : ℂ)) := rfl
    rw [h4, integral_indicator_const _ hIb, hp]
    simp [Measure.real]
  have hmain : ∀ ε : ℝ, 0 < ε → ‖(p : ℂ) - (p : ℂ) ^ 2‖ ≤ 2 * ε := by
    intro ε hε
    obtain ⟨ψ, hψ, -, hψ1⟩ := hd.2.1 ρ (I.indicator 1) hind ε hε
    have hψo : IsBoundedObservable ψ :=
      isBoundedObservable_of_continuous ha (continuous_and_cylinder_of_mem_complexRatPoly hd.1 hψ).1
    have i₁ := integrable_of_isBoundedObservable hind ρ.1
    have i₂ := integrable_of_isBoundedObservable hψo ρ.1
    have i₃ := integrable_of_isBoundedObservable (isBoundedObservable_mul hind hψo) ρ.1
    have hb₁ : ‖(p : ℂ) - ∫ U, ψ U ∂ρ.1‖ ≤ ε := by
      rw [← hpI, ← integral_sub i₁ i₂]
      exact (norm_integral_le_integral_norm _).trans hψ1
    have hb₂ : ‖(p : ℂ) - ∫ U, I.indicator (1 : GaugeField _ → ℂ) U * ψ U ∂ρ.1‖ ≤ ε := by
      have e : (p : ℂ) = ∫ U, I.indicator (1 : GaugeField _ → ℂ) U *
          I.indicator (1 : GaugeField _ → ℂ) U ∂ρ.1 := by
        rw [← hpI]
        refine integral_congr_ae (ae_of_all _ fun U => ?_)
        by_cases h : U ∈ I <;> simp [h]
      rw [e, ← integral_sub
        (integrable_of_isBoundedObservable (isBoundedObservable_mul hind hind) ρ.1) i₃]
      refine (norm_integral_le_of_norm_le (i₁.sub i₂).norm (ae_of_all _ fun U => ?_)).trans hψ1
      rw [← mul_sub, norm_mul]
      have hle : ‖I.indicator (1 : GaugeField _ → ℂ) U‖ ≤ 1 := by
        by_cases h : U ∈ I <;> simp [h]
      calc _ ≤ 1 * ‖I.indicator (1 : GaugeField _ → ℂ) U - ψ U‖ :=
            mul_le_mul_of_nonneg_right hle (norm_nonneg _)
        _ = _ := one_mul _
    have hf := hfacC ψ hψ
    change ∫ U, I.indicator (1 : GaugeField _ → ℂ) U * ψ U ∂ρ.1 =
      (p : ℂ) * ∫ U, ψ U ∂ρ.1 at hf
    rw [hf] at hb₂
    have hsplit : (p : ℂ) - (p : ℂ) ^ 2 =
        ((p : ℂ) - (p : ℂ) * ∫ U, ψ U ∂ρ.1) - (p : ℂ) * ((p : ℂ) - ∫ U, ψ U ∂ρ.1) := by ring
    rw [hsplit]
    have hpn : ‖(p : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp0]
      exact hp1
    have hm : ‖(p : ℂ) * ((p : ℂ) - ∫ U, ψ U ∂ρ.1)‖ ≤ ε := by
      rw [norm_mul]
      calc _ ≤ 1 * ε := mul_le_mul hpn hb₁ (norm_nonneg _) zero_le_one
        _ = ε := one_mul ε
    have := norm_sub_le ((p : ℂ) - (p : ℂ) * ∫ U, ψ U ∂ρ.1)
      ((p : ℂ) * ((p : ℂ) - ∫ U, ψ U ∂ρ.1))
    linarith
  have hz : ‖(p : ℂ) - (p : ℂ) ^ 2‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖(p : ℂ) - (p : ℂ) ^ 2‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have := hmain (‖(p : ℂ) - (p : ℂ) ^ 2‖ / 4) (by positivity)
    linarith
  have hzero : p - p ^ 2 = 0 := by exact_mod_cast norm_eq_zero.mp hz
  have hfact : p * (1 - p) = 0 := by linarith [hzero, show p * (1 - p) = p - p ^ 2 by ring]
  rcases mul_eq_zero.mp hfact with h0 | h1
  · left
    rw [hp] at h0
    exact ((ENNReal.toReal_eq_zero_iff _).mp h0).resolve_right (measure_ne_top _ _)
  · right
    have h2 : p = 1 := by linarith
    rw [hp] at h2
    exact (ENNReal.toReal_eq_one_iff _).mp h2
theorem shiftInvarianceAndErgodicity_holds (h₁ : RatPolyAndStateBorelSets)
    (h₂ : WilsonOperatorProperties)
    (h₃ : PeriodicStatesAllScales.AllScalesAllCouplings) : ShiftInvarianceAndErgodicity := by
  intro L K hL hL13 hK
  exact ⟨shiftsComposeOnFields_holds _, invariantSetsFormSigmaAlgebra_holds _,
    invariantMeasurableIffFixed_holds _, aeInvariantAgreesOnInvariantSet_holds _,
    condExpAndPlateau_holds _, invariantDensitiesPreserveGibbs_holds h₁ h₂ h₃ L K hL hL13 hK _,
    ergodicInvariantFunctionsConstant_holds _,
    factorizationImpliesErgodic_holds h₁ L K hL hL13 hK (meshSize_pos (by omega) K)⟩
end YangMills.Construction.InfiniteLattice.ShiftInvariance
