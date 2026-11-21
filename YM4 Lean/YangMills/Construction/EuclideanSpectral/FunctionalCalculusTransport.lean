import YangMills.Construction.InfiniteLattice.ReflectionPositivityInTheFullFormFromContinuousLocalFunctionsProof
import YangMills.Construction.EuclideanSpectral.FunctionalCalculus
import YangMills.Construction.SpectralTheory.BorelFunctionalCalculusTheorem
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.EuclideanSpectral.FunctionalCalculus
open YangMills.Construction.EuclideanSpectral YangMills.Construction.EuclideanSpectral.SpectralMeasure
open YangMills.Construction.BorelCalculus (BoundedFunctionalCalculus StrongConvergence
  UnboundedFunctionalCalculus KernelAndPositivity IsBoundedFn HasDomainAndAction conjFn)
variable {Y H : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem diagMeasure_eq_ofReal_norm_sq (F : SpectralMeasure Y H) (v : H) (S : BorelSubsets Y) :
    F.diagMeasure v S.1 = ENNReal.ofReal (‖F S v‖ ^ 2) := by
  have h : F.diagMeasure v S.1 = ENNReal.ofReal (F.diagMass v ⟨S.1, S.2⟩).re :=
    Measure.ofMeasurable_apply _ S.2
  rw [h, diagMass_eq_norm_sq, Complex.ofReal_re]
theorem apply_mul_apply_self (F : SpectralMeasure Y H) (S : BorelSubsets Y) :
    F S * F S = F S := by
  have h := F.map_inter S S
  have hu : (⟨S.1 ∩ S.1, S.2.inter S.2⟩ : BorelSubsets Y) = S := Subtype.ext (inter_self _)
  rwa [hu] at h
theorem apply_eq_zero_of_diagMeasure (F : SpectralMeasure Y H) (S : BorelSubsets Y)
    (h : ∀ v, F.diagMeasure v S.1 = 0) : F S = 0 := by
  ext v
  have hv := h v
  rw [diagMeasure_eq_ofReal_norm_sq, ENNReal.ofReal_eq_zero] at hv
  have h0 : ‖F S v‖ ^ 2 = 0 := le_antisymm hv (by positivity)
  simpa using h0
theorem ext_inner_self {A B : H →L[ℂ] H} (h : ∀ v, ⟪v, A v⟫_ℂ = ⟪v, B v⟫_ℂ) : A = B := by
  have h0 : ((A - B : H →L[ℂ] H) : H →ₗ[ℂ] H) = 0 := by
    rw [← inner_map_self_eq_zero]
    intro v
    have hd : ⟪v, (A - B) v⟫_ℂ = 0 := by
      rw [sub_apply, inner_sub_right, h v, sub_self]
    have hc := inner_conj_symm (𝕜 := ℂ) ((A - B) v) v
    rw [hd, map_zero] at hc
    exact hc.symm
  have h1 : A - B = 0 := by
    ext v
    exact congrArg (fun T : H →ₗ[ℂ] H => T v) h0
  exact sub_eq_zero.mp h1
instance instIsFiniteMeasureDiagMeasure (F : SpectralMeasure Y H) (v : H) :
    IsFiniteMeasure (F.diagMeasure v) :=
  ⟨(diagMeasure_eq_ofReal_norm_sq F v ⟨univ, MeasurableSet.univ⟩).trans_lt ENNReal.ofReal_lt_top⟩
theorem diagMeasure_real_eq_diagMass (F : SpectralMeasure Y H) (v : H) (S : BorelSubsets Y) :
    (((F.diagMeasure v).real S.1 : ℝ) : ℂ) = F.diagMass v S := by
  rw [Measure.real, diagMeasure_eq_ofReal_norm_sq, ENNReal.toReal_ofReal (by positivity),
    diagMass_eq_norm_sq]
theorem valuesAndDiagMeasures (F : SpectralMeasure Y H) : ValuesAndDiagMeasures F where
  isOrthProjection S := ⟨F.selfAdjoint S, apply_mul_apply_self F S⟩
  diagMass_eq := F.diagMass_eq_norm_sq
  isFiniteMeasure v := inferInstance
  real_apply := diagMeasure_real_eq_diagMass F
  real_univ v := by
    rw [Measure.real]
    have h := diagMeasure_eq_ofReal_norm_sq F v ⟨univ, MeasurableSet.univ⟩
    rw [F.map_univ] at h
    have h' : F.diagMeasure v univ = ENNReal.ofReal (‖v‖ ^ 2) := by simpa using h
    rw [h', ENNReal.toReal_ofReal (by positivity)]
  apply_empty := by
    refine apply_eq_zero_of_diagMeasure F _ fun v => ?_
    exact measure_empty
  apply_union S S' hd := by
    refine ext_inner_self fun v => ?_
    have hr : (F.diagMeasure v).real (S.1 ∪ S'.1) =
        (F.diagMeasure v).real S.1 + (F.diagMeasure v).real S'.1 :=
      measureReal_union hd S'.2
    have h₀ := diagMeasure_real_eq_diagMass F v ⟨S.1 ∪ S'.1, S.2.union S'.2⟩
    have h₁ := diagMeasure_real_eq_diagMass F v S
    have h₂ := diagMeasure_real_eq_diagMass F v S'
    simp only [diagMass] at h₀ h₁ h₂
    rw [add_apply, inner_add_right, ← h₀, ← h₁, ← h₂, hr]
    push_cast
    rfl
  apply_iUnion S h := by
    refine apply_eq_zero_of_diagMeasure F _ fun v => ?_
    refine measure_iUnion_null fun n => ?_
    rw [diagMeasure_eq_ofReal_norm_sq F v (S n), h n]
    simp
theorem pushforwardDiagMeasures (F : SpectralMeasure Y H) : PushforwardDiagMeasures F := by
  intro Z _ _ _ hZ f hf v
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply hf hs]
  have h₁ := diagMeasure_eq_ofReal_norm_sq (F.pushforward hZ f hf) v ⟨s, hs⟩
  have h₂ := diagMeasure_eq_ofReal_norm_sq F v ⟨f ⁻¹' s, hf hs⟩
  exact h₁.trans h₂.symm
theorem supportLaws (F : SpectralMeasure Y H) : SupportLaws F := by
  obtain ⟨n, ι, hι, -⟩ := F.borelSubset
  have : SecondCountableTopology Y := hι.secondCountableTopology
  let S : Set (Set Y) := {O | IsOpen O ∧ ∀ v, F.diagMeasure v O = 0}
  have hcompl : F.suppᶜ = ⋃₀ S := by
    ext y
    constructor
    · intro hy
      simp only [supp, mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_not] at hy
      obtain ⟨O, hO, hyO, h⟩ := hy
      refine ⟨O, ⟨hO, fun v => ?_⟩, hyO⟩
      have h₁ := diagMeasure_eq_ofReal_norm_sq F v ⟨O, hO.measurableSet⟩
      rw [h] at h₁
      simpa using h₁
    · rintro ⟨O, ⟨hO, h⟩, hyO⟩ hy
      exact hy O hO hyO (apply_eq_zero_of_diagMeasure F ⟨O, hO.measurableSet⟩ h)
  obtain ⟨T, hTc, hTS, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable S fun O hO => hO.1
  have hnull : ∀ v, F.diagMeasure v F.suppᶜ = 0 := fun v => by
    rw [hcompl, ← hTU]
    exact (measure_sUnion_null_iff hTc).mpr fun O hO => (hTS hO).2 v
  refine ⟨apply_eq_zero_of_diagMeasure F _ hnull, fun Y₁ h₁ => ⟨fun hs => ?_, fun hc y hy => ?_⟩⟩
  · exact apply_eq_zero_of_diagMeasure F _ fun v =>
      measure_mono_null (compl_subset_compl.mpr hs) (hnull v)
  · by_contra hy₁
    exact hy Y₁ᶜ h₁.isOpen_compl hy₁ hc
theorem exists_measurableEquiv_euclidean (F : SpectralMeasure Y H) :
    ∃ (m : ℕ) (Y₀ : Set (Fin m → ℝ)), 1 ≤ m ∧ MeasurableSet Y₀ ∧ Nonempty (Y ≃ᵐ Y₀) := by
  obtain ⟨n, ι, hι, hr⟩ := F.borelSubset
  let c : EuclideanSpace ℝ (Fin n) → (Fin (n + 1) → ℝ) := fun x => Fin.cons 0 fun k => x k
  let d : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ (Fin n) := fun w => WithLp.toLp 2 fun k => w k.succ
  have hdc : Function.LeftInverse d c := fun x => by
    ext k
    simp [c, d]
  have hcc : Continuous c := by
    refine continuous_pi fun i => ?_
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa [c] using continuous_const
    · simpa [c] using (EuclideanSpace.proj (𝕜 := ℝ) k).continuous
  have hdd : Continuous d := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => continuous_apply _)
  have hc : IsClosedEmbedding c := hdc.isClosedEmbedding hdd hcc
  have hj : IsEmbedding (c ∘ ι) := hc.isEmbedding.comp hι
  have hrange : MeasurableSet (range (c ∘ ι)) := by
    rw [range_comp]
    exact hc.measurableEmbedding.measurableSet_image' hr
  exact ⟨n + 1, range (c ∘ ι), Nat.succ_le_succ (Nat.zero_le _), hrange,
    ⟨(hj.measurableEmbedding hrange).equivRange⟩⟩
theorem integral_norm_sq_eq_toReal {X : Type*} [MeasurableSpace X] (μ : Measure X) {φ : X → ℂ}
    (hφ : Measurable φ) : ∫ y, ‖φ y‖ ^ 2 ∂μ = (∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ).toReal := by apply _root_.YangMills.Construction.GibbsAtFixedSpacing.FullReflectionPositivityFromContinuousLocal.secondMoment_eq_toReal_lintegral <;> assumption
theorem ennreal_add_sq_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 4 * a ^ 2 + 4 * b ^ 2 := by
  have h₁ : a + b ≤ 2 * max a b := by
    rw [two_mul]
    exact add_le_add (le_max_left _ _) (le_max_right _ _)
  have h₂ : (max a b) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]
      exact le_add_self
    · rw [max_eq_left h]
      exact le_self_add
  calc (a + b) ^ 2 ≤ (2 * max a b) ^ 2 := pow_le_pow_left' h₁ 2
    _ = 4 * (max a b) ^ 2 := by rw [mul_pow]; norm_num
    _ ≤ 4 * (a ^ 2 + b ^ 2) := by gcongr
    _ = 4 * a ^ 2 + 4 * b ^ 2 := by rw [mul_add]
theorem mem_calculusDomain_linComb (F : SpectralMeasure Y H) {φ φ' : Y → ℂ}
    (hφ : Measurable φ) (hφ' : Measurable φ') (α α' : ℂ) {v : H}
    (hv : v ∈ F.calculusDomain φ ∩ F.calculusDomain φ') :
    v ∈ F.calculusDomain (α • φ + α' • φ') := by
  have h₁ : ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂F.diagMeasure v < ∞ := hv.1
  have h₂ : ∫⁻ y, ‖φ' y‖ₑ ^ 2 ∂F.diagMeasure v < ∞ := hv.2
  have hle : ∀ y, ‖(α • φ + α' • φ') y‖ₑ ^ 2 ≤
      (4 * ‖α‖ₑ ^ 2) * ‖φ y‖ₑ ^ 2 + (4 * ‖α'‖ₑ ^ 2) * ‖φ' y‖ₑ ^ 2 := fun y => by
    have h : ‖(α • φ + α' • φ') y‖ₑ ≤ ‖α‖ₑ * ‖φ y‖ₑ + ‖α'‖ₑ * ‖φ' y‖ₑ := by
      refine (enorm_add_le _ _).trans ?_
      simp only [Pi.smul_apply, enorm_smul, le_refl]
    calc ‖(α • φ + α' • φ') y‖ₑ ^ 2 ≤ (‖α‖ₑ * ‖φ y‖ₑ + ‖α'‖ₑ * ‖φ' y‖ₑ) ^ 2 :=
          pow_le_pow_left' h 2
      _ ≤ 4 * (‖α‖ₑ * ‖φ y‖ₑ) ^ 2 + 4 * (‖α'‖ₑ * ‖φ' y‖ₑ) ^ 2 := ennreal_add_sq_le _ _
      _ = _ := by simp only [mul_pow, mul_assoc]
  have hm : Measurable fun y => (4 * ‖α‖ₑ ^ 2) * ‖φ y‖ₑ ^ 2 :=
    (hφ.enorm.pow_const 2).const_mul _
  have hc : ∀ a : ℂ, 4 * ‖a‖ₑ ^ 2 ≠ ∞ := fun a =>
    ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top enorm_ne_top)
  show ∫⁻ y, ‖(α • φ + α' • φ') y‖ₑ ^ 2 ∂F.diagMeasure v < ∞
  refine (lintegral_mono hle).trans_lt ?_
  rw [lintegral_add_left hm, lintegral_const_mul _ (hφ.enorm.pow_const 2),
    lintegral_const_mul _ (hφ'.enorm.pow_const 2)]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (hc α).lt_top h₁,
    ENNReal.mul_lt_top (hc α').lt_top h₂⟩
theorem calculusOperator_pushforward (F : SpectralMeasure Y H) {Z : Type}
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (hZ : IsEuclideanBorel Z) (f : Y → Z) (hf : Measurable f) (φ' : Z → ℂ)
    (hφ' : Measurable φ') :
    (F.pushforward hZ f hf).calculusOperator φ' = F.calculusOperator (φ' ∘ f) := by
  have hmeas : ∀ v, (F.pushforward hZ f hf).diagMeasure v = (F.diagMeasure v).map f :=
    fun v => pushforwardDiagMeasures F Z hZ f hf v
  have hd : (F.pushforward hZ f hf).calculusDomain φ' = F.calculusDomain (φ' ∘ f) := by
    ext v
    show ∫⁻ y, ‖φ' y‖ₑ ^ 2 ∂(F.pushforward hZ f hf).diagMeasure v < ∞ ↔
      ∫⁻ y, ‖(φ' ∘ f) y‖ₑ ^ 2 ∂F.diagMeasure v < ∞
    rw [hmeas, lintegral_map (hφ'.enorm.pow_const 2) hf]
    rfl
  have hb : ∀ g : Z → ℂ, Measurable g →
      (F.pushforward hZ f hf).boundedCalculus g = F.boundedCalculus (g ∘ f) := fun g hg => by
    unfold boundedCalculus
    congr 1
    funext B
    refine propext (forall_congr' fun v => ?_)
    rw [hmeas, integral_map hf.aemeasurable hg.aestronglyMeasurable]
    rfl
  have ht : ∀ n, Measurable (truncate φ' n) := fun n =>
    hφ'.indicator (measurableSet_le hφ'.norm measurable_const)
  have hc : ∀ n, truncate φ' n ∘ f = truncate (φ' ∘ f) n := fun n => rfl
  have hl : (F.pushforward hZ f hf).calculusLimit φ' = F.calculusLimit (φ' ∘ f) := by
    funext v
    unfold calculusLimit
    simp only [hb _ (ht _), hc]
  unfold calculusOperator IsCalculusOperator
  rw [hd, hl]
section Transport
variable {m : ℕ} {Y₀ : Set (Fin m → ℝ)}
def transport (F : SpectralMeasure Y H) (hm : 1 ≤ m) (hY₀ : MeasurableSet Y₀)
    (e : Y ≃ᵐ Y₀) : BorelSpectral.SpectralMeasure Y₀ H where
  one_le_dimension := hm
  measurableSet_carrier := hY₀
  toFun S := F ⟨e ⁻¹' S.1, e.measurable S.2⟩
  isStarProjection S :=
    ⟨apply_mul_apply_self F _, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun x y =>
      (F.selfAdjoint _ x y).symm⟩
  map_univ := F.map_univ
  map_inter S S' :=
    (F.map_inter ⟨e ⁻¹' S.1, e.measurable S.2⟩ ⟨e ⁻¹' S'.1, e.measurable S'.2⟩).symm
  countablyAdditive v S hd := by
    have h := F.countablyAdditive v (fun k => ⟨e ⁻¹' (S k).1, e.measurable (S k).2⟩)
      (fun k l hkl => (hd hkl).preimage e)
    have hu : (⟨e ⁻¹' ⋃ k, (S k).1, e.measurable (MeasurableSet.iUnion fun k => (S k).2)⟩ :
        BorelSubsets Y) = ⟨⋃ k, e ⁻¹' (S k).1, MeasurableSet.iUnion fun k => e.measurable (S k).2⟩ :=
      Subtype.ext preimage_iUnion
    simpa only [hu] using h
variable {F : SpectralMeasure Y H} {e : Y ≃ᵐ Y₀}
  {E : BorelSpectral.SpectralMeasure Y₀ H}
theorem diagMeasure_transport (hE : ∀ S, E S = F ⟨e ⁻¹' S.1, e.measurable S.2⟩) (v : H) :
    E.diagMeasure v = (F.diagMeasure v).map e := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply e.measurable hs]
  have h₁ := E.diagMeasure_apply v ⟨s, hs⟩
  have h₂ := diagMeasure_eq_ofReal_norm_sq F v ⟨e ⁻¹' s, e.measurable hs⟩
  rw [hE] at h₁
  exact h₁.trans h₂.symm
theorem integral_transport (hE : ∀ S, E S = F ⟨e ⁻¹' S.1, e.measurable S.2⟩) {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] (f : Y → G) (v : H) :
    ∫ y, (f ∘ e.symm) y ∂E.diagMeasure v = ∫ y, f y ∂F.diagMeasure v := by
  rw [diagMeasure_transport hE, e.measurableEmbedding.integral_map]
  simp
theorem lintegral_transport (hE : ∀ S, E S = F ⟨e ⁻¹' S.1, e.measurable S.2⟩) (f : Y → ℝ≥0∞)
    (v : H) : ∫⁻ y, (f ∘ e.symm) y ∂E.diagMeasure v = ∫⁻ y, f y ∂F.diagMeasure v := by
  rw [diagMeasure_transport hE, e.measurableEmbedding.lintegral_map]
  simp
theorem isDiagonalIntegral_iff (hE : ∀ S, E S = F ⟨e ⁻¹' S.1, e.measurable S.2⟩) (φ : Y → ℂ)
    (B : H →L[ℂ] H) : E.IsDiagonalIntegral (φ ∘ e.symm) B ↔ F.IsBoundedCalculus φ B := by
  refine forall_congr' fun v => ?_
  rw [integral_transport hE]
theorem integralOp_transport (hE : ∀ S, E S = F ⟨e ⁻¹' S.1, e.measurable S.2⟩)
    (φ : Y → ℂ) : E.integralOp (φ ∘ e.symm) = F.boundedCalculus φ := by
  unfold BorelSpectral.SpectralMeasure.integralOp boundedCalculus
  congr 1
  funext B
  exact propext (isDiagonalIntegral_iff hE φ B)
theorem integralDom_transport (hE : ∀ S, E S = F ⟨e ⁻¹' S.1, e.measurable S.2⟩)
    (φ : Y → ℂ) : E.integralDom (φ ∘ e.symm) = F.calculusDomain φ := by
  ext v
  exact iff_of_eq (congrArg (· < ∞) (lintegral_transport hE (fun y => ‖φ y‖ₑ ^ 2) v))
theorem truncate_transport (φ : Y → ℂ) (n : ℕ) :
    BorelSpectral.truncate (φ ∘ e.symm) n = truncate φ n ∘ e.symm :=
  rfl
theorem integralApply_transport (hE : ∀ S, E S = F ⟨e ⁻¹' S.1, e.measurable S.2⟩)
    (φ : Y → ℂ) (v : H) : E.integralApply (φ ∘ e.symm) v = F.calculusLimit φ v := by
  unfold BorelSpectral.SpectralMeasure.integralApply calculusLimit
  simp only [truncate_transport, integralOp_transport hE]
theorem measurable_comp_symm {φ : Y → ℂ} (hφ : Measurable φ) : Measurable (φ ∘ e.symm) :=
  hφ.comp e.symm.measurable
theorem isBoundedFn_comp_symm {φ : Y → ℂ} {c : ℝ} (hc : ∀ y, ‖φ y‖ ≤ c) :
    IsBoundedFn (φ ∘ e.symm) :=
  ⟨c, fun _ => hc _⟩
theorem isCarriedBy_univ (hb : BoundedFunctionalCalculus E) :
    E.IsCarriedBy ⟨univ, MeasurableSet.univ⟩ :=
  (congrArg E.toFun (Subtype.ext compl_univ)).trans hb.apply_empty
theorem boundedCalculusLaws (hE : ∀ S, E S = F ⟨e ⁻¹' S.1, e.measurable S.2⟩)
    (hb : BoundedFunctionalCalculus E) : BoundedCalculusLaws F := by
  have mp : ∀ {φ : Y → ℂ}, IsBoundedMeasurable φ → Measurable (φ ∘ e.symm) :=
    fun h => measurable_comp_symm h.1
  have bp : ∀ {φ : Y → ℂ}, IsBoundedMeasurable φ → IsBoundedFn (φ ∘ e.symm) :=
    fun h => by
      obtain ⟨_, c, hc⟩ := h
      exact isBoundedFn_comp_symm hc
  have hEU : ∀ φ : Y → ℂ, IsBoundedMeasurable φ → ∃! B : H →L[ℂ] H, F.IsBoundedCalculus φ B :=
    fun φ hφ => by
      have h := hb.existsUnique_op _ (mp hφ) (bp hφ)
      simpa only [isDiagonalIntegral_iff hE] using h
  have bI := integralOp_transport hE
  refine
    { existsUnique := hEU
      isBoundedCalculus := fun φ hφ => Classical.epsilon_spec (hEU φ hφ).exists
      add := fun φ φ' h h' => ?_
      smul := fun α φ h => ?_
      mul := fun φ φ' h h' => ?_
      isAdjointPair := fun φ h χ v => ?_
      indicator := fun S => ?_
      norm_sq := fun φ h v => ?_
      integral_le := fun φ h v => ?_
      diagMeasure_real_apply := fun φ h v S => ?_ }
  · rw [← bI (φ + φ'), ← bI φ, ← bI φ']
    exact hb.add _ _ (mp h) (bp h) (mp h') (bp h')
  · rw [← bI (α • φ), ← bI φ]
    exact hb.smul α _ (mp h) (bp h)
  · rw [← bI (φ * φ'), ← bI φ, ← bI φ']
    exact hb.mul _ _ (mp h) (bp h) (mp h') (bp h')
  · have hconj := hb.star_eq _ (mp h) (bp h)
    have hcf : (fun y => (starRingEnd ℂ) (φ y)) ∘ e.symm = conjFn (φ ∘ e.symm) := rfl
    rw [← bI φ, ← bI (fun y => (starRingEnd ℂ) (φ y)), hcf, hconj,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  · have h := hb.indicator ⟨e.symm ⁻¹' S.1, e.symm.measurable S.2⟩
    have h₁ : (e.symm ⁻¹' S.1).indicator (1 : Y₀ → ℂ) = S.1.indicator 1 ∘ e.symm := by
      funext y
      simp only [indicator, Pi.one_apply, Function.comp_apply]
      rfl
    rw [show (⟨e.symm ⁻¹' S.1, e.symm.measurable S.2⟩ : BorelSubsets Y₀).1 = e.symm ⁻¹' S.1 from rfl,
      h₁, bI, hE] at h
    rw [h]
    congr 1
    exact Subtype.ext (by ext y; simp)
  · have h₁ := hb.norm_sq _ (mp h) (bp h) v
    rw [bI] at h₁
    rw [h₁]
    exact integral_transport hE (fun y => ‖φ y‖ ^ 2) v
  · have h₁ := hb.integral_le _ (mp h) (bp h) v
    have hS : ⨆ y, ‖(φ ∘ e.symm) y‖ = ⨆ y, ‖φ y‖ :=
      e.symm.toEquiv.iSup_comp (g := fun y => ‖φ y‖)
    rw [← integral_transport hE (fun y => ‖φ y‖ ^ 2) v, ← hS]
    exact h₁
  · have hmeas : Measurable fun y => ‖(φ ∘ e.symm) y‖ₑ ^ 2 := (mp h).enorm.pow_const 2
    have key := hb.diagMeasure_eq _ (mp h) (bp h) v ⟨e.symm ⁻¹' S.1, e.symm.measurable S.2⟩
    rw [bI] at key
    simp only at key
    rw [diagMeasure_transport hE, diagMeasure_transport hE,
      Measure.map_apply e.measurable (e.symm.measurable S.2),
      setLIntegral_map (e.symm.measurable S.2) hmeas e.measurable] at key
    have hpre : e ⁻¹' (e.symm ⁻¹' S.1) = S.1 := by
      ext y
      simp
    rw [hpre] at key
    have hcomp : ∀ y, ‖(φ ∘ e.symm) (e y)‖ₑ ^ 2 = ‖φ y‖ₑ ^ 2 := fun y => by simp
    simp only [hcomp] at key
    rw [Measure.real, key, integral_norm_sq_eq_toReal _ h.1]
theorem dominatedStrongConvergence (hE : ∀ S, E S = F ⟨e ⁻¹' S.1, e.measurable S.2⟩)
    (hb : BoundedFunctionalCalculus E) (hs : StrongConvergence E) :
    DominatedStrongConvergence F := by
  intro f φ c hf hc hl v
  have hφ : Measurable φ := measurable_of_tendsto_metrizable hf (tendsto_pi_nhds.mpr hl)
  have hcφ : ∀ y, ‖φ y‖ ≤ c := fun y =>
    le_of_tendsto (hl y).norm (Eventually.of_forall fun n => hc n y)
  have h := (hs (fun n => f n ∘ e.symm) (φ ∘ e.symm) c ⟨univ, MeasurableSet.univ⟩
    (fun n => measurable_comp_symm (hf n)) (measurable_comp_symm hφ) (fun n y => hc n _)
    (isCarriedBy_univ hb) (fun y _ => hl _)).2 v
  rw [E.integralApply_eq_integralOp (g := φ ∘ e.symm) (fun y => hcφ _),
    integralOp_transport hE] at h
  simpa only [integralOp_transport hE] using h
theorem realBoundedCalculus (hE : ∀ S, E S = F ⟨e ⁻¹' S.1, e.measurable S.2⟩)
    (hb : BoundedFunctionalCalculus E) (hk : KernelAndPositivity E) : RealBoundedCalculus F := by
  have hsa : ∀ φ : Y → ℝ, Measurable φ → (∃ c : ℝ, ∀ y, |φ y| ≤ c) →
      IsSelfAdjointOp (F.boundedCalculus fun y => (φ y : ℂ)) := by
    rintro φ hφ ⟨c, hc⟩ χ v
    have hm : Measurable fun y => (φ y : ℂ) := Complex.measurable_ofReal.comp hφ
    have h := hb.isSelfAdjoint _ (measurable_comp_symm (e := e) hm)
      (isBoundedFn_comp_symm (c := c) fun y => by simpa using hc y) fun y => Complex.ofReal_im _
    rw [integralOp_transport hE] at h
    exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp h χ v).symm
  refine ⟨hsa, ?_⟩
  rintro φ hφ ⟨c, hc⟩ hge
  have hm : Measurable fun y => (φ y : ℂ) := Complex.measurable_ofReal.comp hφ
  have hgm := measurable_comp_symm (e := e) hm
  have hnn := (hk.nonneg_iff _ hgm fun y => Complex.ofReal_im _).mp fun v _ => by
    rw [E.integralApply_eq_integralOp (c := c) (fun y => by simpa using hc _),
      integralOp_transport hE]
    have hre := hge v
    simp only [scalarOp, Complex.ofReal_zero, zero_smul, zero_apply,
      inner_zero_right, Complex.zero_re] at hre
    have hsym := hsa φ hφ ⟨c, hc⟩ v v
    have him : (⟪v, (F.boundedCalculus fun y => (φ y : ℂ)) v⟫_ℂ).im = 0 := by
      have hconj := inner_conj_symm (𝕜 := ℂ) v ((F.boundedCalculus fun y => (φ y : ℂ)) v)
      rw [← hsym] at hconj
      exact Complex.conj_eq_iff_im.mp hconj
    exact Complex.le_def.mpr ⟨by simpa using hre, by simpa using him.symm⟩
  rw [hE] at hnn
  refine Eq.trans (congrArg F.toFun (Subtype.ext ?_)) hnn
  ext y
  simp [YangMills.Construction.BorelCalculus.negativeLocus]
theorem calculusLimit_linComb (hE : ∀ S, E S = F ⟨e ⁻¹' S.1, e.measurable S.2⟩)
    (hb : BoundedFunctionalCalculus E) (hs : StrongConvergence E)
    (hu : UnboundedFunctionalCalculus E) {φ φ' : Y → ℂ}
    (hφ : Measurable φ) (hφ' : Measurable φ') (α α' : ℂ) {v : H}
    (hv : v ∈ F.calculusDomain φ ∩ F.calculusDomain φ') :
    F.calculusLimit (α • φ + α' • φ') v = α • F.calculusLimit φ v + α' • F.calculusLimit φ' v := by
  have hg := measurable_comp_symm (e := e) hφ
  have hg' := measurable_comp_symm (e := e) hφ'
  have hvg : v ∈ E.integralDom (φ ∘ e.symm) := by
    rw [integralDom_transport hE]
    exact hv.1
  have hvg' : v ∈ E.integralDom (φ' ∘ e.symm) := by
    rw [integralDom_transport hE]
    exact hv.2
  have hvu : v ∈ E.integralDom ((α • φ + α' • φ') ∘ e.symm) := by
    rw [integralDom_transport hE]
    exact mem_calculusDomain_linComb F hφ hφ' α α' hv
  have hum : Measurable ((α • φ + α' • φ') ∘ e.symm) :=
    measurable_comp_symm ((hφ.const_smul α).add (hφ'.const_smul α'))
  rw [← integralApply_transport hE, ← integralApply_transport hE,
    ← integralApply_transport hE]
  generalize hgdef : φ ∘ e.symm = g at *
  generalize hg'def : φ' ∘ e.symm = g' at *
  have hudef : (α • φ + α' • φ') ∘ e.symm = α • g + α' • g' := by
    rw [← hgdef, ← hg'def]
    rfl
  rw [hudef] at hvu hum ⊢
  let W : ℕ → Set Y₀ := fun n => {y | ‖g y‖ ≤ n ∧ ‖g' y‖ ≤ n}
  have hW : ∀ n, MeasurableSet (W n) := fun n =>
    (measurableSet_le hg.norm measurable_const).inter (measurableSet_le hg'.norm measurable_const)
  let b : ℕ → Y₀ → ℂ := fun n => (W n).indicator 1
  have hbm : ∀ n, Measurable (b n) := fun n => measurable_one.indicator (hW n)
  have hbb : ∀ n y, ‖b n y‖ ≤ 1 := fun n y => by
    by_cases hy : y ∈ W n
    · simp [b, indicator_of_mem hy]
    · simp [b, indicator_of_notMem hy]
  have hbB : ∀ n, IsBoundedFn (b n) := fun n => ⟨1, hbb n⟩
  have bdd : ∀ (f : Y₀ → ℂ) (C : ℝ) (n : ℕ), 0 ≤ C → (∀ y ∈ W n, ‖f y‖ ≤ C) →
      IsBoundedFn (f * b n) := fun f C n hC hf => ⟨C, fun y => by
    by_cases hy : y ∈ W n
    · simpa [b, indicator_of_mem hy] using hf y hy
    · simpa [b, indicator_of_notMem hy] using hC⟩
  have hB₁ : ∀ n, IsBoundedFn (g * b n) := fun n =>
    bdd g n n (Nat.cast_nonneg n) fun y hy => hy.1
  have hB₂ : ∀ n, IsBoundedFn (g' * b n) := fun n =>
    bdd g' n n (Nat.cast_nonneg n) fun y hy => hy.2
  have hB₃ : ∀ n, IsBoundedFn ((α • g + α' • g') * b n) := fun n =>
    bdd _ (‖α‖ * n + ‖α'‖ * n) n (by positivity) fun y hy => by
      refine (norm_add_le _ _).trans ?_
      simp only [Pi.smul_apply, norm_smul]
      exact add_le_add (mul_le_mul_of_nonneg_left hy.1 (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hy.2 (norm_nonneg _))
  have key : ∀ (f : Y₀ → ℂ) (n : ℕ), Measurable f → IsBoundedFn (f * b n) →
      v ∈ E.integralDom f →
      E.integralOp (b n) (E.integralApply f v) = E.integralOp (f * b n) v := by
    intro f n hf hB hvf
    rw [← hu.integralApply_integralOp f (b n) hf (hbm n) (hbB n) v hvf]
    exact (hu.range_subset_dom f (b n) hf (hbm n) (hbB n) hB v).2
  have hsm : ∀ (a : ℂ) {f : Y₀ → ℂ}, IsBoundedFn f → IsBoundedFn (a • f) := by
    rintro a f ⟨c, hc⟩
    exact ⟨‖a‖ * c, fun y => by
      rw [Pi.smul_apply, norm_smul]
      exact mul_le_mul_of_nonneg_left (hc y) (norm_nonneg _)⟩
  have hub : ∀ n, E.integralOp (b n) (α • E.integralApply g v + α' • E.integralApply g' v) =
      E.integralOp (b n) (E.integralApply (α • g + α' • g') v) := fun n => by
    have hprod : (α • g + α' • g') * b n = α • (g * b n) + α' • (g' * b n) := by
      funext y
      simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hm₁ : Measurable (g * b n) := hg.mul (hbm n)
    have hm₂ : Measurable (g' * b n) := hg'.mul (hbm n)
    rw [key _ n hum (hB₃ n) hvu, map_add, map_smul, map_smul, key g n hg (hB₁ n) hvg,
      key g' n hg' (hB₂ n) hvg', hprod,
      hb.add _ _ (hm₁.const_smul α) (hsm α (hB₁ n)) (hm₂.const_smul α') (hsm α' (hB₂ n)),
      hb.smul α _ hm₁ (hB₁ n), hb.smul α' _ hm₂ (hB₂ n)]
    rfl
  have hone : E.integralOp (fun _ => (1 : ℂ)) = 1 := by
    have h := hb.indicator ⟨univ, MeasurableSet.univ⟩
    simp only [indicator_univ] at h
    exact h.trans E.map_univ
  have hlim : ∀ w, Tendsto (fun n => E.integralOp (b n) w) atTop (𝓝 w) := fun w => by
    have h := (hs b (fun _ => 1) 1 ⟨univ, MeasurableSet.univ⟩ hbm measurable_const hbb
      (isCarriedBy_univ hb) (fun y _ => by
        obtain ⟨N, hN⟩ := exists_nat_ge (max ‖g y‖ ‖g' y‖)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop N] with n hn
        have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
        have hy : y ∈ W n := ⟨((le_max_left _ _).trans hN).trans hNn,
          ((le_max_right _ _).trans hN).trans hNn⟩
        simp [b, indicator_of_mem hy])).2 w
    rw [E.integralApply_eq_integralOp (c := 1) (by simp), hone] at h
    exact h
  exact tendsto_nhds_unique (hlim _) ((hlim _).congr hub)
theorem unboundedCalculusLaws (hE : ∀ S, E S = F ⟨e ⁻¹' S.1, e.measurable S.2⟩)
    (hb : BoundedFunctionalCalculus E) (hs : StrongConvergence E)
    (hu : UnboundedFunctionalCalculus E) : UnboundedCalculusLaws F := by
  have hdom := integralDom_transport hE
  have hval := integralApply_transport hE
  have hiff : ∀ (φ : Y → ℂ) (A : H →ₗ.[ℂ] H), F.IsCalculusOperator φ A ↔
      HasDomainAndAction A (E.integralDom (φ ∘ e.symm)) (E.integralApply (φ ∘ e.symm)) := by
    intro φ A
    have hv : E.integralApply (φ ∘ e.symm) = F.calculusLimit φ := funext (hval φ)
    rw [HasDomainAndAction, hdom, hv]
    rfl
  have hop : ∀ φ : Y → ℂ, Measurable φ →
      F.IsCalculusOperator φ (F.calculusOperator φ) := fun φ hφ => by
    obtain ⟨A, -, hA⟩ := hu.exists_op _ (measurable_comp_symm (e := e) hφ)
    exact Classical.epsilon_spec ⟨A, (hiff φ A).mpr hA⟩
  refine
    { dense := fun φ hφ => ?_
      isCalculusOperator := hop
      tendsto := fun φ hφ v hv => ?_
      norm_sq := fun φ hφ v hv => ?_
      inner_eq := fun φ hφ v hv => ?_
      of_bounded := fun φ hφ => ?_
      mem_calculusDomain_add := fun φ φ' hφ hφ' α α' v hv =>
        mem_calculusDomain_linComb F hφ hφ' α α' hv
      calculusLimit_add := fun φ φ' hφ hφ' α α' v hv =>
        calculusLimit_linComb hE hb hs hu hφ hφ' α α' hv
      isSelfAdjoint := fun φ hφ => ?_
      pushforward := fun Z _ _ _ hZ f hf φ' hφ' => calculusOperator_pushforward F hZ f hf φ' hφ' }
  · obtain ⟨A, hd, hA⟩ := hu.exists_op _ (measurable_comp_symm (e := e) hφ)
    rw [hA.1, hdom] at hd
    exact hd
  · have h := hu.tendsto_truncate _ (measurable_comp_symm (e := e) hφ) v (by rwa [hdom])
    simpa only [truncate_transport, integralOp_transport hE, hval] using h
  · have h := hu.norm_sq _ (measurable_comp_symm (e := e) hφ) v (by rwa [hdom])
    rw [hval] at h
    rw [h]
    exact integral_transport hE (fun y => ‖φ y‖ ^ 2) v
  · have h := hu.inner_eq _ (measurable_comp_symm (e := e) hφ) v (by rwa [hdom])
    rwa [hval, integral_transport hE] at h
  · obtain ⟨hm, c, hc⟩ := hφ
    have hI := hop φ hm
    have hU : F.calculusDomain φ = univ := by
      rw [← hdom]
      exact E.integralDom_eq_univ fun y => hc _
    have hdt : (F.calculusOperator φ).domain = ⊤ := by
      refine SetLike.coe_injective ?_
      rw [hI.1, hU]
      rfl
    refine ⟨hdt, fun v => ?_⟩
    rw [hI.2 v, ← hval, E.integralApply_eq_integralOp (g := φ ∘ e.symm) fun y => hc _,
      integralOp_transport hE]
  · have hm : Measurable fun y => (φ y : ℂ) := Complex.measurable_ofReal.comp hφ
    have hI := hop _ hm
    have hA := hu.isSelfAdjoint _ (measurable_comp_symm (e := e) hm)
      (fun y => Complex.ofReal_im _) _ ((hiff _ _).mp hI)
    exact ⟨hA.1, hA.2.2, fun χ χ' h => (hA.2.1 χ).mpr ⟨χ', h⟩⟩
end Transport
theorem functionalCalculusHolds_of_borel
    (h : YangMills.Construction.BorelCalculus.BorelCalculusTheorem) : FunctionalCalculusHolds := by
  intro Y H _ _ _ _ _ _ F
  obtain ⟨m, Y₀, hm, hY₀, ⟨e⟩⟩ := exists_measurableEquiv_euclidean F
  have hE : ∀ S, transport F hm hY₀ e S = F ⟨e ⁻¹' S.1, e.measurable S.2⟩ := fun _ => rfl
  obtain ⟨hb, hs, -, hu, hk, -, -⟩ := (h H m).1 Y₀ (transport F hm hY₀ e)
  exact ⟨valuesAndDiagMeasures F, boundedCalculusLaws hE hb, dominatedStrongConvergence hE hb hs,
    realBoundedCalculus hE hb hk, pushforwardDiagMeasures F, unboundedCalculusLaws hE hb hs hu,
    supportLaws F⟩
end YangMills.Construction.EuclideanSpectral.FunctionalCalculus
