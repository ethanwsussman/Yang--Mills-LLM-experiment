import YangMills.Construction.ReflectionPositivity.ContractionOfTheLimitOfALatticeApproximationProof
import YangMills.Construction.HilbertSpace.BasicFacts
import YangMills.Construction.ReflectionPositivity.FromFivePointInequalitiesAtSmallTimesToTheConeProof
import YangMills.Construction.ReflectionPositivity.PropertiesOfTheFormOfAFunctionalProof
import YangMills.Construction.SpectralTheory.BorelFunctionalCalculusTheorem
import YangMills.Construction.SpectralTheory.FromFivePointsToTheCone
import YangMills.Construction.SpectralTheory.JointMeasureOfASemigroupAndARepresentation
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ComplexConjugate ComplexOrder InnerProductSpace Matrix NNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.Reconstruction
open YangMills.Construction.SeparatedTuples YangMills.Construction.ReflectionPositivity.TupleForm YangMills.Construction.HilbertSpaceBasics
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.BorelSpectral YangMills.Construction.SpectralTheorem YangMills.Construction.SelfAdjointFunctions
open YangMills.Construction.ReflectionPositivity.FormProperties (shiftedSpan unitSpan)
theorem timeComponent_smul_timeBasisVec (t : ℝ) :
    TimeAxis.timeComponent (t • timeBasisVec) = t := by apply _root_.YangMills.Construction.ReflectionPositivity.LimitContraction.timeComponent_smul_basisVector <;> assumption
theorem timeComponent_embedSpatial (a : Fin 3 → ℝ) : TimeAxis.timeComponent (embedSpatial a) = 0 := by
  simp [TimeAxis.timeComponent, TimeAxis.timeIdx, embedSpatial]
theorem timeComponent_add (a b : AmbientSpace) :
    TimeAxis.timeComponent (a + b) = TimeAxis.timeComponent a + TimeAxis.timeComponent b := rfl
theorem embedSpatial_add (a b : Fin 3 → ℝ) :
    embedSpatial (a + b) = embedSpatial a + embedSpatial b := by
  funext i
  fin_cases i <;> simp [embedSpatial]
theorem embedSpatial_zero : embedSpatial 0 = 0 := by apply _root_.YangMills.Construction.ReflectionPositivity.SmallTimeCone.embedSpatial_zero <;> assumption
theorem embedSpatial_smul (s : ℝ) (a : Fin 3 → ℝ) :
    embedSpatial (s • a) = s • embedSpatial a := by apply _root_.YangMills.Construction.ReflectionPositivity.SmallTimeCone.embedSpatial_smul <;> assumption
theorem continuous_embedSpatial : Continuous embedSpatial := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact continuous_apply 0
  · exact continuous_apply 1
  · exact continuous_apply 2
  · exact continuous_const
section Shifts
variable (hAct : SeparatedTuples.BasicFacts.PushSpanProperties)
include hAct
theorem pushSpan_translate_mem {v : AmbientSpace} (hv : 0 ≤ TimeAxis.timeComponent v)
    (F : PositiveSpan) :
    pushSpan (translate v) F.1 ∈ spanIn TimeAxis.upperHalfSpace := by
  have hτ := isEuclidIsometry_translate v
  have hopen : IsOpen TimeAxis.upperHalfSpace :=
    isOpen_lt continuous_const (continuous_apply TimeAxis.timeIdx)
  have hmap := ((hAct _ _ hτ hτ 0 0 0).2.2.2.2.1 _ hopen).2
  have h₁ : pushSpan (translate v) F.1 ∈
      spanIn (translate v '' TimeAxis.upperHalfSpace) := by
    rw [← hmap]
    exact Submodule.mem_map_of_mem F.2
  have himage : SeparatedTuples.translate v '' TimeAxis.upperHalfSpace ⊆ TimeAxis.upperHalfSpace := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : 0 < TimeAxis.timeComponent x := hx
    show 0 < TimeAxis.timeComponent (x + v)
    rw [timeComponent_add]
    linarith
  refine (Submodule.span_mono ?_) h₁
  rintro _ ⟨X, rfl⟩
  exact ⟨⟨X.1, fun f hf => (X.2 f hf).trans himage⟩, rfl⟩
theorem shiftedSpan_val {v : AmbientSpace} (hv : 0 ≤ TimeAxis.timeComponent v) (F : PositiveSpan) :
    (shiftedSpan v F).1 = pushSpan (translate v) F.1 := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.coe_shiftedSpan <;> assumption
theorem shiftedSpan_zero (F : PositiveSpan) : shiftedSpan 0 F = F := by
  have hτ := isEuclidIsometry_translate 0
  refine Subtype.ext ?_
  rw [shiftedSpan_val hAct (by simp [TimeAxis.timeComponent])]
  exact (hAct _ _ hτ hτ 0 0 F.1).2.2.1
theorem shiftedSpan_shiftedSpan {a b : AmbientSpace} (ha : 0 ≤ TimeAxis.timeComponent a)
    (hb : 0 ≤ TimeAxis.timeComponent b) (F : PositiveSpan) :
    shiftedSpan a (shiftedSpan b F) = shiftedSpan (a + b) F := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.shiftedSpan_shiftedSpan <;> assumption
theorem shiftedSpan_nil {v : AmbientSpace} (hv : 0 ≤ TimeAxis.timeComponent v) :
    shiftedSpan v (posTupleVec ⟨SepTuple.nil, nil_mem_supportedIn _⟩) =
      posTupleVec ⟨SepTuple.nil, nil_mem_supportedIn _⟩ := by
  refine Subtype.ext ?_
  rw [shiftedSpan_val hAct hv]
  show pushSpan (translate v) (basisVec SepTuple.nil) = basisVec SepTuple.nil
  unfold pushSpan
  rw [linearExtend_basisVec, push_nil]
theorem reflectedCorrelation_eq {w : AmbientSpace} (hw : 0 ≤ TimeAxis.timeComponent w)
    (σ : TupleFunctional) (F : PositiveSpan) :
    reflectedCorrelation σ F w = reflectionForm σ F (shiftedSpan w F) := by
  unfold reflectedCorrelation reflectionForm
  rw [shiftedSpan_val hAct hw]
theorem spanClass_pushSpan (σ : TupleFunctional) (h : IsPosSemidef (reflectionForm σ))
    {v : AmbientSpace} (hv : 0 ≤ TimeAxis.timeComponent v) (F : PositiveSpan) :
    spanClass σ h (pushSpan (translate v) F.1) = posClass σ h (shiftedSpan v F) := by
  unfold spanClass
  rw [dif_pos (pushSpan_translate_mem hAct hv F)]
  congr 1
  exact Subtype.ext (shiftedSpan_val hAct hv F).symm
omit hAct in
def shiftLinearMap (hAct : SeparatedTuples.BasicFacts.PushSpanProperties) (v : AmbientSpace)
    (hv : 0 ≤ TimeAxis.timeComponent v) : PositiveSpan →ₗ[ℂ] PositiveSpan :=
  (pushSpan (translate v)).restrict fun F hF => pushSpan_translate_mem hAct hv ⟨F, hF⟩
theorem shiftLinearMap_apply {v : AmbientSpace} (hv : 0 ≤ TimeAxis.timeComponent v)
    (F : PositiveSpan) : shiftLinearMap hAct v hv F = shiftedSpan v F :=
  Subtype.ext (shiftedSpan_val hAct hv F).symm
end Shifts
structure ReconstructionInputs (σ : TupleFunctional) (D₀ : Set ℝ)
    (h : IsPosSemidef (reflectionForm σ)) : Prop where
  completion : HilbertSpaceFacts.CompletionProperties
  extension : HilbertSpaceFacts.CompletionOperatorExtension
  identities : HilbertSpaceFacts.DenseSubsetIdentities
  strongConv : HilbertSpaceFacts.DenseSubsetStrongConvergence
  push : SeparatedTuples.BasicFacts.PushSpanProperties
  formProps : FormProperties.Assertion
  hyp : ContractionHypotheses σ D₀
variable {σ : TupleFunctional} {D₀ : Set ℝ} {h : IsPosSemidef (reflectionForm σ)}
theorem inner_posClass (S : ReconstructionInputs σ D₀ h) (F F' : PositiveSpan) :
    ⟪posClass σ h F, posClass σ h F'⟫_ℂ = reflectionForm σ F F' :=
  (S.completion _ (reflectionForm σ) h).2.1 F F'
theorem dense_range_posClass (S : ReconstructionInputs σ D₀ h) :
    Dense (Set.range (posClass σ h)) := by
  have hd := (S.completion _ (reflectionForm σ) h).2.2.2.1
  rwa [LinearMap.coe_range] at hd
theorem clm_ext_posClass (S : ReconstructionInputs σ D₀ h)
    {A B : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h}
    (hAB : ∀ F, A (posClass σ h F) = B (posClass σ h F)) : A = B := by
  refine (S.identities _ _ (dense_range_posClass S)).2.1 A B ?_
  rintro _ ⟨F, rfl⟩
  exact hAB F
theorem norm_sub_posClass_sq (S : ReconstructionInputs σ D₀ h) (G F : PositiveSpan) :
    ‖posClass σ h G - posClass σ h F‖ ^ 2 =
      (reflectionForm σ G G).re - 2 * (reflectionForm σ F G).re + (reflectionForm σ F F).re := by
  have hherm := h.isHermitianForm F G
  have h₁ := @norm_sub_sq ℂ _ _ _ _ (posClass σ h G) (posClass σ h F)
  have h₂ := @norm_sq_eq_re_inner ℂ _ _ _ _ (posClass σ h G)
  have h₃ := @norm_sq_eq_re_inner ℂ _ _ _ _ (posClass σ h F)
  rw [inner_posClass S] at h₂ h₃
  rw [h₁, h₂, h₃, inner_posClass S, hherm]
  simp
theorem tendsto_of_norm_sub_sq_tendsto_zero {ι E : Type*} [NormedAddCommGroup E] {l : Filter ι}
    {x : ι → E} {y : E} (hx : Tendsto (fun i => ‖x i - y‖ ^ 2) l (𝓝 0)) :
    Tendsto x l (𝓝 y) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have := hx.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this
theorem formSeminorm_le_of_re_le {F G : PositiveSpan}
    (hle : (reflectionForm σ G G).re ≤ (reflectionForm σ F F).re) :
    formSeminorm (reflectionForm σ) G ≤ formSeminorm (reflectionForm σ) F :=
  Real.sqrt_le_sqrt hle
theorem continuousOn_form_shifted (S : ReconstructionInputs σ D₀ h) (F : PositiveSpan) :
    ContinuousOn (fun v : AmbientSpace => reflectionForm σ F (shiftedSpan v F))
      {v | 0 ≤ TimeAxis.timeComponent v} :=
  (S.formProps σ F F).2.2.2.2 S.hyp.continuous
theorem reflectionForm_timeShift_symm (S : ReconstructionInputs σ D₀ h) {t : ℝ} (ht : 0 ≤ t)
    (F F' : PositiveSpan) :
    reflectionForm σ F (shiftedSpan (t • timeBasisVec) F') =
      reflectionForm σ (shiftedSpan (t • timeBasisVec) F) F' :=
  (((S.formProps σ F F').2.2.1 S.hyp.translateInvariant).1 t ht).1
theorem reflectionForm_timeShift_self (S : ReconstructionInputs σ D₀ h) {t : ℝ} (ht : 0 ≤ t)
    (F : PositiveSpan) :
    reflectionForm σ (shiftedSpan (t • timeBasisVec) F) (shiftedSpan (t • timeBasisVec) F) =
      reflectionForm σ F (shiftedSpan ((2 * t) • timeBasisVec) F) := by
  have h₁ := (((S.formProps σ F F).2.2.1 S.hyp.translateInvariant).1 t ht).2
  have h₂ : 0 ≤ TimeAxis.timeComponent ((2 * t) • timeBasisVec) := by
    rw [timeComponent_smul_timeBasisVec]
    linarith
  rw [← reflectedCorrelation_eq S.push h₂]
  exact h₁.symm
theorem reflectionForm_spatialShift (S : ReconstructionInputs σ D₀ h) (a : Fin 3 → ℝ)
    (F F' : PositiveSpan) :
    reflectionForm σ (shiftedSpan (embedSpatial a) F) (shiftedSpan (embedSpatial a) F') =
      reflectionForm σ F F' :=
  ((S.formProps σ F F').2.2.1 S.hyp.translateInvariant).2 _ (timeComponent_embedSpatial a)
theorem closure_timeSet (S : ReconstructionInputs σ D₀ h) : closure D₀ = Ici 0 := by
  have hc := S.hyp
  refine subset_antisymm ?_ ?_
  · have := closure_mono hc.subset_pos
    rwa [closure_Ioi] at this
  · rw [← closure_Ioi]
    exact closure_minimal hc.dense isClosed_closure
theorem re_form_double_le (S : ReconstructionInputs σ D₀ h) (F : PositiveSpan) {t : ℝ} (ht : 0 ≤ t) :
    (reflectionForm σ F (shiftedSpan ((2 * t) • timeBasisVec) F)).re ≤ (reflectionForm σ F F).re := by
  have hc := S.hyp
  have hmaps : ∀ x ∈ closure D₀, ((2 * x) • timeBasisVec) ∈ {v | 0 ≤ TimeAxis.timeComponent v} := by
    intro x hx
    rw [closure_timeSet S] at hx
    have hx' : (0 : ℝ) ≤ x := hx
    show 0 ≤ TimeAxis.timeComponent ((2 * x) • timeBasisVec)
    rw [timeComponent_smul_timeBasisVec]
    linarith
  have hcont : ContinuousOn
      (fun x : ℝ => (reflectionForm σ F (shiftedSpan ((2 * x) • timeBasisVec) F)).re) (closure D₀) :=
    Complex.continuous_re.comp_continuousOn
      ((continuousOn_form_shifted S F).comp (Continuous.continuousOn (by fun_prop)) hmaps)
  refine le_on_closure
    (f := fun x : ℝ => (reflectionForm σ F (shiftedSpan ((2 * x) • timeBasisVec) F)).re)
    (g := fun _ => (reflectionForm σ F F).re) ?_ hcont continuousOn_const
    (by rw [closure_timeSet S]; exact ht)
  intro x hx
  have hx₀ : (0 : ℝ) < x := hc.subset_pos hx
  have h₂ : 0 ≤ TimeAxis.timeComponent ((2 * x) • timeBasisVec) := by
    rw [timeComponent_smul_timeBasisVec]
    linarith
  have hle := hc.contraction F x hx
  rw [reflectedCorrelation_eq S.push h₂] at hle
  exact (Complex.le_def.mp hle).1
theorem exists_contraction_extension (S : ReconstructionInputs σ D₀ h) {v : AmbientSpace}
    (hv : 0 ≤ TimeAxis.timeComponent v)
    (hb : ∀ F, formSeminorm (reflectionForm σ) (shiftedSpan v F) ≤ formSeminorm (reflectionForm σ) F) :
    ∃ A : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h,
      (∀ F, A (posClass σ h F) = posClass σ h (shiftedSpan v F)) ∧ ‖A‖ ≤ 1 := by
  obtain ⟨-, A, hA, hn, -⟩ := S.extension _ (reflectionForm σ) h 1 (shiftLinearMap S.push v hv)
    zero_le_one (fun F => by
      rw [shiftLinearMap_apply S.push hv, one_mul]
      exact hb F)
  refine ⟨A, fun F => ?_, hn⟩
  rw [← shiftLinearMap_apply S.push hv]
  exact hA F
theorem timeComponent_timeVec_nonneg (t : ℝ≥0) :
    0 ≤ TimeAxis.timeComponent ((t : ℝ) • timeBasisVec) := by
  rw [timeComponent_smul_timeBasisVec]
  exact t.2
theorem exists_timeShiftFamily (S : ReconstructionInputs σ D₀ h) :
    ∃ T, IsTimeShiftFamily σ h T ∧ ∀ t, ‖T t‖ ≤ 1 := by
  have hex : ∀ t : ℝ≥0, ∃ A : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h,
      (∀ F, A (posClass σ h F) = posClass σ h (shiftedSpan ((t : ℝ) • timeBasisVec) F)) ∧
        ‖A‖ ≤ 1 := fun t =>
    exists_contraction_extension S (timeComponent_timeVec_nonneg t) fun F =>
      formSeminorm_le_of_re_le (by
        rw [reflectionForm_timeShift_self S t.coe_nonneg]
        exact re_form_double_le S F t.coe_nonneg)
  choose T hT hn using hex
  refine ⟨T, fun t F => ?_, hn⟩
  rw [spanClass_pushSpan S.push σ h (timeComponent_timeVec_nonneg t)]
  exact hT t F
theorem isTimeShiftFamily_timeShift (S : ReconstructionInputs σ D₀ h) :
    IsTimeShiftFamily σ h (timeShift σ h) := by
  obtain ⟨T, hT, -⟩ := exists_timeShiftFamily S
  exact Classical.epsilon_spec (p := IsTimeShiftFamily σ h) ⟨T, hT⟩
theorem timeShift_posClass (S : ReconstructionInputs σ D₀ h) (t : ℝ≥0) (F : PositiveSpan) :
    timeShift σ h t (posClass σ h F) = posClass σ h (shiftedSpan ((t : ℝ) • timeBasisVec) F) := by
  rw [isTimeShiftFamily_timeShift S t F,
    spanClass_pushSpan S.push σ h (timeComponent_timeVec_nonneg t)]
theorem timeShift_unique (S : ReconstructionInputs σ D₀ h)
    {T : ℝ≥0 → PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h}
    (hT : IsTimeShiftFamily σ h T) : T = timeShift σ h := by
  funext t
  refine clm_ext_posClass S fun F => ?_
  rw [hT t F, isTimeShiftFamily_timeShift S t F]
theorem norm_timeShift_le (S : ReconstructionInputs σ D₀ h) (t : ℝ≥0) : ‖timeShift σ h t‖ ≤ 1 := by
  obtain ⟨T, hT, hn⟩ := exists_timeShiftFamily S
  rw [← timeShift_unique S hT]
  exact hn t
theorem isOpSemigroup_timeShift (S : ReconstructionInputs σ D₀ h) : IsOpSemigroup (timeShift σ h) := by
  refine ⟨clm_ext_posClass S fun F => ?_, fun t t' => clm_ext_posClass S fun F => ?_⟩
  · rw [timeShift_posClass S]
    simp [shiftedSpan_zero S.push]
  · show timeShift σ h t (timeShift σ h t' (posClass σ h F)) = _
    rw [timeShift_posClass S, timeShift_posClass S, timeShift_posClass S,
      shiftedSpan_shiftedSpan S.push (timeComponent_timeVec_nonneg t)
        (timeComponent_timeVec_nonneg t'), NNReal.coe_add, add_smul]
theorem isSelfAdjoint_timeShift (S : ReconstructionInputs σ D₀ h) (t : ℝ≥0) :
    IsSelfAdjoint (timeShift σ h t) := by
  refine (S.identities _ _ (dense_range_posClass S)).2.2.2.1 _ ?_
  rintro _ ⟨F, rfl⟩ _ ⟨F', rfl⟩
  rw [timeShift_posClass S, timeShift_posClass S, inner_posClass S, inner_posClass S]
  exact reflectionForm_timeShift_symm S t.2 F F'
theorem tendsto_timeShift_zero (S : ReconstructionInputs σ D₀ h) (ψ : PhysicalSpace σ h) :
    Tendsto (fun t => timeShift σ h t ψ) (𝓝[>] 0) (𝓝 ψ) := by
  have hs : TendstoStrongly (timeShift σ h) (𝓝[>] 0) 1 := by
    refine S.strongConv _ _ _ _ _ _ (dense_range_posClass S)
      ⟨1, by rintro _ ⟨t, rfl⟩; exact norm_timeShift_le S t⟩ ?_
    rintro _ ⟨F, rfl⟩
    refine tendsto_of_norm_sub_sq_tendsto_zero ?_
    have hcon := continuousOn_form_shifted S F
    have h₁ : Continuous fun t : ℝ≥0 =>
        reflectionForm σ F (shiftedSpan ((t : ℝ) • timeBasisVec) F) :=
      hcon.comp_continuous (by fun_prop) fun t => timeComponent_timeVec_nonneg t
    have h₂ : Continuous fun t : ℝ≥0 =>
        reflectionForm σ F (shiftedSpan ((2 * (t : ℝ)) • timeBasisVec) F) := by
      refine hcon.comp_continuous (by fun_prop) fun t => ?_
      show 0 ≤ TimeAxis.timeComponent ((2 * (t : ℝ)) • timeBasisVec)
      rw [timeComponent_smul_timeBasisVec]
      have := t.2
      linarith
    have hG : Continuous fun t : ℝ≥0 =>
        (reflectionForm σ F (shiftedSpan ((2 * (t : ℝ)) • timeBasisVec) F)).re -
          2 * (reflectionForm σ F (shiftedSpan ((t : ℝ) • timeBasisVec) F)).re +
            (reflectionForm σ F F).re :=
      ((Complex.continuous_re.comp h₂).sub
        (continuous_const.mul (Complex.continuous_re.comp h₁))).add continuous_const
    have h₀ := (hG.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    have hz : (reflectionForm σ F (shiftedSpan ((2 * ((0 : ℝ≥0) : ℝ)) • timeBasisVec) F)).re -
        2 * (reflectionForm σ F (shiftedSpan (((0 : ℝ≥0) : ℝ) • timeBasisVec) F)).re +
          (reflectionForm σ F F).re = 0 := by
      simp only [NNReal.coe_zero, mul_zero, zero_smul, shiftedSpan_zero S.push]
      ring
    rw [hz] at h₀
    refine h₀.congr fun t => ?_
    show _ = ‖timeShift σ h t (posClass σ h F) - posClass σ h F‖ ^ 2
    rw [timeShift_posClass S, norm_sub_posClass_sq S, reflectionForm_timeShift_self S t.coe_nonneg]
  exact hs ψ
theorem timeShift_contractionSemigroup (S : ReconstructionInputs σ D₀ h) :
    ContractionSemigroups.IsSelfAdjointContractionSemigroup (timeShift σ h) where
  semigroup := isOpSemigroup_timeShift S
  selfAdjoint := isSelfAdjoint_timeShift S
  contraction := norm_timeShift_le S
  tendsto_zero := tendsto_timeShift_zero S
theorem timeShift_vacuum (S : ReconstructionInputs σ D₀ h) (t : ℝ≥0) :
    timeShift σ h t (vacuum σ h) = vacuum σ h := by
  unfold vacuum
  rw [timeShift_posClass S, shiftedSpan_nil S.push (timeComponent_timeVec_nonneg t)]
theorem exists_apply_eq_zero_of_mem_opKernel {ℋ : Type*} [NormedAddCommGroup ℋ]
    [InnerProductSpace ℂ ℋ] {A : UnboundedOp ℋ} {ψ : ℋ} (hψ : ψ ∈ opKernel A) :
    ∃ hd : ψ ∈ A.domain, A ⟨ψ, hd⟩ = 0 := by
  obtain ⟨x, hx, rfl⟩ := hψ
  exact ⟨x.2, hx⟩
theorem timeComponent_embedSpatial_nonneg (a : Fin 3 → ℝ) :
    0 ≤ TimeAxis.timeComponent (embedSpatial a) :=
  (timeComponent_embedSpatial a).ge
theorem exists_spaceShiftFamily (S : ReconstructionInputs σ D₀ h) :
    ∃ U, IsSpaceShiftFamily σ h U := by
  have hex : ∀ a : Fin 3 → ℝ, ∃ A : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h,
      (∀ F, A (posClass σ h F) = posClass σ h (shiftedSpan (embedSpatial a) F)) ∧
        ‖A‖ ≤ 1 := fun a =>
    exists_contraction_extension S (timeComponent_embedSpatial_nonneg a) fun F =>
      formSeminorm_le_of_re_le (by rw [reflectionForm_spatialShift S])
  choose U hU _ using hex
  refine ⟨U, fun a F => ?_⟩
  rw [spanClass_pushSpan S.push σ h (timeComponent_embedSpatial_nonneg a)]
  exact hU a F
theorem isSpaceShiftFamily_spaceShift (S : ReconstructionInputs σ D₀ h) :
    IsSpaceShiftFamily σ h (spaceShift σ h) :=
  Classical.epsilon_spec (p := IsSpaceShiftFamily σ h) (exists_spaceShiftFamily S)
theorem spaceShift_posClass (S : ReconstructionInputs σ D₀ h) (a : Fin 3 → ℝ) (F : PositiveSpan) :
    spaceShift σ h a (posClass σ h F) = posClass σ h (shiftedSpan (embedSpatial a) F) := by
  rw [isSpaceShiftFamily_spaceShift S a F,
    spanClass_pushSpan S.push σ h (timeComponent_embedSpatial_nonneg a)]
theorem spaceShift_unique (S : ReconstructionInputs σ D₀ h)
    {U : (Fin 3 → ℝ) → PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h}
    (hU : IsSpaceShiftFamily σ h U) : U = spaceShift σ h := by
  funext a
  refine clm_ext_posClass S fun F => ?_
  rw [hU a F, isSpaceShiftFamily_spaceShift S a F]
theorem inner_spaceShift (S : ReconstructionInputs σ D₀ h) (a : Fin 3 → ℝ)
    (φ ψ : PhysicalSpace σ h) :
    ⟪spaceShift σ h a φ, spaceShift σ h a ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ := by
  have hall := (S.identities _ _ (dense_range_posClass S)).1 (spaceShift σ h a)
    (spaceShift σ h a) 1 1 (by
      rintro _ ⟨F, rfl⟩ _ ⟨F', rfl⟩
      rw [spaceShift_posClass S, spaceShift_posClass S, inner_posClass S,
        reflectionForm_spatialShift S]
      exact (inner_posClass S F F').symm) φ ψ
  exact hall
theorem spaceShift_zero (S : ReconstructionInputs σ D₀ h) : spaceShift σ h 0 = 1 := by
  refine clm_ext_posClass S fun F => ?_
  rw [spaceShift_posClass S, embedSpatial_zero, shiftedSpan_zero S.push]
  rfl
theorem spaceShift_mul (S : ReconstructionInputs σ D₀ h) (a a' : Fin 3 → ℝ) :
    spaceShift σ h a * spaceShift σ h a' = spaceShift σ h (a + a') := by
  refine clm_ext_posClass S fun F => ?_
  show spaceShift σ h a (spaceShift σ h a' (posClass σ h F)) = _
  rw [spaceShift_posClass S, spaceShift_posClass S, spaceShift_posClass S,
    shiftedSpan_shiftedSpan S.push (timeComponent_embedSpatial_nonneg a)
      (timeComponent_embedSpatial_nonneg a'), embedSpatial_add]
theorem isUnitaryOp_spaceShift (S : ReconstructionInputs σ D₀ h) (a : Fin 3 → ℝ) :
    IsUnitaryOp (spaceShift σ h a) := by
  have hs : star (spaceShift σ h a) * spaceShift σ h a = 1 := by
    refine ContinuousLinearMap.ext fun ψ => ext_inner_left ℂ fun φ => ?_
    show ⟪φ, star (spaceShift σ h a) (spaceShift σ h a ψ)⟫_ℂ = ⟪φ, ψ⟫_ℂ
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
      inner_spaceShift S]
  have hinv : spaceShift σ h a * spaceShift σ h (-a) = 1 := by
    rw [spaceShift_mul S, add_neg_cancel, spaceShift_zero S]
  have hst : star (spaceShift σ h a) = spaceShift σ h (-a) := by
    calc star (spaceShift σ h a)
        = star (spaceShift σ h a) * (spaceShift σ h a * spaceShift σ h (-a)) := by
          rw [hinv, mul_one]
      _ = spaceShift σ h (-a) := by rw [← mul_assoc, hs, one_mul]
  exact ⟨hs, by rw [hst]; exact hinv⟩
theorem norm_spaceShift_le (S : ReconstructionInputs σ D₀ h) (a : Fin 3 → ℝ) :
    ‖spaceShift σ h a‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ψ => ?_
  have h₁ : ‖spaceShift σ h a ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ _ _ _ _ ψ, inner_spaceShift S]
  rw [one_mul]
  exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h₁).le
theorem spaceShift_tendstoStrongly (S : ReconstructionInputs σ D₀ h) :
    TendstoStrongly (spaceShift σ h) (𝓝 0) 1 := by
  refine S.strongConv _ _ _ _ _ _ (dense_range_posClass S)
    ⟨1, by rintro _ ⟨a, rfl⟩; exact norm_spaceShift_le S a⟩ ?_
  rintro _ ⟨F, rfl⟩
  refine tendsto_of_norm_sub_sq_tendsto_zero ?_
  have h₁ : Continuous fun a : Fin 3 → ℝ => reflectionForm σ F (shiftedSpan (embedSpatial a) F) :=
    (continuousOn_form_shifted S F).comp_continuous continuous_embedSpatial
      fun a => timeComponent_embedSpatial_nonneg a
  have hG : Continuous fun a : Fin 3 → ℝ =>
      (reflectionForm σ F F).re - 2 * (reflectionForm σ F (shiftedSpan (embedSpatial a) F)).re +
        (reflectionForm σ F F).re :=
    (continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp h₁))).add
      continuous_const
  have h₀ := hG.tendsto 0
  have hz : (reflectionForm σ F F).re -
      2 * (reflectionForm σ F (shiftedSpan (embedSpatial 0) F)).re +
        (reflectionForm σ F F).re = 0 := by
    rw [embedSpatial_zero, shiftedSpan_zero S.push]
    ring
  rw [hz] at h₀
  refine h₀.congr fun a => ?_
  show _ = ‖spaceShift σ h a (posClass σ h F) - posClass σ h F‖ ^ 2
  rw [spaceShift_posClass S, norm_sub_posClass_sq S, reflectionForm_spatialShift S]
theorem spaceShift_comm_timeShift (S : ReconstructionInputs σ D₀ h) (a : Fin 3 → ℝ) (t : ℝ≥0) :
    spaceShift σ h a * timeShift σ h t = timeShift σ h t * spaceShift σ h a := by
  refine clm_ext_posClass S fun F => ?_
  show spaceShift σ h a (timeShift σ h t (posClass σ h F)) =
    timeShift σ h t (spaceShift σ h a (posClass σ h F))
  rw [timeShift_posClass S, spaceShift_posClass S, spaceShift_posClass S, timeShift_posClass S,
    shiftedSpan_shiftedSpan S.push (timeComponent_embedSpatial_nonneg a)
      (timeComponent_timeVec_nonneg t),
    shiftedSpan_shiftedSpan S.push (timeComponent_timeVec_nonneg t)
      (timeComponent_embedSpatial_nonneg a), add_comm]
theorem spaceShift_vacuum (S : ReconstructionInputs σ D₀ h) (a : Fin 3 → ℝ) :
    spaceShift σ h a (vacuum σ h) = vacuum σ h := by
  unfold vacuum
  rw [spaceShift_posClass S, shiftedSpan_nil S.push (timeComponent_embedSpatial_nonneg a)]
theorem matrixElementFormula_holds (S : ReconstructionInputs σ D₀ h) : MatrixElementFormula σ h := by
  intro F F' t a
  have hsum : 0 ≤ TimeAxis.timeComponent ((t : ℝ) • timeBasisVec + embedSpatial a) := by
    rw [timeComponent_add]
    have := timeComponent_timeVec_nonneg t
    have := timeComponent_embedSpatial_nonneg a
    linarith
  rw [spaceShift_posClass S, timeShift_posClass S,
    shiftedSpan_shiftedSpan S.push (timeComponent_timeVec_nonneg t)
      (timeComponent_embedSpatial_nonneg a), inner_posClass S]
  unfold reflectionForm
  rw [shiftedSpan_val S.push hsum]
theorem spanBasisIn_eq_posTupleVec (X : supportedIn TimeAxis.upperHalfSpace) :
    spanBasisIn TimeAxis.upperHalfSpace X = posTupleVec X := by
  unfold spanBasisIn
  exact Module.Basis.span_apply _ X
theorem vacuumProperties_hold (S : ReconstructionInputs σ D₀ h) : VacuumProperties σ h := by
  have hb := (S.formProps σ 0 0).2.1 S.hyp.reflectionPositive
  have hemp : unitSpan = posTupleVec ⟨SepTuple.nil, nil_mem_supportedIn _⟩ :=
    spanBasisIn_eq_posTupleVec _
  refine ⟨h.isHermitianForm, ?_, fun X => ?_⟩
  · have h₁ : ‖vacuum σ h‖ ^ 2 = 1 := by
      rw [@norm_sq_eq_re_inner ℂ]
      unfold vacuum
      rw [inner_posClass S, ← hemp, hb.2]
      simp
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h₁
  · obtain ⟨-, h₂, h₃⟩ := hb.1 X
    rw [spanBasisIn_eq_posTupleVec, hemp] at h₂ h₃
    unfold vacuum
    rw [inner_posClass S, inner_posClass S, h₂, h₃]
    refine ⟨rfl, ?_⟩
    have h₄ := congrArg conj h₃
    simpa using h₄
theorem semigroupProperties_hold (S : ReconstructionInputs σ D₀ h)
    (hSem : ContractionSemigroups.ContractionSemigroupTheorem) :
    SemigroupProperties σ h ∧ IsHamiltonianOp σ h (hamiltonian σ h) ∧
      hamiltonian σ h = ContractionSemigroups.semigroupGenerator (timeShift σ h) := by
  obtain ⟨⟨hsc, -, hker⟩, -, ⟨hu, hnn, hexp, -, -⟩, ⟨hkern, -⟩, -⟩ :=
    hSem _ _ (timeShift_contractionSemigroup S)
  have hspec : IsHamiltonianOp σ h
      (ContractionSemigroups.semigroupGenerator (timeShift σ h)) := ⟨hnn, hexp⟩
  have hham : IsHamiltonianOp σ h (hamiltonian σ h) :=
    Classical.epsilon_spec (p := IsHamiltonianOp σ h) ⟨_, hspec⟩
  have hH : hamiltonian σ h = ContractionSemigroups.semigroupGenerator (timeShift σ h) :=
    hu.unique hham hspec
  refine ⟨⟨⟨timeShift σ h, isTimeShiftFamily_timeShift S, fun T hT => timeShift_unique S hT⟩,
    isTimeShiftFamily_timeShift S, hsc, isOpSemigroup_timeShift S, fun t =>
      ⟨isSelfAdjoint_timeShift S t, norm_timeShift_le S t, fun ψ hψ => ?_⟩, hu, hham, ?_⟩,
    hham, hH⟩
  · have hm : ψ ∈ LinearMap.ker
        (timeShift σ h t : PhysicalSpace σ h →ₗ[ℂ] PhysicalSpace σ h) := hψ
    rw [hker t] at hm
    simpa using hm
  · have hm : vacuum σ h ∈ ((opKernel (ContractionSemigroups.semigroupGenerator
        (timeShift σ h)) : Submodule ℂ (PhysicalSpace σ h)) : Set (PhysicalSpace σ h)) := by
      rw [hkern]
      exact timeShift_vacuum S 1
    rw [hH]
    exact exists_apply_eq_zero_of_mem_opKernel hm
theorem isContinuousUnitaryGroup_axis (S : ReconstructionInputs σ D₀ h) (j : Fin 3) :
    UnitaryGroups.IsContinuousUnitaryGroup
      (fun s : ℝ => spaceShift σ h (s • spatialBasisVec j)) := by
  refine ⟨⟨fun s => isUnitaryOp_spaceShift S _, ?_, fun s s' => ?_⟩, fun ψ => ?_⟩
  · simp only [zero_smul]
    exact spaceShift_zero S
  · simp only [add_smul]
    exact spaceShift_mul S _ _
  · have hl : Tendsto (fun s : ℝ => s • spatialBasisVec j) (𝓝 0) (𝓝 0) := by
      have hc : Continuous fun s : ℝ => s • spatialBasisVec j := by fun_prop
      have := hc.tendsto 0
      simpa using this
    exact (spaceShift_tendstoStrongly S ψ).comp hl
theorem momentum_properties (S : ReconstructionInputs σ D₀ h)
    (hGrp : UnitaryGroups.StoneTheoremHolds) (j : Fin 3) :
    (∃! P, IsMomentumOp σ h j P) ∧ IsMomentumOp σ h j (momentum σ h j) ∧
      momentum σ h j = UnitaryGroups.stoneGenerator
        (fun s : ℝ => spaceShift σ h (s • spatialBasisVec j)) ∧
      ∃ hΩ : vacuum σ h ∈ (momentum σ h j).domain, momentum σ h j ⟨vacuum σ h, hΩ⟩ = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hu, hg, hk, -⟩ :=
    (hGrp _).1 _ (isContinuousUnitaryGroup_axis S j)
  have hmom : IsMomentumOp σ h j (momentum σ h j) :=
    Classical.epsilon_spec (p := IsMomentumOp σ h j) ⟨_, hg⟩
  have hP : momentum σ h j = UnitaryGroups.stoneGenerator
      (fun s : ℝ => spaceShift σ h (s • spatialBasisVec j)) := hu.unique hmom hg
  refine ⟨hu, hmom, hP, ?_⟩
  have hm : vacuum σ h ∈ ((opKernel (UnitaryGroups.stoneGenerator
      (fun s : ℝ => spaceShift σ h (s • spatialBasisVec j))) :
      Submodule ℂ (PhysicalSpace σ h)) : Set (PhysicalSpace σ h)) := by
    rw [hk]
    exact fun s => spaceShift_vacuum S _
  rw [hP]
  exact exists_apply_eq_zero_of_mem_opKernel hm
theorem spatialProperties_hold (S : ReconstructionInputs σ D₀ h)
    (hGrp : UnitaryGroups.StoneTheoremHolds)
    (hJoint : SemigroupRepresentation.JointSpectralTheoremForPair) : SpatialProperties σ h := by
  have hrep : IsUnitaryRep (spaceShift σ h) :=
    ⟨isUnitaryOp_spaceShift S, spaceShift_zero S, spaceShift_mul S⟩
  have hpair : SemigroupRepresentation.IsCommutingSemigroupRep (timeShift σ h) (spaceShift σ h) :=
    ⟨timeShift_contractionSemigroup S, hrep, spaceShift_tendstoStrongly S,
      spaceShift_comm_timeShift S⟩
  refine ⟨⟨spaceShift σ h, isSpaceShiftFamily_spaceShift S, fun U hU => spaceShift_unique S hU⟩,
    isSpaceShiftFamily_spaceShift S, ((hJoint _ 3 (by norm_num)).1 _ _ hpair).1, hrep,
    fun a t => spaceShift_comm_timeShift S a t, spaceShift_vacuum S,
    fun j => (momentum_properties S hGrp j).1, fun j => (momentum_properties S hGrp j).2.1,
    fun j => (momentum_properties S hGrp j).2.2.2, fun j j' s s' => ?_⟩
  have h₁ := (momentum_properties S hGrp j).2.1.2 s
  have h₂ := (momentum_properties S hGrp j').2.1.2 s'
  show expI (momentum σ h j) s * expI (momentum σ h j') s' =
    expI (momentum σ h j') s' * expI (momentum σ h j) s
  rw [← h₁, ← h₂, spaceShift_mul S, spaceShift_mul S, add_comm]
def axisRep (σ : TupleFunctional) (h : IsPosSemidef (reflectionForm σ)) (j : Fin 3)
    (a : Fin 1 → ℝ) : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h :=
  spaceShift σ h (a 0 • spatialBasisVec j)
theorem isCommutingSemigroupRep_axisRep (S : ReconstructionInputs σ D₀ h) (j : Fin 3) :
    SemigroupRepresentation.IsCommutingSemigroupRep (timeShift σ h) (axisRep σ h j) := by
  refine ⟨timeShift_contractionSemigroup S, ⟨fun a => isUnitaryOp_spaceShift S _, ?_, fun a a' => ?_⟩,
    fun ψ => ?_, fun a t => spaceShift_comm_timeShift S _ t⟩
  · simp only [axisRep, Pi.zero_apply, zero_smul]
    exact spaceShift_zero S
  · simp only [axisRep, Pi.add_apply, add_smul]
    exact spaceShift_mul S _ _
  · have hl : Tendsto (fun a : Fin 1 → ℝ => a 0 • spatialBasisVec j) (𝓝 0) (𝓝 0) := by
      have hc : Continuous fun a : Fin 1 → ℝ => a 0 • spatialBasisVec j := by fun_prop
      have := hc.tendsto 0
      simpa using this
    exact (spaceShift_tendstoStrongly S ψ).comp hl
theorem momentumOp_axisRep (S : ReconstructionInputs σ D₀ h)
    (hGrp : UnitaryGroups.StoneTheoremHolds) (j : Fin 3) :
    SemigroupRepresentation.momentumOp (axisRep σ h j) 0 = momentum σ h j := by
  have he : (fun s : ℝ => axisRep σ h j (s • Pi.single 0 1)) =
      fun s : ℝ => spaceShift σ h (s • spatialBasisVec j) := by
    funext s
    simp [axisRep]
  unfold SemigroupRepresentation.momentumOp
  rw [he]
  exact (momentum_properties S hGrp j).2.2.1.symm
theorem expNeg_hamiltonian (S : ReconstructionInputs σ D₀ h)
    (hSem : ContractionSemigroups.ContractionSemigroupTheorem) (t : ℝ≥0) :
    expNeg (hamiltonian σ h) t = timeShift σ h t :=
  ((semigroupProperties_hold S hSem).2.1.2 t).symm
theorem expI_momentum (S : ReconstructionInputs σ D₀ h)
    (hGrp : UnitaryGroups.StoneTheoremHolds) (j : Fin 3) (s : ℝ) :
    expI (momentum σ h j) s = spaceShift σ h (s • spatialBasisVec j) :=
  ((momentum_properties S hGrp j).2.1.2 s).symm
theorem isJointSpectralMeasure_iff (S : ReconstructionInputs σ D₀ h)
    (hSem : ContractionSemigroups.ContractionSemigroupTheorem)
    (hGrp : UnitaryGroups.StoneTheoremHolds) (j : Fin 3)
    (E : SpectralMeasure nonnegHalfPlane (PhysicalSpace σ h)) :
    IsJointSpectralMeasure σ h j E ↔
      SemigroupRepresentation.IsJointSpectralMeasure (n := 1) E (timeShift σ h)
        (axisRep σ h j) := by
  have hdot : ∀ (a : Fin 1 → ℝ) (y : Fin 2 → ℝ),
      a ⬝ᵥ SemigroupRepresentation.spatialCoords (n := 1) y = a 0 * y 1 := by
    intro a y
    simp [dotProduct, SemigroupRepresentation.spatialCoords]
  constructor
  · intro hE t a
    have h₁ := hE t (a 0)
    rw [expNeg_hamiltonian S hSem, expI_momentum S hGrp] at h₁
    refine h₁.trans (congrArg E.integralOp (funext fun y => ?_))
    rw [hdot]
  · intro hE t s
    rw [expNeg_hamiltonian S hSem, expI_momentum S hGrp]
    have h₁ := hE t (fun _ => s)
    refine Eq.trans h₁ (congrArg E.integralOp (funext fun y => ?_))
    rw [hdot]
theorem jointSpectralProperties_hold (S : ReconstructionInputs σ D₀ h)
    (hSem : ContractionSemigroups.ContractionSemigroupTheorem)
    (hGrp : UnitaryGroups.StoneTheoremHolds)
    (hJoint : SemigroupRepresentation.JointSpectralTheoremForPair) :
    JointSpectralProperties σ h := by
  intro j
  obtain ⟨-, hex, hJ, hIH, hIP, hM0, hM1, -⟩ :=
    (hJoint _ 1 le_rfl).1 _ _ (isCommutingSemigroupRep_axisRep S j)
  have hiff := isJointSpectralMeasure_iff S hSem hGrp j
  have hH := (semigroupProperties_hold S hSem).2.2
  have hP := momentumOp_axisRep S hGrp j
  have hspec : IsJointSpectralMeasure σ h j (SemigroupRepresentation.jointSpectralMeasure
      (timeShift σ h) (axisRep σ h j)) := (hiff _).2 hJ
  have hjm : IsJointSpectralMeasure σ h j (jointSpectralMeasure σ h j) := by
    unfold jointSpectralMeasure
    exact Classical.epsilon_spec ⟨_, hspec⟩
  have hEq : jointSpectralMeasure σ h j = SemigroupRepresentation.jointSpectralMeasure
      (timeShift σ h) (axisRep σ h j) := hex.unique ((hiff _).1 hjm) hJ
  refine ⟨?_, hjm, fun Δ => ?_, fun Δ => ?_, ?_, ?_⟩
  · obtain ⟨E₀, hE₀, hU₀⟩ := hex
    exact ⟨E₀, (hiff _).2 hE₀, fun E' hE' => hU₀ E' ((hiff _).1 hE')⟩
  · rw [hEq, hH, ← hM0]
    rfl
  · rw [hEq, ← hP, ← hM1 0]
    rfl
  · rw [hEq, hH]
    exact hIH
  · rw [hEq, ← hP]
    exact hIP 0
def energyCoord (y : nonnegHalfPlane) : ℝ := y.1 0
def momentumCoord (y : nonnegHalfPlane) : ℝ := y.1 1
theorem measurable_energyCoord : Measurable energyCoord :=
  (measurable_pi_apply 0).comp measurable_subtype_coe
theorem measurable_momentumCoord : Measurable momentumCoord :=
  (measurable_pi_apply 1).comp measurable_subtype_coe
theorem spectralIntegralOp_eq {n : ℕ} {Y : Set (Fin n → ℝ)} {ℋ : Type*} [NormedAddCommGroup ℋ]
    [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] {E : SpectralMeasure Y ℋ} {g : Y → ℂ}
    {A : UnboundedOp ℋ} (hA : IsSpectralIntegralOf A E g) : spectralIntegralOp E g = A := by
  have hs : IsSpectralIntegralOf (spectralIntegralOp E g) E g :=
    Classical.epsilon_spec (p := fun A => IsSpectralIntegralOf A E g) ⟨A, hA⟩
  refine LinearPMap.ext (SetLike.ext fun ψ => (hs.1 ψ).trans (hA.1 ψ).symm) ?_
  intro x hx hy
  rw [hs.2 ⟨x, hx⟩, hA.2 ⟨x, hy⟩]
section Cone
variable (S : ReconstructionInputs σ D₀ h) (hSem : ContractionSemigroups.ContractionSemigroupTheorem)
  (hGrp : UnitaryGroups.StoneTheoremHolds)
  (hJM : JointSpectralProperties σ h)
include S hSem hGrp hJM
theorem heatOp_eq (j : Fin 3) (t : ℝ≥0) :
    FivePointCone.heatOp (jointSpectralMeasure σ h j) energyCoord t = timeShift σ h t := by
  have h₁ := (hJM j).2.1 t 0
  rw [expNeg_hamiltonian S hSem, expI_momentum S hGrp, zero_smul,
    spaceShift_zero S, mul_one] at h₁
  rw [h₁]
  unfold FivePointCone.heatOp
  refine congrArg (jointSpectralMeasure σ h j).integralOp (funext fun y => ?_)
  simp [energyCoord]
theorem phaseOp_eq (j : Fin 3) (s : ℝ) :
    FivePointCone.phaseOp (jointSpectralMeasure σ h j) momentumCoord s =
      spaceShift σ h (s • spatialBasisVec j) := by
  have h₁ := (hJM j).2.1 0 s
  rw [expNeg_hamiltonian S hSem, expI_momentum S hGrp,
    (isOpSemigroup_timeShift S).1, one_mul] at h₁
  rw [h₁]
  unfold FivePointCone.phaseOp
  refine congrArg (jointSpectralMeasure σ h j).integralOp (funext fun y => ?_)
  simp [momentumCoord, mul_assoc]
theorem inner_fivePointOp_posClass (j : Fin 3) (F : PositiveSpan) {t : ℝ} (ht : 0 < t) :
    ⟪posClass σ h F, FivePointCone.fivePointOp (jointSpectralMeasure σ h j)
      energyCoord momentumCoord t (posClass σ h F)⟫_ℂ = fivePointCombination σ F t j := by
  obtain ⟨t', rfl⟩ : ∃ t' : ℝ≥0, (t' : ℝ) = t := ⟨⟨t, ht.le⟩, rfl⟩
  have c₁ := heatOp_eq S hSem hGrp hJM j t'
  have c₂ := heatOp_eq S hSem hGrp hJM j (2 * t')
  have e₂ : ((2 * t' : ℝ≥0) : ℝ) = 2 * (t' : ℝ) := by simp
  rw [e₂] at c₂
  have u₁ := phaseOp_eq S hSem hGrp hJM j (t' : ℝ)
  have u₂ := phaseOp_eq S hSem hGrp hJM j (-(t' : ℝ))
  have expand : ∀ (ψ : PhysicalSpace σ h) (A B C D : PhysicalSpace σ h →L[ℂ] PhysicalSpace σ h),
      ⟪ψ, (1 - (4 : ℂ) • A + B + C + D) ψ⟫_ℂ =
        ⟪ψ, ψ⟫_ℂ - 4 * ⟪ψ, A ψ⟫_ℂ + ⟪ψ, B ψ⟫_ℂ + ⟪ψ, C ψ⟫_ℂ + ⟪ψ, D ψ⟫_ℂ := by
    intro ψ A B C D
    show ⟪ψ, ψ - (4 : ℂ) • A ψ + B ψ + C ψ + D ψ⟫_ℂ = _
    simp only [inner_add_right, inner_sub_right, inner_smul_right]
  have mm : ∀ (s : ℝ≥0) (a : Fin 3 → ℝ),
      ⟪posClass σ h F, timeShift σ h s (spaceShift σ h a (posClass σ h F))⟫_ℂ =
        reflectedCorrelation σ F ((s : ℝ) • timeBasisVec + embedSpatial a) :=
    fun s a => matrixElementFormula_holds S F F s a
  have m₂ : ∀ s : ℝ≥0, ⟪posClass σ h F, timeShift σ h s (posClass σ h F)⟫_ℂ =
      reflectedCorrelation σ F ((s : ℝ) • timeBasisVec) := by
    intro s
    have := mm s 0
    rw [spaceShift_zero S, embedSpatial_zero, add_zero] at this
    exact this
  have m₁ : ⟪posClass σ h F, posClass σ h F⟫_ℂ = reflectedCorrelation σ F 0 := by
    have := m₂ 0
    rw [(isOpSemigroup_timeShift S).1] at this
    simpa using this
  unfold FivePointCone.fivePointOp
  rw [c₁, c₂, u₁, u₂, expand, m₁, m₂]
  have m₃ := m₂ (2 * t')
  rw [e₂] at m₃
  have v₄ : (t' : ℝ) • timeBasisVec + embedSpatial ((t' : ℝ) • spatialBasisVec j) =
      (t' : ℝ) • timeBasisVec + (t' : ℝ) • embedSpatial (spatialBasisVec j) := by
    rw [embedSpatial_smul]
  have v₅ : (t' : ℝ) • timeBasisVec + embedSpatial ((-(t' : ℝ)) • spatialBasisVec j) =
      (t' : ℝ) • timeBasisVec - (t' : ℝ) • embedSpatial (spatialBasisVec j) := by
    rw [embedSpatial_smul, neg_smul, sub_eq_add_neg]
  have m₄ : ⟪posClass σ h F, (timeShift σ h t' *
      spaceShift σ h ((t' : ℝ) • spatialBasisVec j)) (posClass σ h F)⟫_ℂ =
      reflectedCorrelation σ F ((t' : ℝ) • timeBasisVec + (t' : ℝ) • embedSpatial (spatialBasisVec j)) :=
    (mm t' _).trans (by rw [v₄])
  have m₅ : ⟪posClass σ h F, (timeShift σ h t' *
      spaceShift σ h ((-(t' : ℝ)) • spatialBasisVec j)) (posClass σ h F)⟫_ℂ =
      reflectedCorrelation σ F ((t' : ℝ) • timeBasisVec - (t' : ℝ) • embedSpatial (spatialBasisVec j)) :=
    (mm t' _).trans (by rw [v₅])
  unfold fivePointCombination
  rw [m₃, m₄, m₅]
end Cone
theorem spectralConeProperties_hold (S : ReconstructionInputs σ D₀ h)
    (hSem : ContractionSemigroups.ContractionSemigroupTheorem)
    (hGrp : UnitaryGroups.StoneTheoremHolds)
    (hJM : JointSpectralProperties σ h) (hCone : FivePointCone.FivePointConeTheorem)
    (hCalc : BorelCalculus.BorelCalculusTheorem) : SpectralConeProperties σ h := by
  intro j D hD h0 hfive
  obtain ⟨-, -, -, -, hIH, hIP⟩ := hJM j
  obtain ⟨-, -, hc, hd⟩ := hCone _ 2 nonnegHalfPlane (jointSpectralMeasure σ h j) energyCoord
    momentumCoord measurable_energyCoord measurable_momentumCoord (fun y => y.2)
  obtain ⟨x, hxD, hx0⟩ := mem_closure_iff_seq_limit.1 h0
  have hbelow := hc x (fun k => hD (hxD k)) hx0 fun k =>
    ⟨Set.range (posClass σ h), dense_range_posClass S, by
      rintro _ ⟨F, rfl⟩
      rw [inner_fivePointOp_posClass S hSem hGrp hJM j F (hD (hxD k))]
      exact hfive F _ (hxD k)⟩
  obtain ⟨-, hdom, -, hineq, hfix⟩ := hd hbelow
  have hEn : FivePointCone.energyOp (jointSpectralMeasure σ h j) energyCoord =
      hamiltonian σ h := spectralIntegralOp_eq hIH
  have hMo : FivePointCone.momentumOp (jointSpectralMeasure σ h j) momentumCoord =
      momentum σ h j := spectralIntegralOp_eq hIP
  rw [hEn, hMo] at hdom hineq
  rw [hEn] at hfix
  refine ⟨?_, fun ψ hψ => hdom hψ, hineq, fun ψ hψ s => ?_⟩
  · obtain ⟨-, -, -, -, -, -, hsf⟩ := (hCalc _ 2).1 nonnegHalfPlane (jointSpectralMeasure σ h j)
    have hZ : IsClosed {y : Fin 2 → ℝ | |y 1| ≤ y 0} := isClosed_le (by fun_prop) (by fun_prop)
    refine hsf.essSupport_subset _ hZ ?_
    refine (congrArg (jointSpectralMeasure σ h j).toFun (Subtype.ext ?_)).trans hbelow
    ext y
    show ¬ (|y.1 1| ≤ y.1 0) ↔ y.1 0 < |y.1 1|
    exact not_le
  · rw [expI_momentum S hGrp, ← phaseOp_eq S hSem hGrp hJM j s]
    exact hfix ψ hψ s
theorem reconstructionTheorem_proof (h₁ : HilbertSpaceFacts.Facts)
    (h₂ : FormProperties.Assertion)
    (h₃ : SeparatedTuples.BasicFacts.MainFacts)
    (h₄ : ContractionSemigroups.ContractionSemigroupTheorem)
    (h₅ : UnitaryGroups.StoneTheoremHolds)
    (h₆ : SemigroupRepresentation.JointSpectralTheoremForPair)
    (h₇ : FivePointCone.FivePointConeTheorem)
    (h₈ : BorelCalculus.BorelCalculusTheorem) : ReconstructionTheorem := by
  obtain ⟨-, -, -, -, -, hC, -, hO, -, -, -, -, -, -, -, -, -, -, -, hI, hS⟩ := h₁
  obtain ⟨-, -, -, -, hAct, -⟩ := h₃
  intro σ D₀ hc
  have hpsd := ((h₂ σ 0 0).1 hc.reflectionPositive).1
  have S : ReconstructionInputs σ D₀ hpsd := ⟨hC, hO, hI, hS, hAct, h₂, hc⟩
  have hJM := jointSpectralProperties_hold S h₄ h₅ h₆
  exact ⟨hpsd, vacuumProperties_hold S, (semigroupProperties_hold S h₄).1,
    spatialProperties_hold S h₅ h₆, matrixElementFormula_holds S, hJM,
    spectralConeProperties_hold S h₄ h₅ hJM h₇ h₈⟩
end YangMills.Construction.ReflectionPositivity.Reconstruction
