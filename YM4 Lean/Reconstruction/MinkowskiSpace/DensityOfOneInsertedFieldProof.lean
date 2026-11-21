import Reconstruction.MinkowskiSpace.ClassesOfOneInsertedFieldProof
import YangMills.Construction.ReflectionPositivity.ContractionOfTheLimitOfALatticeApproximationProof
import YangMills.Construction.HilbertSpaces.CompletionsAdjointsAndWeakIntegralsAreWellDefined
import Reconstruction.MinkowskiSpace.DensityNearTheMiddleOfASlabProof
import Reconstruction.MinkowskiSpace.DensityOfOneInsertedField
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace ContDiff Manifold
open MeasureTheory Filter Topology
noncomputable section
namespace YangMills.Construction.InsertedFieldForm.FieldDensity
open YangMills.Construction.FieldFormConditions YangMills.Construction.ReflectionPositivity.TupleForm YangMills.Construction.ReflectionPositivity.FormProperties YangMills.Construction.OneLoopNotation
theorem timeIdx_smul_timeUnitVec (s : ℝ) : (s • timeUnitVec) TimeAxis.timeIdx = s := by apply _root_.YangMills.Construction.ReflectionPositivity.LimitContraction.timeComponent_smul_basisVector <;> assumption
theorem isOpen_centralBox (η : ℝ) : IsOpen (centralBox η) := by apply _root_.YangMills.Construction.CentralDensity.isOpen_centralBox <;> assumption
theorem zero_mem_centralBox {η : ℝ} (hη : 0 < η) : (0 : Fin 4 → ℝ) ∈ centralBox η := by
  refine ⟨by simpa using by positivity, ?_⟩
  simp [TorusMetric.euclidNormVec]
def boxAround (y : Fin 4 → ℝ) (η : ℝ) : Set (Fin 4 → ℝ) := {y' | y' - y ∈ centralBox η}
theorem isOpen_boxAround (y : Fin 4 → ℝ) (η : ℝ) : IsOpen (boxAround y η) :=
  (isOpen_centralBox η).preimage (continuous_id.sub continuous_const)
structure IsAdmissibleHeight (c : ℝ) (y : Fin 4 → ℝ) (η : ℝ) : Prop where
  pos : 0 < η
  le_one : η ≤ 1
  three_mul_le : 3 * η ≤ y TimeAxis.timeIdx
  three_mul_le_sub : 3 * η ≤ c - y TimeAxis.timeIdx
theorem IsAdmissibleHeight.mem_timeSlab {c : ℝ} {y y' : Fin 4 → ℝ} {η : ℝ}
    (hη : IsAdmissibleHeight c y η) (hy' : y' ∈ boxAround y η) : y' ∈ timeSlab c := by
  have h := abs_lt.1 hy'.1
  have h1 : (y' - y) TimeAxis.timeIdx = y' TimeAxis.timeIdx - y TimeAxis.timeIdx := rfl
  rw [h1] at h
  have := hη.pos
  have := hη.three_mul_le
  have := hη.three_mul_le_sub
  exact ⟨by linarith [h.1], by linarith [h.2]⟩
def admissibleHeight (c : ℝ) (y : Fin 4 → ℝ) : ℝ :=
  min 1 (min (y TimeAxis.timeIdx / 3) ((c - y TimeAxis.timeIdx) / 3))
theorem isAdmissibleHeight_admissibleHeight {c : ℝ} {y : Fin 4 → ℝ} (hy : y ∈ timeSlab c) :
    IsAdmissibleHeight c y (admissibleHeight c y) := by
  obtain ⟨h0, h1⟩ := hy
  have ha : admissibleHeight c y ≤ y TimeAxis.timeIdx / 3 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hb : admissibleHeight c y ≤ (c - y TimeAxis.timeIdx) / 3 :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨?_, min_le_left _ _, by linarith, by linarith⟩
  refine lt_min one_pos (lt_min ?_ ?_) <;> linarith
variable (σ : TestSpaces.SepTuple → ℝ)
  (E : ProjectionMeasures.FourBorelSet → BddOp (StateSpace σ))
def localFieldDensity (c : ℝ) (y : Fin 4 → ℝ) (η : ℝ) (y' : Fin 4 → ℝ) :
    BddOp (StateSpace σ) :=
  FieldForms.spectralTranslation E (realWickPoint (y - (3 * η) • timeUnitVec)) *
    smoothedFieldOp σ E η (y' - y) *
      FieldForms.spectralTranslation E (realWickPoint ((c - 3 * η) • timeUnitVec - y))
def slabFieldDensity (c : ℝ) (y : Fin 4 → ℝ) : BddOp (StateSpace σ) :=
  localFieldDensity σ E c y (admissibleHeight c y) y
variable {σ E}
theorem translateFun_mem (a : Fin 4 → ℝ) {f : (Fin 4 → ℝ) → ℂ}
    (hf : f ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))) :
    translateFun a f ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) := by apply _root_.YangMills.Construction.InsertedFieldClasses.translateFun_mem_complexC1c <;> assumption
theorem sub_mem_tsupport_of_mem_tsupport_translateFun {a x : Fin 4 → ℝ} {f : (Fin 4 → ℝ) → ℂ}
    (hx : x ∈ tsupport (translateFun a f)) : x - a ∈ tsupport f := by
  have : translateFun a f = f ∘ (Homeomorph.subRight a) := rfl
  rw [this, tsupport_comp_eq_preimage] at hx
  exact hx
theorem integrable_mul_of_continuousOn_tsupport {h a : (Fin 4 → ℝ) → ℂ} (hc : Continuous h)
    (hK : HasCompactSupport h) (ha : ContinuousOn a (tsupport h)) :
    Integrable fun y => h y * a y := by
  have h1 : IntegrableOn (fun y => h y * a y) (tsupport h) :=
    (hc.continuousOn.mul ha).integrableOn_compact hK
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 h1
  intro y hy
  exact subset_tsupport h (fun h0 => hy (by simp [h0]))
theorem inner_insertedState_eq_integral_local (hClasses : InsertedStateProperties)
    (hMiddle : CentralDensityFormula) {p C : ℝ} (hcond : Hypotheses σ E p C)
    {c : ℝ} {y : Fin 4 → ℝ} {η : ℝ} (hη : IsAdmissibleHeight c y η) {h : (Fin 4 → ℝ) → ℂ}
    (hh : h ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)))
    (hsupp : tsupport h ⊆ boxAround y η) (F : PositiveSpan) (χ : StateSpace σ) :
    ⟪χ, insertedState σ h (c • timeUnitVec) F⟫_ℂ =
      ∫ y', h y' * ⟪χ, localFieldDensity σ E c y η y' (stateOf σ F)⟫_ℂ := by
  obtain ⟨-, -, hpart3, hpart4⟩ := hClasses σ E p C hcond
  set b : Fin 4 → ℝ := y - (3 * η) • timeUnitVec with hb
  set b' : Fin 4 → ℝ := (c - 3 * η) • timeUnitVec - y with hb'
  have hbt : b TimeAxis.timeIdx = y TimeAxis.timeIdx - 3 * η := by
    simp only [hb, Pi.sub_apply, timeIdx_smul_timeUnitVec]
  have hbt' : b' TimeAxis.timeIdx = c - 3 * η - y TimeAxis.timeIdx := by
    simp only [hb', Pi.sub_apply, timeIdx_smul_timeUnitVec]
  have hb0 : 0 ≤ b TimeAxis.timeIdx := by rw [hbt]; linarith [hη.three_mul_le]
  have hb0' : 0 ≤ b' TimeAxis.timeIdx := by rw [hbt']; linarith [hη.three_mul_le_sub]
  have hpos := hη.pos
  set f : (Fin 4 → ℝ) → ℂ := translateFun (-b) h with hf
  have hfh : translateFun b f = h := by
    funext x
    simp [hf, translateFun]
  have hfm := translateFun_mem (-b) hh
  have hfs : ∀ x ∈ tsupport f, x - (3 * η) • timeUnitVec ∈ centralBox η := by
    intro x hx
    have h1 := hsupp (sub_mem_tsupport_of_mem_tsupport_translateFun hx)
    have h2 : x - -b - y = x - (3 * η) • timeUnitVec := by
      rw [hb]
      abel
    have h3 : x - -b - y ∈ centralBox η := h1
    rwa [h2] at h3
  have hbelowf : SupportedBelow ((6 * η) • timeUnitVec) f := by
    refine ⟨hfm, fun x hx => ?_⟩
    have h1 := abs_lt.1 (hfs x hx).1
    have h2 : (x - (3 * η) • timeUnitVec) TimeAxis.timeIdx =
        x TimeAxis.timeIdx - 3 * η := by
      simp only [Pi.sub_apply, timeIdx_smul_timeUnitVec]
    rw [h2] at h1
    rw [timeIdx_smul_timeUnitVec]
    constructor <;> linarith [h1.1, h1.2]
  have hbelowh : SupportedBelow (b + (6 * η) • timeUnitVec) h := by
    refine ⟨hh, fun x hx => ?_⟩
    have h1 := abs_lt.1 (hsupp hx).1
    have h2 : (x - y) TimeAxis.timeIdx = x TimeAxis.timeIdx - y TimeAxis.timeIdx := rfl
    rw [h2] at h1
    have h3 : (b + (6 * η) • timeUnitVec) TimeAxis.timeIdx =
        y TimeAxis.timeIdx + 3 * η := by
      simp only [Pi.add_apply, timeIdx_smul_timeUnitVec, hbt]
      ring
    rw [h3]
    constructor <;> linarith [h1.1, h1.2, hη.three_mul_le]
  have hsum : (b + (6 * η) • timeUnitVec) + b' = c • timeUnitVec := by
    rw [hb, hb']
    module
  have e1 : insertedState σ h (c • timeUnitVec) F =
      FieldForms.spectralTranslation E (realWickPoint b)
        (insertedState σ f ((6 * η) • timeUnitVec) (shiftedSpan b' F)) := by
    rw [← hsum, hpart4 _ _ h F hb0' hbelowh]
    have := hpart3 b _ f (shiftedSpan b' F) hb0 hbelowf
    rw [hfh] at this
    exact this.symm
  have e2 := hMiddle σ E p C hcond η f (shiftedSpan b' F)
    ((FieldForms.spectralTranslation E (realWickPoint b)).adjoint χ) hη.pos hη.le_one hfm hfs
  have e3 : stateOf σ (shiftedSpan b' F) =
      FieldForms.spectralTranslation E (realWickPoint b') (stateOf σ F) :=
    (hcond.translationMeasure.translate_stateOf F b' hb0').symm
  rw [e1, ← ContinuousLinearMap.adjoint_inner_left, e2, e3]
  rw [← integral_add_left_eq_self
    (fun y' => h y' * ⟪χ, localFieldDensity σ E c y η y' (stateOf σ F)⟫_ℂ) y]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  have hfa : f ((3 * η) • timeUnitVec + a) = h (y + a) := by
    simp only [hf, translateFun]
    congr 1
    rw [hb]
    abel
  simp only [hfa, ContinuousLinearMap.adjoint_inner_left, localFieldDensity, add_sub_cancel_left]
  rfl
theorem continuousOn_inner_localFieldDensity (hSmoothed : SmoothedKernelField.Regularity) {p C : ℝ}
    (hcond : Hypotheses σ E p C) {c : ℝ} {y : Fin 4 → ℝ} {η : ℝ}
    (hη : IsAdmissibleHeight c y η) (χ χ' : StateSpace σ) :
    ContinuousOn (fun y' => ⟪χ, localFieldDensity σ E c y η y' χ'⟫_ℂ) (boxAround y η) := by
  have h1 := (hSmoothed σ E p C hcond η hη.pos hη.le_one).2.2
    ((FieldForms.spectralTranslation E (realWickPoint (y - (3 * η) • timeUnitVec))).adjoint χ)
    (FieldForms.spectralTranslation E (realWickPoint ((c - 3 * η) • timeUnitVec - y)) χ')
  have h2 : ContinuousOn (fun y' : Fin 4 → ℝ => y' - y) (boxAround y η) :=
    (continuous_id.sub continuous_const).continuousOn
  refine (h1.comp h2 fun y' hy' => ?_).congr fun y' _ => ?_
  · have h3 : |(y' - y) TimeAxis.timeIdx| < η / 4 := hy'.1
    show |(y' - y) TimeAxis.timeIdx| ≤ η / 2
    linarith [hη.pos]
  · simp only [Function.comp, ContinuousLinearMap.adjoint_inner_left, localFieldDensity]
    rfl
theorem localFieldDensity_eq (hW : HilbertWellDefined.WellDefinedStatement)
    (hClasses : InsertedStateProperties)
    (hMiddle : CentralDensityFormula)
    (hSmoothed : SmoothedKernelField.Regularity) {p C : ℝ}
    (hcond : Hypotheses σ E p C) {c : ℝ} {y₁ y₂ : Fin 4 → ℝ} {η₁ η₂ : ℝ}
    (h₁ : IsAdmissibleHeight c y₁ η₁) (h₂ : IsAdmissibleHeight c y₂ η₂) {y' : Fin 4 → ℝ}
    (hy₁ : y' ∈ boxAround y₁ η₁) (hy₂ : y' ∈ boxAround y₂ η₂) :
    localFieldDensity σ E c y₁ η₁ y' = localFieldDensity σ E c y₂ η₂ y' := by
  have hU : IsOpen (boxAround y₁ η₁ ∩ boxAround y₂ η₂) :=
    (isOpen_boxAround _ _).inter (isOpen_boxAround _ _)
  have key : ∀ (F : PositiveSpan) (χ : StateSpace σ),
      ⟪χ, localFieldDensity σ E c y₁ η₁ y' (stateOf σ F)⟫_ℂ =
        ⟪χ, localFieldDensity σ E c y₂ η₂ y' (stateOf σ F)⟫_ℂ := by
    intro F χ
    set a₁ : (Fin 4 → ℝ) → ℂ :=
      fun x => ⟪χ, localFieldDensity σ E c y₁ η₁ x (stateOf σ F)⟫_ℂ with ha₁
    set a₂ : (Fin 4 → ℝ) → ℂ :=
      fun x => ⟪χ, localFieldDensity σ E c y₂ η₂ x (stateOf σ F)⟫_ℂ with ha₂
    have hc₁ : ContinuousOn a₁ (boxAround y₁ η₁ ∩ boxAround y₂ η₂) :=
      (continuousOn_inner_localFieldDensity hSmoothed hcond h₁ _ _).mono Set.inter_subset_left
    have hc₂ : ContinuousOn a₂ (boxAround y₁ η₁ ∩ boxAround y₂ η₂) :=
      (continuousOn_inner_localFieldDensity hSmoothed hcond h₂ _ _).mono Set.inter_subset_right
    have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
      (f := fun x => a₁ x - a₂ x) ((hc₁.sub hc₂).locallyIntegrableOn hU.measurableSet)
      (fun g hg hgK hgU => by
        set w : (Fin 4 → ℝ) → ℂ := fun x => (g x : ℂ) with hw
        have hwd : ContDiff ℝ 1 w :=
          Complex.ofRealCLM.contDiff.comp (hg.of_le (by exact_mod_cast le_top))
        have hwsub : tsupport w ⊆ tsupport g := by
          refine closure_mono fun x hx => ?_
          intro h0
          exact hx (by simp [hw, h0])
        have hwK : HasCompactSupport w := hgK.mono' (by
          exact (subset_tsupport w).trans hwsub)
        have hwm : w ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) :=
          ⟨hwd, hwK, Set.subset_univ _⟩
        have hwU := hwsub.trans hgU
        have l₁ := inner_insertedState_eq_integral_local hClasses hMiddle hcond h₁ hwm
          (hwU.trans Set.inter_subset_left) F χ
        have l₂ := inner_insertedState_eq_integral_local hClasses hMiddle hcond h₂ hwm
          (hwU.trans Set.inter_subset_right) F χ
        have i₁ : Integrable fun x => w x * a₁ x :=
          integrable_mul_of_continuousOn_tsupport hwd.continuous hwK (hc₁.mono hwU)
        have i₂ : Integrable fun x => w x * a₂ x :=
          integrable_mul_of_continuousOn_tsupport hwd.continuous hwK (hc₂.mono hwU)
        have : ∀ x, g x • (a₁ x - a₂ x) = w x * a₁ x - w x * a₂ x := by
          intro x
          simp only [hw, Complex.real_smul]
          ring
        simp only [this]
        rw [integral_sub i₁ i₂, ← l₁, ← l₂, sub_self])
    have hres : (fun x => a₁ x - a₂ x) =ᵐ[volume.restrict (boxAround y₁ η₁ ∩ boxAround y₂ η₂)]
        fun _ => (0 : ℂ) := (ae_restrict_iff' hU.measurableSet).2 hae
    have heq := Measure.eqOn_open_of_ae_eq hres hU (hc₁.sub hc₂) continuousOn_const ⟨hy₁, hy₂⟩
    exact sub_eq_zero.1 heq
  have hdense : Dense (Set.range (stateOf σ)) := by
    obtain ⟨-, cl, hcl, hpair⟩ := hW.1 PositiveSpan (pairing σ) hcond.posSemidef
    have h1 := (ComplexHilbert.isDenseSet_iff _).1 hpair.denseRange
    have h2 : Set.range cl = Set.range (stateOf σ) := by
      ext v
      constructor
      · rintro ⟨F, rfl⟩
        exact ⟨F, (hcl F).symm⟩
      · rintro ⟨F, rfl⟩
        exact ⟨F, hcl F⟩
    rwa [h2] at h1
  exact DFunLike.coe_injective (DenseRange.equalizer (f := stateOf σ) hdense
    (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
    (funext fun F => ext_inner_left ℂ fun χ => key F χ))
theorem slabFieldDensity_eq_local (hW : HilbertWellDefined.WellDefinedStatement)
    (hClasses : InsertedStateProperties)
    (hMiddle : CentralDensityFormula)
    (hSmoothed : SmoothedKernelField.Regularity) {p C : ℝ}
    (hcond : Hypotheses σ E p C) {c : ℝ} {y y' : Fin 4 → ℝ} {η : ℝ}
    (hη : IsAdmissibleHeight c y η) (hy' : y' ∈ boxAround y η) :
    slabFieldDensity σ E c y' = localFieldDensity σ E c y η y' := by
  have hs := isAdmissibleHeight_admissibleHeight (hη.mem_timeSlab hy')
  have h0 : y' ∈ boxAround y' (admissibleHeight c y') := by
    show y' - y' ∈ centralBox _
    rw [sub_self]
    exact zero_mem_centralBox hs.pos
  exact localFieldDensity_eq hW hClasses hMiddle hSmoothed hcond hs hη h0 hy'
theorem continuousOn_inner_slabFieldDensity
    (hW : HilbertWellDefined.WellDefinedStatement)
    (hClasses : InsertedStateProperties)
    (hMiddle : CentralDensityFormula)
    (hSmoothed : SmoothedKernelField.Regularity) {p C : ℝ}
    (hcond : Hypotheses σ E p C) (c : ℝ) (χ χ' : StateSpace σ) :
    ContinuousOn (fun y => ⟪χ, slabFieldDensity σ E c y χ'⟫_ℂ) (timeSlab c) := by
  intro y hy
  have hs := isAdmissibleHeight_admissibleHeight hy
  have h0 : y ∈ boxAround y (admissibleHeight c y) := by
    show y - y ∈ centralBox _
    rw [sub_self]
    exact zero_mem_centralBox hs.pos
  have h1 := continuousOn_inner_localFieldDensity hSmoothed hcond hs χ χ'
  have h2 : ContinuousOn (fun y' => ⟪χ, slabFieldDensity σ E c y' χ'⟫_ℂ)
      (boxAround y (admissibleHeight c y)) := h1.congr fun y' hy' => by
    simp only [slabFieldDensity_eq_local hW hClasses hMiddle hSmoothed hcond hs hy']
  exact (h2.continuousAt ((isOpen_boxAround _ _).mem_nhds h0)).continuousWithinAt
theorem inner_insertedState_eq_setIntegral
    (hW : HilbertWellDefined.WellDefinedStatement)
    (hClasses : InsertedStateProperties)
    (hMiddle : CentralDensityFormula)
    (hSmoothed : SmoothedKernelField.Regularity) {p C : ℝ}
    (hcond : Hypotheses σ E p C) {c : ℝ} {h : (Fin 4 → ℝ) → ℂ} (F : PositiveSpan)
    (χ : StateSpace σ)
    (hh : h ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)))
    (hsub : tsupport h ⊆ timeSlab c) :
    ⟪χ, insertedState σ h (c • timeUnitVec) F⟫_ℂ =
      ∫ y in tsupport h, h y * ⟪χ, slabFieldDensity σ E c y (stateOf σ F)⟫_ℂ := by
  have hK : IsCompact (tsupport h) := hh.2.1
  set g : (Fin 4 → ℝ) → ℂ :=
    fun y => ⟪χ, slabFieldDensity σ E c y (stateOf σ F)⟫_ℂ with hg
  have hgc : ContinuousOn g (timeSlab c) :=
    continuousOn_inner_slabFieldDensity hW hClasses hMiddle hSmoothed hcond c χ _
  obtain ⟨-, hpart2, -, -⟩ := hClasses σ E p C hcond
  obtain ⟨t, htK, ht⟩ := hK.elim_nhds_subcover (fun y => boxAround y (admissibleHeight c y))
    (fun y hy => by
      have hs := isAdmissibleHeight_admissibleHeight (hsub hy)
      refine (isOpen_boxAround _ _).mem_nhds ?_
      show y - y ∈ centralBox _
      rw [sub_self]
      exact zero_mem_centralBox hs.pos)
  have hcov : tsupport h ⊆ ⋃ i : t, boxAround i.1 (admissibleHeight c i.1) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact Set.mem_iUnion.2 ⟨⟨y, hy⟩, hxy⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Fin 4 → ℝ)
    (isClosed_tsupport h) (fun i : t => boxAround i.1 (admissibleHeight c i.1))
    (fun i => isOpen_boxAround _ _) hcov
  set w : t → (Fin 4 → ℝ) → ℂ := fun i x => ((ρ i x : ℝ) : ℂ) * h x with hw
  have hρd : ∀ i, ContDiff ℝ 1 fun x => ((ρ i x : ℝ) : ℂ) := fun i =>
    Complex.ofRealCLM.contDiff.comp ((ρ i).contMDiff.contDiff.of_le (by exact_mod_cast le_top))
  have hwd : ∀ i, ContDiff ℝ 1 (w i) := fun i => (hρd i).mul hh.1
  have hwK : ∀ i, HasCompactSupport (w i) := fun i => hh.2.1.mul_left
  have hws : ∀ i, tsupport (w i) ⊆ tsupport h := fun i => tsupport_mul_subset_right
  have hwU : ∀ i, tsupport (w i) ⊆ boxAround i.1 (admissibleHeight c i.1) := by
    intro i
    refine Set.Subset.trans ?_ (hρ i)
    refine Set.Subset.trans tsupport_mul_subset_left (closure_mono fun x hx => ?_)
    intro h0
    exact hx (by simp [h0])
  have hwm : ∀ i, w i ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) := fun i =>
    ⟨hwd i, hwK i, Set.subset_univ _⟩
  have hbelow : ∀ i, SupportedBelow (c • timeUnitVec) (w i) := by
    intro i
    refine ⟨hwm i, fun x hx => ?_⟩
    have h1 := hsub (hws i hx)
    rw [timeIdx_smul_timeUnitVec]
    exact ⟨h1.1, h1.2.le⟩
  have hsum : (∑ i ∈ (Finset.univ : Finset t), (1 : ℂ) • w i) = h := by
    funext x
    by_cases hx : x ∈ tsupport h
    · have h1 := ρ.sum_eq_one hx
      rw [finsum_eq_sum_of_fintype] at h1
      have h2 : (∑ i : t, ((ρ i x : ℝ) : ℂ)) = 1 := by
        rw [← Complex.ofReal_sum, h1, Complex.ofReal_one]
      simp only [Finset.sum_apply, one_smul, hw]
      rw [← Finset.sum_mul, h2, one_mul]
    · have h0 : h x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hw, h0]
  have e1 := hpart2 Finset.univ (fun _ => (1 : ℂ)) w (c • timeUnitVec) F fun i _ => hbelow i
  rw [hsum] at e1
  have e2 : ∀ i : t, ⟪χ, insertedState σ (w i) (c • timeUnitVec) F⟫_ℂ = ∫ y, w i y * g y := by
    intro i
    have hs := isAdmissibleHeight_admissibleHeight (hsub (htK i.1 i.2))
    rw [inner_insertedState_eq_integral_local hClasses hMiddle hcond hs (hwm i) (hwU i) F χ]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ tsupport (w i)
    · simp only [hg, slabFieldDensity_eq_local hW hClasses hMiddle hSmoothed hcond hs (hwU i hy)]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  have hint : ∀ i ∈ (Finset.univ : Finset t), Integrable fun y => w i y * g y := fun i _ =>
    integrable_mul_of_continuousOn_tsupport (hwd i).continuous (hwK i)
      (hgc.mono ((hws i).trans hsub))
  rw [e1, inner_sum]
  simp only [one_smul, e2]
  rw [← integral_finsetSum _ hint,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      simp [image_eq_zero_of_notMem_tsupport hy]]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have h3 : h y = ∑ i, w i y := by
    conv_lhs => rw [← hsum]
    simp
  simp only [h3, Finset.sum_mul]
  rfl
theorem fieldDensityExists (hClasses : InsertedStateProperties)
    (hMiddle : CentralDensityFormula)
    (hSmoothed : SmoothedKernelField.Regularity)
    (hW : HilbertWellDefined.WellDefinedStatement) : FieldDensityExists := by
  intro σ E p C hcond
  refine ⟨slabFieldDensity σ E, ⟨?_, ?_, ?_⟩⟩
  · intro c χ χ' _
    exact continuousOn_inner_slabFieldDensity hW hClasses hMiddle hSmoothed hcond c χ χ'
  · intro c η y h0 h1 h2 h3
    have hη : IsAdmissibleHeight c y η := ⟨h0, h1, h2, h3⟩
    have hy : y ∈ boxAround y η := by
      show y - y ∈ centralBox _
      rw [sub_self]
      exact zero_mem_centralBox h0
    rw [slabFieldDensity_eq_local hW hClasses hMiddle hSmoothed hcond hη hy]
    simp only [localFieldDensity, sub_self]
  · intro c h F χ _ hh hsub
    exact inner_insertedState_eq_setIntegral hW hClasses hMiddle hSmoothed hcond F χ hh hsub
end YangMills.Construction.InsertedFieldForm.FieldDensity
end
